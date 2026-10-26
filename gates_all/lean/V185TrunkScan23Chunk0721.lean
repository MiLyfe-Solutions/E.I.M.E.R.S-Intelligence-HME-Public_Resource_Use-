import V185TrunkScan23Chunk0720

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4263452 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_4263452 : Nat := 118140960795 + 4263452 * 2 ^ 59
def prefixEnd_4263452 : Nat := 4983230072969 + 3 ^ 40 * 4263452 * 2
def baseEnd_4263452 : Nat := 729733374457586152714249

theorem tailTrace_4263452 : CollatzResearch.WordTrace tailWord_4263452 prefixEnd_4263452 729733374457586152714249 := by
  unfold tailWord_4263452
  simp only [CollatzResearch.WordTrace]
  refine ⟨77750434675124509238276305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103667246233499345651035073 77750434675124509238276305)
  ·
    refine ⟨58312826006343381928707229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77750434675124509238276305 58312826006343381928707229)
    ·
      refine ⟨21867309752378768223265211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58312826006343381928707229 21867309752378768223265211)
      ·
        refine ⟨32800964628568152334897817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21867309752378768223265211 32800964628568152334897817)
        ·
          refine ⟨24600723471426114251173363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32800964628568152334897817 24600723471426114251173363)
          ·
            refine ⟨36901085207139171376760045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24600723471426114251173363 36901085207139171376760045)
            ·
              refine ⟨13837906952677189266285017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36901085207139171376760045 13837906952677189266285017)
              ·
                refine ⟨10378430214507891949713763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13837906952677189266285017 10378430214507891949713763)
                ·
                  refine ⟨15567645321761837924570645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10378430214507891949713763 15567645321761837924570645)
                  ·
                    refine ⟨729733374457586152714249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15567645321761837924570645 729733374457586152714249)
                    ·
                      rfl

theorem cell23_4263452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_4263452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263452 prefixEnd_4263452 := by exact prefixLift 4263452
  have htrace : WordTrace (prefixWord ++ tailWord_4263452) baseStart_4263452 baseEnd_4263452 := by
    simpa [prefixWord, tailWord_4263452, baseEnd_4263452] using wordTrace_append hprefix tailTrace_4263452
  have hstable : (prefixWord ++ tailWord_4263452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263452).length < 2 ^ (prefixWord ++ tailWord_4263452).sum := by decide
  have hdescent : baseEnd_4263452 < baseStart_4263452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263456 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_4263456 : Nat := 118140960795 + 4263456 * 2 ^ 59
def prefixEnd_4263456 : Nat := 4983230072969 + 3 ^ 40 * 4263456 * 2
def baseEnd_4263456 : Nat := 729734059098458814164243

theorem tailTrace_4263456 : CollatzResearch.WordTrace tailWord_4263456 prefixEnd_4263456 729734059098458814164243 := by
  unfold tailWord_4263456
  simp only [CollatzResearch.WordTrace]
  refine ⟨77750507621117263579849111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103667343494823018106465481 77750507621117263579849111)
  ·
    refine ⟨116625761431675895369773667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77750507621117263579849111 116625761431675895369773667)
    ·
      refine ⟨174938642147513843054660501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116625761431675895369773667 174938642147513843054660501)
      ·
        refine ⟨8200248850664711393187211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174938642147513843054660501 8200248850664711393187211)
        ·
          refine ⟨12300373275997067089780817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200248850664711393187211 12300373275997067089780817)
          ·
            refine ⟨9225279956997800317335613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12300373275997067089780817 9225279956997800317335613)
            ·
              refine ⟨3459479983874175119000855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9225279956997800317335613 3459479983874175119000855)
              ·
                refine ⟨5189219975811262678501283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459479983874175119000855 5189219975811262678501283)
                ·
                  refine ⟨7783829963716894017751925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189219975811262678501283 7783829963716894017751925)
                  ·
                    refine ⟨729734059098458814164243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7783829963716894017751925 729734059098458814164243)
                    ·
                      rfl

theorem cell23_4263456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_4263456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263456 prefixEnd_4263456 := by exact prefixLift 4263456
  have htrace : WordTrace (prefixWord ++ tailWord_4263456) baseStart_4263456 baseEnd_4263456 := by
    simpa [prefixWord, tailWord_4263456, baseEnd_4263456] using wordTrace_append hprefix tailTrace_4263456
  have hstable : (prefixWord ++ tailWord_4263456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263456).length < 2 ^ (prefixWord ++ tailWord_4263456).sum := by decide
  have hdescent : baseEnd_4263456 < baseStart_4263456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263470 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4263470 : Nat := 118140960795 + 4263470 * 2 ^ 59
def prefixEnd_4263470 : Nat := 4983230072969 + 3 ^ 40 * 4263470 * 2
def baseEnd_4263470 : Nat := 2189209366024539387717665

theorem tailTrace_4263470 : CollatzResearch.WordTrace tailWord_4263470 prefixEnd_4263470 2189209366024539387717665 := by
  unfold tailWord_4263470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19437690733022975943838483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103667683909455871700471909 19437690733022975943838483)
  ·
    refine ⟨29156536099534463915757725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19437690733022975943838483 29156536099534463915757725)
    ·
      refine ⟨10933701037325423968409147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29156536099534463915757725 10933701037325423968409147)
      ·
        refine ⟨16400551555988135952613721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10933701037325423968409147 16400551555988135952613721)
        ·
          refine ⟨12300413666991101964460291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16400551555988135952613721 12300413666991101964460291)
          ·
            refine ⟨18450620500486652946690437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300413666991101964460291 18450620500486652946690437)
            ·
              refine ⟨3459491343841247427504457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18450620500486652946690437 3459491343841247427504457)
              ·
                refine ⟨2594618507880935570628343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459491343841247427504457 2594618507880935570628343)
                ·
                  refine ⟨3891927761821403355942515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594618507880935570628343 3891927761821403355942515)
                  ·
                    refine ⟨5837891642732105033913773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891927761821403355942515 5837891642732105033913773)
                    ·
                      refine ⟨2189209366024539387717665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837891642732105033913773 2189209366024539387717665)
                      ·
                        rfl

theorem cell23_4263470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4263470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263470 prefixEnd_4263470 := by exact prefixLift 4263470
  have htrace : WordTrace (prefixWord ++ tailWord_4263470) baseStart_4263470 baseEnd_4263470 := by
    simpa [prefixWord, tailWord_4263470, baseEnd_4263470] using wordTrace_append hprefix tailTrace_4263470
  have hstable : (prefixWord ++ tailWord_4263470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263470).length < 2 ^ (prefixWord ++ tailWord_4263470).sum := by decide
  have hdescent : baseEnd_4263470 < baseStart_4263470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263489 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4263489 : Nat := 118140960795 + 4263489 * 2 ^ 59
def prefixEnd_4263489 : Nat := 4983230072969 + 3 ^ 40 * 4263489 * 2
def baseEnd_4263489 : Nat := 2189219122156974813380077

theorem tailTrace_4263489 : CollatzResearch.WordTrace tailWord_4263489 prefixEnd_4263489 2189219122156974813380077 := by
  unfold tailWord_4263489
  simp only [CollatzResearch.WordTrace]
  refine ⟨155502218851114973795649521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103668145900743315863766347 155502218851114973795649521)
  ·
    refine ⟨116626664138336230346737141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155502218851114973795649521 116626664138336230346737141)
    ·
      refine ⟨10933749762969021595006607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116626664138336230346737141 10933749762969021595006607)
      ·
        refine ⟨16400624644453532392509911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10933749762969021595006607 16400624644453532392509911)
        ·
          refine ⟨24600936966680298588764867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16400624644453532392509911 24600936966680298588764867)
          ·
            refine ⟨36901405450020447883147301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24600936966680298588764867 36901405450020447883147301)
            ·
              refine ⟨6919013521878833978090119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36901405450020447883147301 6919013521878833978090119)
              ·
                refine ⟨10378520282818250967135179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6919013521878833978090119 10378520282818250967135179)
                ·
                  refine ⟨15567780424227376450702769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10378520282818250967135179 15567780424227376450702769)
                  ·
                    refine ⟨11675835318170532338027077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15567780424227376450702769 11675835318170532338027077)
                    ·
                      refine ⟨2189219122156974813380077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11675835318170532338027077 2189219122156974813380077)
                      ·
                        rfl

theorem cell23_4263489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4263489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263489 prefixEnd_4263489 := by exact prefixLift 4263489
  have htrace : WordTrace (prefixWord ++ tailWord_4263489) baseStart_4263489 baseEnd_4263489 := by
    simpa [prefixWord, tailWord_4263489, baseEnd_4263489] using wordTrace_append hprefix tailTrace_4263489
  have hstable : (prefixWord ++ tailWord_4263489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263489).length < 2 ^ (prefixWord ++ tailWord_4263489).sum := by decide
  have hdescent : baseEnd_4263489 < baseStart_4263489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263509 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4263509 : Nat := 118140960795 + 4263509 * 2 ^ 59
def prefixEnd_4263509 : Nat := 4983230072969 + 3 ^ 40 * 4263509 * 2
def baseEnd_4263509 : Nat := 2189229391770064735129985

theorem tailTrace_4263509 : CollatzResearch.WordTrace tailWord_4263509 prefixEnd_4263509 2189229391770064735129985 := by
  unfold tailWord_4263509
  simp only [CollatzResearch.WordTrace]
  refine ⟨155502948311042517211377581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103668632207361678140918387 155502948311042517211377581)
  ·
    refine ⟨58313605616640943954266593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155502948311042517211377581 58313605616640943954266593)
    ·
      refine ⟨43735204212480707965699945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58313605616640943954266593 43735204212480707965699945)
      ·
        refine ⟨32801403159360530974274959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43735204212480707965699945 32801403159360530974274959)
        ·
          refine ⟨49202104739040796461412439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32801403159360530974274959 49202104739040796461412439)
          ·
            refine ⟨73803157108561194692118659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49202104739040796461412439 73803157108561194692118659)
            ·
              refine ⟨110704735662841792038177989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73803157108561194692118659 110704735662841792038177989)
              ·
                refine ⟨20757137936782836007158373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110704735662841792038177989 20757137936782836007158373)
                ·
                  refine ⟨3891963363146781751342195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20757137936782836007158373 3891963363146781751342195)
                  ·
                    refine ⟨5837945044720172627013293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891963363146781751342195 5837945044720172627013293)
                    ·
                      refine ⟨2189229391770064735129985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837945044720172627013293 2189229391770064735129985)
                      ·
                        rfl

theorem cell23_4263509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4263509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263509 prefixEnd_4263509 := by exact prefixLift 4263509
  have htrace : WordTrace (prefixWord ++ tailWord_4263509) baseStart_4263509 baseEnd_4263509 := by
    simpa [prefixWord, tailWord_4263509, baseEnd_4263509] using wordTrace_append hprefix tailTrace_4263509
  have hstable : (prefixWord ++ tailWord_4263509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263509).length < 2 ^ (prefixWord ++ tailWord_4263509).sum := by decide
  have hdescent : baseEnd_4263509 < baseStart_4263509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263510 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4263510 : Nat := 118140960795 + 4263510 * 2 ^ 59
def prefixEnd_4263510 : Nat := 4983230072969 + 3 ^ 40 * 4263510 * 2
def baseEnd_4263510 : Nat := 2189229905250719231217481

theorem tailTrace_4263510 : CollatzResearch.WordTrace tailWord_4263510 prefixEnd_4263510 2189229905250719231217481 := by
  unfold tailWord_4263510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718936549002430898885249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103668656522692596254775989 9718936549002430898885249)
  ·
    refine ⟨7289202411751823174163937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9718936549002430898885249 7289202411751823174163937)
    ·
      refine ⟨5466901808813867380622953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7289202411751823174163937 5466901808813867380622953)
      ·
        refine ⟨4100176356610400535467215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5466901808813867380622953 4100176356610400535467215)
        ·
          refine ⟨6150264534915600803200823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100176356610400535467215 6150264534915600803200823)
          ·
            refine ⟨9225396802373401204801235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6150264534915600803200823 9225396802373401204801235)
            ·
              refine ⟨13838095203560101807201853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9225396802373401204801235 13838095203560101807201853)
              ·
                refine ⟨5189285701335038177700695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13838095203560101807201853 5189285701335038177700695)
                ·
                  refine ⟨7783928552002557266551043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189285701335038177700695 7783928552002557266551043)
                  ·
                    refine ⟨11675892828003835899826565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7783928552002557266551043 11675892828003835899826565)
                    ·
                      refine ⟨2189229905250719231217481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11675892828003835899826565 2189229905250719231217481)
                      ·
                        rfl

theorem cell23_4263510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4263510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263510 prefixEnd_4263510 := by exact prefixLift 4263510
  have htrace : WordTrace (prefixWord ++ tailWord_4263510) baseStart_4263510 baseEnd_4263510 := by
    simpa [prefixWord, tailWord_4263510, baseEnd_4263510] using wordTrace_append hprefix tailTrace_4263510
  have hstable : (prefixWord ++ tailWord_4263510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263510).length < 2 ^ (prefixWord ++ tailWord_4263510).sum := by decide
  have hdescent : baseEnd_4263510 < baseStart_4263510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263552 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_4263552 : Nat := 118140960795 + 4263552 * 2 ^ 59
def prefixEnd_4263552 : Nat := 4983230072969 + 3 ^ 40 * 4263552 * 2
def baseEnd_4263552 : Nat := 2189251471438208066892287

theorem tailTrace_4263552 : CollatzResearch.WordTrace tailWord_4263552 prefixEnd_4263552 2189251471438208066892287 := by
  unfold tailWord_4263552
  simp only [CollatzResearch.WordTrace]
  refine ⟨77752258324943367777596455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103669677766591157036795273 77752258324943367777596455)
  ·
    refine ⟨116628387487415051666394683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77752258324943367777596455 116628387487415051666394683)
    ·
      refine ⟨174942581231122577499592025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116628387487415051666394683 174942581231122577499592025)
      ·
        refine ⟨131206935923341933124694019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174942581231122577499592025 131206935923341933124694019)
        ·
          refine ⟨196810403885012899687041029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131206935923341933124694019 196810403885012899687041029)
          ·
            refine ⟨36901950728439918691320193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196810403885012899687041029 36901950728439918691320193)
            ·
              refine ⟨27676463046329939018490145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36901950728439918691320193 27676463046329939018490145)
              ·
                refine ⟨20757347284747454263867609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27676463046329939018490145 20757347284747454263867609)
                ·
                  refine ⟨15568010463560590697900707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20757347284747454263867609 15568010463560590697900707)
                  ·
                    refine ⟨23352015695340886046851061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15568010463560590697900707 23352015695340886046851061)
                    ·
                      refine ⟨2189251471438208066892287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23352015695340886046851061 2189251471438208066892287)
                      ·
                        rfl

theorem cell23_4263552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_4263552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263552 prefixEnd_4263552 := by exact prefixLift 4263552
  have htrace : WordTrace (prefixWord ++ tailWord_4263552) baseStart_4263552 baseEnd_4263552 := by
    simpa [prefixWord, tailWord_4263552, baseEnd_4263552] using wordTrace_append hprefix tailTrace_4263552
  have hstable : (prefixWord ++ tailWord_4263552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263552).length < 2 ^ (prefixWord ++ tailWord_4263552).sum := by decide
  have hdescent : baseEnd_4263552 < baseStart_4263552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263553 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_4263553 : Nat := 118140960795 + 4263553 * 2 ^ 59
def prefixEnd_4263553 : Nat := 4983230072969 + 3 ^ 40 * 4263553 * 2
def baseEnd_4263553 : Nat := 2189251984918862562979783

theorem tailTrace_4263553 : CollatzResearch.WordTrace tailWord_4263553 prefixEnd_4263553 2189251984918862562979783 := by
  unfold tailWord_4263553
  simp only [CollatzResearch.WordTrace]
  refine ⟨155504553122883112725979313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103669702081922075150652875 155504553122883112725979313)
  ·
    refine ⟨116628414842162334544484485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155504553122883112725979313 116628414842162334544484485)
    ·
      refine ⟨21867827782905437727090841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116628414842162334544484485 21867827782905437727090841)
      ·
        refine ⟨16400870837179078295318131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21867827782905437727090841 16400870837179078295318131)
        ·
          refine ⟨24601306255768617442977197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16400870837179078295318131 24601306255768617442977197)
          ·
            refine ⟨9225489845913231541116449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24601306255768617442977197 9225489845913231541116449)
            ·
              refine ⟨6919117384434923655837337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9225489845913231541116449 6919117384434923655837337)
              ·
                refine ⟨5189338038326192741878003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919117384434923655837337 5189338038326192741878003)
                ·
                  refine ⟨7784007057489289112817005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189338038326192741878003 7784007057489289112817005)
                  ·
                    refine ⟨2919002646558483417306377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7784007057489289112817005 2919002646558483417306377)
                    ·
                      refine ⟨2189251984918862562979783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919002646558483417306377 2189251984918862562979783)
                      ·
                        rfl

theorem cell23_4263553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_4263553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263553 prefixEnd_4263553 := by exact prefixLift 4263553
  have htrace : WordTrace (prefixWord ++ tailWord_4263553) baseStart_4263553 baseEnd_4263553 := by
    simpa [prefixWord, tailWord_4263553, baseEnd_4263553] using wordTrace_append hprefix tailTrace_4263553
  have hstable : (prefixWord ++ tailWord_4263553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263553).length < 2 ^ (prefixWord ++ tailWord_4263553).sum := by decide
  have hdescent : baseEnd_4263553 < baseStart_4263553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263589 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 5]
def baseStart_4263589 : Nat := 118140960795 + 4263589 * 2 ^ 59
def prefixEnd_4263589 : Nat := 4983230072969 + 3 ^ 40 * 4263589 * 2
def baseEnd_4263589 : Nat := 243252274469158269125513

theorem tailTrace_4263589 : CollatzResearch.WordTrace tailWord_4263589 prefixEnd_4263589 243252274469158269125513 := by
  unfold tailWord_4263589
  simp only [CollatzResearch.WordTrace]
  refine ⟨155505866150752690874289821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103670577433835127249526547 155505866150752690874289821)
  ·
    refine ⟨58314699806532259077858683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155505866150752690874289821 58314699806532259077858683)
    ·
      refine ⟨87472049709798388616788025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58314699806532259077858683 87472049709798388616788025)
      ·
        refine ⟨65604037282348791462591019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87472049709798388616788025 65604037282348791462591019)
        ·
          refine ⟨98406055923523187193886529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65604037282348791462591019 98406055923523187193886529)
          ·
            refine ⟨73804541942642390395414897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98406055923523187193886529 73804541942642390395414897)
            ·
              refine ⟨55353406456981792796561173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73804541942642390395414897 55353406456981792796561173)
              ·
                refine ⟨2594690927671021537338805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55353406456981792796561173 2594690927671021537338805)
                ·
                  refine ⟨243252274469158269125513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594690927671021537338805 243252274469158269125513)
                  ·
                    rfl

theorem cell23_4263589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_4263589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263589 prefixEnd_4263589 := by exact prefixLift 4263589
  have htrace : WordTrace (prefixWord ++ tailWord_4263589) baseStart_4263589 baseEnd_4263589 := by
    simpa [prefixWord, tailWord_4263589, baseEnd_4263589] using wordTrace_append hprefix tailTrace_4263589
  have hstable : (prefixWord ++ tailWord_4263589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263589).length < 2 ^ (prefixWord ++ tailWord_4263589).sum := by decide
  have hdescent : baseEnd_4263589 < baseStart_4263589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263602 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_4263602 : Nat := 118140960795 + 4263602 * 2 ^ 59
def prefixEnd_4263602 : Nat := 4983230072969 + 3 ^ 40 * 4263602 * 2
def baseEnd_4263602 : Nat := 729759048490310957089019

theorem tailTrace_4263602 : CollatzResearch.WordTrace tailWord_4263602 prefixEnd_4263602 729759048490310957089019 := by
  unfold tailWord_4263602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38876585074926398523628265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103670893533137062729675373 38876585074926398523628265)
  ·
    refine ⟨29157438806194798892721199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38876585074926398523628265 29157438806194798892721199)
    ·
      refine ⟨43736158209292198339081799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29157438806194798892721199 43736158209292198339081799)
      ·
        refine ⟨65604237313938297508622699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43736158209292198339081799 65604237313938297508622699)
        ·
          refine ⟨98406355970907446262934049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65604237313938297508622699 98406355970907446262934049)
          ·
            refine ⟨73804766978180584697200537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98406355970907446262934049 73804766978180584697200537)
            ·
              refine ⟨55353575233635438522900403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73804766978180584697200537 55353575233635438522900403)
              ·
                refine ⟨83030362850453157784350605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55353575233635438522900403 83030362850453157784350605)
                ·
                  refine ⟨31136386068919934169131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83030362850453157784350605 31136386068919934169131477)
                  ·
                    refine ⟨729759048490310957089019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31136386068919934169131477 729759048490310957089019)
                    ·
                      rfl

theorem cell23_4263602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_4263602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263602 prefixEnd_4263602 := by exact prefixLift 4263602
  have htrace : WordTrace (prefixWord ++ tailWord_4263602) baseStart_4263602 baseEnd_4263602 := by
    simpa [prefixWord, tailWord_4263602, baseEnd_4263602] using wordTrace_append hprefix tailTrace_4263602
  have hstable : (prefixWord ++ tailWord_4263602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263602).length < 2 ^ (prefixWord ++ tailWord_4263602).sum := by decide
  have hdescent : baseEnd_4263602 < baseStart_4263602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263636 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4263636 : Nat := 118140960795 + 4263636 * 2 ^ 59
def prefixEnd_4263636 : Nat := 4983230072969 + 3 ^ 40 * 4263636 * 2
def baseEnd_4263636 : Nat := 729764867937728579413967

theorem tailTrace_4263636 : CollatzResearch.WordTrace tailWord_4263636 prefixEnd_4263636 729764867937728579413967 := by
  unfold tailWord_4263636
  simp only [CollatzResearch.WordTrace]
  refine ⟨77753790190791208950625381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103671720254388278600833841 77753790190791208950625381)
  ·
    refine ⟨14578835660773351678242259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77753790190791208950625381 14578835660773351678242259)
    ·
      refine ⟨21868253491160027517363389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14578835660773351678242259 21868253491160027517363389)
      ·
        refine ⟨8200595059185010319011271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21868253491160027517363389 8200595059185010319011271)
        ·
          refine ⟨12300892588777515478516907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200595059185010319011271 12300892588777515478516907)
          ·
            refine ⟨18451338883166273217775361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300892588777515478516907 18451338883166273217775361)
            ·
              refine ⟨13838504162374704913331521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18451338883166273217775361 13838504162374704913331521)
              ·
                refine ⟨10378878121781028684998641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13838504162374704913331521 10378878121781028684998641)
                ·
                  refine ⟨7784158591335771513748981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10378878121781028684998641 7784158591335771513748981)
                  ·
                    refine ⟨729764867937728579413967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7784158591335771513748981 729764867937728579413967)
                    ·
                      rfl

theorem cell23_4263636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4263636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263636 prefixEnd_4263636 := by exact prefixLift 4263636
  have htrace : WordTrace (prefixWord ++ tailWord_4263636) baseStart_4263636 baseEnd_4263636 := by
    simpa [prefixWord, tailWord_4263636, baseEnd_4263636] using wordTrace_append hprefix tailTrace_4263636
  have hstable : (prefixWord ++ tailWord_4263636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263636).length < 2 ^ (prefixWord ++ tailWord_4263636).sum := by decide
  have hdescent : baseEnd_4263636 < baseStart_4263636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263639 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_4263639 : Nat := 118140960795 + 4263639 * 2 ^ 59
def prefixEnd_4263639 : Nat := 4983230072969 + 3 ^ 40 * 4263639 * 2
def baseEnd_4263639 : Nat := 2189296144255149226504387

theorem tailTrace_4263639 : CollatzResearch.WordTrace tailWord_4263639 prefixEnd_4263639 2189296144255149226504387 := by
  unfold tailWord_4263639
  simp only [CollatzResearch.WordTrace]
  refine ⟨155507689800571549413609971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103671793200381032942406647 155507689800571549413609971)
  ·
    refine ⟨233261534700857324120414957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155507689800571549413609971 233261534700857324120414957)
    ·
      refine ⟨87473075512821496545155609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233261534700857324120414957 87473075512821496545155609)
      ·
        refine ⟨65604806634616122408866707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87473075512821496545155609 65604806634616122408866707)
        ·
          refine ⟨98407209951924183613300061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65604806634616122408866707 98407209951924183613300061)
          ·
            refine ⟨36902703731971568854987523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98407209951924183613300061 36902703731971568854987523)
            ·
              refine ⟨55354055597957353282481285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36902703731971568854987523 55354055597957353282481285)
              ·
                refine ⟨10378885424617003740465241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55354055597957353282481285 10378885424617003740465241)
                ·
                  refine ⟨7784164068462752805348931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10378885424617003740465241 7784164068462752805348931)
                  ·
                    refine ⟨11676246102694129208023397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7784164068462752805348931 11676246102694129208023397)
                    ·
                      refine ⟨2189296144255149226504387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11676246102694129208023397 2189296144255149226504387)
                      ·
                        rfl

theorem cell23_4263639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_4263639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263639 prefixEnd_4263639 := by exact prefixLift 4263639
  have htrace : WordTrace (prefixWord ++ tailWord_4263639) baseStart_4263639 baseEnd_4263639 := by
    simpa [prefixWord, tailWord_4263639, baseEnd_4263639] using wordTrace_append hprefix tailTrace_4263639
  have hstable : (prefixWord ++ tailWord_4263639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263639).length < 2 ^ (prefixWord ++ tailWord_4263639).sum := by decide
  have hdescent : baseEnd_4263639 < baseStart_4263639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263656 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4263656 : Nat := 118140960795 + 4263656 * 2 ^ 59
def prefixEnd_4263656 : Nat := 4983230072969 + 3 ^ 40 * 4263656 * 2
def baseEnd_4263656 : Nat := 2189304873426275659991809

theorem tailTrace_4263656 : CollatzResearch.WordTrace tailWord_4263656 prefixEnd_4263656 2189304873426275659991809 := by
  unfold tailWord_4263656
  simp only [CollatzResearch.WordTrace]
  refine ⟨77754154920754980658489411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103672206561006640877985881 77754154920754980658489411)
  ·
    refine ⟨116631232381132470987734117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77754154920754980658489411 116631232381132470987734117)
    ·
      refine ⟨21868356071462338310200147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116631232381132470987734117 21868356071462338310200147)
      ·
        refine ⟨32802534107193507465300221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21868356071462338310200147 32802534107193507465300221)
        ·
          refine ⟨12300950290197565299487583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32802534107193507465300221 12300950290197565299487583)
          ·
            refine ⟨18451425435296347949231375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300950290197565299487583 18451425435296347949231375)
            ·
              refine ⟨27677138152944521923847063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18451425435296347949231375 27677138152944521923847063)
              ·
                refine ⟨41515707229416782885770595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27677138152944521923847063 41515707229416782885770595)
                ·
                  refine ⟨62273560844125174328655893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41515707229416782885770595 62273560844125174328655893)
                  ·
                    refine ⟨2919073164568367546655745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62273560844125174328655893 2919073164568367546655745)
                    ·
                      refine ⟨2189304873426275659991809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919073164568367546655745 2189304873426275659991809)
                      ·
                        rfl

theorem cell23_4263656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4263656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263656 prefixEnd_4263656 := by exact prefixLift 4263656
  have htrace : WordTrace (prefixWord ++ tailWord_4263656) baseStart_4263656 baseEnd_4263656 := by
    simpa [prefixWord, tailWord_4263656, baseEnd_4263656] using wordTrace_append hprefix tailTrace_4263656
  have hstable : (prefixWord ++ tailWord_4263656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263656).length < 2 ^ (prefixWord ++ tailWord_4263656).sum := by decide
  have hdescent : baseEnd_4263656 < baseStart_4263656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263659 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3]
def baseStart_4263659 : Nat := 118140960795 + 4263659 * 2 ^ 59
def prefixEnd_4263659 : Nat := 4983230072969 + 3 ^ 40 * 4263659 * 2
def baseEnd_4263659 : Nat := 2189306413868239148254295

theorem tailTrace_4263659 : CollatzResearch.WordTrace tailWord_4263659 prefixEnd_4263659 2189306413868239148254295 := by
  unfold tailWord_4263659
  simp only [CollatzResearch.WordTrace]
  refine ⟨155508419260499092829338031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103672279506999395219558687 155508419260499092829338031)
  ·
    refine ⟨233262628890748639244007047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155508419260499092829338031 233262628890748639244007047)
    ·
      refine ⟨349893943336122958866010571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233262628890748639244007047 349893943336122958866010571)
      ·
        refine ⟨524840915004184438299015857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349893943336122958866010571 524840915004184438299015857)
        ·
          refine ⟨393630686253138328724261893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524840915004184438299015857 393630686253138328724261893)
          ·
            refine ⟨73805753672463436635799105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393630686253138328724261893 73805753672463436635799105)
            ·
              refine ⟨55354315254347577476849329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73805753672463436635799105 55354315254347577476849329)
              ·
                refine ⟨41515736440760683107636997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55354315254347577476849329 41515736440760683107636997)
                ·
                  refine ⟨7784200582642628082681937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41515736440760683107636997 7784200582642628082681937)
                  ·
                    refine ⟨5838150436981971062011453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7784200582642628082681937 5838150436981971062011453)
                    ·
                      refine ⟨2189306413868239148254295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5838150436981971062011453 2189306413868239148254295)
                      ·
                        rfl

theorem cell23_4263659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].length) (baseStart_4263659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263659 prefixEnd_4263659 := by exact prefixLift 4263659
  have htrace : WordTrace (prefixWord ++ tailWord_4263659) baseStart_4263659 baseEnd_4263659 := by
    simpa [prefixWord, tailWord_4263659, baseEnd_4263659] using wordTrace_append hprefix tailTrace_4263659
  have hstable : (prefixWord ++ tailWord_4263659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263659).length < 2 ^ (prefixWord ++ tailWord_4263659).sum := by decide
  have hdescent : baseEnd_4263659 < baseStart_4263659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263666 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_4263666 : Nat := 118140960795 + 4263666 * 2 ^ 59
def prefixEnd_4263666 : Nat := 4983230072969 + 3 ^ 40 * 4263666 * 2
def baseEnd_4263666 : Nat := 729770002744273540288921

theorem tailTrace_4263666 : CollatzResearch.WordTrace tailWord_4263666 prefixEnd_4263666 729770002744273540288921 := by
  unfold tailWord_4263666
  simp only [CollatzResearch.WordTrace]
  refine ⟨38877168642868433256210713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103672449714315822016561901 38877168642868433256210713)
  ·
    refine ⟨29157876482151324942158035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38877168642868433256210713 29157876482151324942158035)
    ·
      refine ⟨43736814723226987413237053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29157876482151324942158035 43736814723226987413237053)
      ·
        refine ⟨16401305521210120279963895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43736814723226987413237053 16401305521210120279963895)
        ·
          refine ⟨24601958281815180419945843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16401305521210120279963895 24601958281815180419945843)
          ·
            refine ⟨36902937422722770629918765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24601958281815180419945843 36902937422722770629918765)
            ·
              refine ⟨13838601533521038986219537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36902937422722770629918765 13838601533521038986219537)
              ·
                refine ⟨10378951150140779239664653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13838601533521038986219537 10378951150140779239664653)
                ·
                  refine ⟨3892106681302792214874245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10378951150140779239664653 3892106681302792214874245)
                  ·
                    refine ⟨729770002744273540288921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892106681302792214874245 729770002744273540288921)
                    ·
                      rfl

theorem cell23_4263666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_4263666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263666 prefixEnd_4263666 := by exact prefixLift 4263666
  have htrace : WordTrace (prefixWord ++ tailWord_4263666) baseStart_4263666 baseEnd_4263666 := by
    simpa [prefixWord, tailWord_4263666, baseEnd_4263666] using wordTrace_append hprefix tailTrace_4263666
  have hstable : (prefixWord ++ tailWord_4263666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263666).length < 2 ^ (prefixWord ++ tailWord_4263666).sum := by decide
  have hdescent : baseEnd_4263666 < baseStart_4263666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263740 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_4263740 : Nat := 118140960795 + 4263740 * 2 ^ 59
def prefixEnd_4263740 : Nat := 4983230072969 + 3 ^ 40 * 4263740 * 2
def baseEnd_4263740 : Nat := 2189348005801253331341423

theorem tailTrace_4263740 : CollatzResearch.WordTrace tailWord_4263740 prefixEnd_4263740 2189348005801253331341423 := by
  unfold tailWord_4263740
  simp only [CollatzResearch.WordTrace]
  refine ⟨77755686786602821831518337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103674249048803762442024449 77755686786602821831518337)
  ·
    refine ⟨58316765089952116373638753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77755686786602821831518337 58316765089952116373638753)
    ·
      refine ⟨43737573817464087280229065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58316765089952116373638753 43737573817464087280229065)
      ·
        refine ⟨32803180363098065460171799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43737573817464087280229065 32803180363098065460171799)
        ·
          refine ⟨49204770544647098190257699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32803180363098065460171799 49204770544647098190257699)
          ·
            refine ⟨73807155816970647285386549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49204770544647098190257699 73807155816970647285386549)
            ·
              refine ⟨6919420857840998183004989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73807155816970647285386549 6919420857840998183004989)
              ·
                refine ⟨2594782821690374318626871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6919420857840998183004989 2594782821690374318626871)
                ·
                  refine ⟨3892174232535561477940307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594782821690374318626871 3892174232535561477940307)
                  ·
                    refine ⟨5838261348803342216910461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892174232535561477940307 5838261348803342216910461)
                    ·
                      refine ⟨2189348005801253331341423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5838261348803342216910461 2189348005801253331341423)
                      ·
                        rfl

theorem cell23_4263740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_4263740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263740 prefixEnd_4263740 := by exact prefixLift 4263740
  have htrace : WordTrace (prefixWord ++ tailWord_4263740) baseStart_4263740 baseEnd_4263740 := by
    simpa [prefixWord, tailWord_4263740, baseEnd_4263740] using wordTrace_append hprefix tailTrace_4263740
  have hstable : (prefixWord ++ tailWord_4263740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263740).length < 2 ^ (prefixWord ++ tailWord_4263740).sum := by decide
  have hdescent : baseEnd_4263740 < baseStart_4263740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263757 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4263757 : Nat := 118140960795 + 4263757 * 2 ^ 59
def prefixEnd_4263757 : Nat := 4983230072969 + 3 ^ 40 * 4263757 * 2
def baseEnd_4263757 : Nat := 2189356734972379764828845

theorem tailTrace_4263757 : CollatzResearch.WordTrace tailWord_4263757 prefixEnd_4263757 2189356734972379764828845 := by
  unfold tailWord_4263757
  simp only [CollatzResearch.WordTrace]
  refine ⟨155511993614144055566405525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103674662409429370377603683 155511993614144055566405525)
  ·
    refine ⟨7289624700663002604675259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155511993614144055566405525 7289624700663002604675259)
    ·
      refine ⟨10934437050994503907012889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7289624700663002604675259 10934437050994503907012889)
      ·
        refine ⟨8200827788245877930259667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10934437050994503907012889 8200827788245877930259667)
        ·
          refine ⟨12301241682368816895389501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200827788245877930259667 12301241682368816895389501)
          ·
            refine ⟨4612965630888306335771063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12301241682368816895389501 4612965630888306335771063)
            ·
              refine ⟨6919448446332459503656595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612965630888306335771063 6919448446332459503656595)
              ·
                refine ⟨10379172669498689255484893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6919448446332459503656595 10379172669498689255484893)
                ·
                  refine ⟨3892189751062008470806835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10379172669498689255484893 3892189751062008470806835)
                  ·
                    refine ⟨5838284626593012706210253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892189751062008470806835 5838284626593012706210253)
                    ·
                      refine ⟨2189356734972379764828845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5838284626593012706210253 2189356734972379764828845)
                      ·
                        rfl

theorem cell23_4263757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4263757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263757 prefixEnd_4263757 := by exact prefixLift 4263757
  have htrace : WordTrace (prefixWord ++ tailWord_4263757) baseStart_4263757 baseEnd_4263757 := by
    simpa [prefixWord, tailWord_4263757, baseEnd_4263757] using wordTrace_append hprefix tailTrace_4263757
  have hstable : (prefixWord ++ tailWord_4263757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263757).length < 2 ^ (prefixWord ++ tailWord_4263757).sum := by decide
  have hdescent : baseEnd_4263757 < baseStart_4263757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263769 : List Nat := [1, 2, 1, 2, 2, 3, 4, 8]
def baseStart_4263769 : Nat := 118140960795 + 4263769 * 2 ^ 59
def prefixEnd_4263769 : Nat := 4983230072969 + 3 ^ 40 * 4263769 * 2
def baseEnd_4263769 : Nat := 81087514694082730291807

theorem tailTrace_4263769 : CollatzResearch.WordTrace tailWord_4263769 prefixEnd_4263769 81087514694082730291807 := by
  unfold tailWord_4263769
  simp only [CollatzResearch.WordTrace]
  refine ⟨155512431290100581615842361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103674954193400387743894907 155512431290100581615842361)
  ·
    refine ⟨116634323467575436211881771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155512431290100581615842361 116634323467575436211881771)
    ·
      refine ⟨174951485201363154317822657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116634323467575436211881771 174951485201363154317822657)
      ·
        refine ⟨131213613901022365738366993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174951485201363154317822657 131213613901022365738366993)
        ·
          refine ⟨98410210425766774303775245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131213613901022365738366993 98410210425766774303775245)
          ·
            refine ⟨36903828909662540363915717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98410210425766774303775245 36903828909662540363915717)
            ·
              refine ⟨6919467920561726318234197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36903828909662540363915717 6919467920561726318234197)
              ·
                refine ⟨81087514694082730291807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6919467920561726318234197 81087514694082730291807)
                ·
                  rfl

theorem cell23_4263769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 8].length) (baseStart_4263769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263769 prefixEnd_4263769 := by exact prefixLift 4263769
  have htrace : WordTrace (prefixWord ++ tailWord_4263769) baseStart_4263769 baseEnd_4263769 := by
    simpa [prefixWord, tailWord_4263769, baseEnd_4263769] using wordTrace_append hprefix tailTrace_4263769
  have hstable : (prefixWord ++ tailWord_4263769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263769).length < 2 ^ (prefixWord ++ tailWord_4263769).sum := by decide
  have hdescent : baseEnd_4263769 < baseStart_4263769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263780 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_4263780 : Nat := 118140960795 + 4263780 * 2 ^ 59
def prefixEnd_4263780 : Nat := 4983230072969 + 3 ^ 40 * 4263780 * 2
def baseEnd_4263780 : Nat := 2189368545027433174841239

theorem tailTrace_4263780 : CollatzResearch.WordTrace tailWord_4263780 prefixEnd_4263780 2189368545027433174841239 := by
  unfold tailWord_4263780
  simp only [CollatzResearch.WordTrace]
  refine ⟨77756416246530365247246397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103675221662040486996328529 77756416246530365247246397)
  ·
    refine ⟨29158656092448886967717399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77756416246530365247246397 29158656092448886967717399)
    ·
      refine ⟨43737984138673330451576099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29158656092448886967717399 43737984138673330451576099)
      ·
        refine ⟨65606976208009995677364149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43737984138673330451576099 65606976208009995677364149)
        ·
          refine ⟨6150654019500937094752889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65606976208009995677364149 6150654019500937094752889)
          ·
            refine ⟨4612990514625702821064667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6150654019500937094752889 4612990514625702821064667)
            ·
              refine ⟨6919485771938554231597001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612990514625702821064667 6919485771938554231597001)
              ·
                refine ⟨5189614328953915673697751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919485771938554231597001 5189614328953915673697751)
                ·
                  refine ⟨7784421493430873510546627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189614328953915673697751 7784421493430873510546627)
                  ·
                    refine ⟨11676632240146310265819941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7784421493430873510546627 11676632240146310265819941)
                    ·
                      refine ⟨2189368545027433174841239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11676632240146310265819941 2189368545027433174841239)
                      ·
                        rfl

theorem cell23_4263780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_4263780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263780 prefixEnd_4263780 := by exact prefixLift 4263780
  have htrace : WordTrace (prefixWord ++ tailWord_4263780) baseStart_4263780 baseEnd_4263780 := by
    simpa [prefixWord, tailWord_4263780, baseEnd_4263780] using wordTrace_append hprefix tailTrace_4263780
  have hstable : (prefixWord ++ tailWord_4263780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263780).length < 2 ^ (prefixWord ++ tailWord_4263780).sum := by decide
  have hdescent : baseEnd_4263780 < baseStart_4263780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263797 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4263797 : Nat := 118140960795 + 4263797 * 2 ^ 59
def prefixEnd_4263797 : Nat := 4983230072969 + 3 ^ 40 * 4263797 * 2
def baseEnd_4263797 : Nat := 2189377274198559608328661

theorem tailTrace_4263797 : CollatzResearch.WordTrace tailWord_4263797 prefixEnd_4263797 2189377274198559608328661 := by
  unfold tailWord_4263797
  simp only [CollatzResearch.WordTrace]
  refine ⟨155513452533999142397861645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103675635022666094931907763 155513452533999142397861645)
  ·
    refine ⟨58317544700249678399198117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155513452533999142397861645 58317544700249678399198117)
    ·
      refine ⟨10934539631296814699849647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58317544700249678399198117 10934539631296814699849647)
      ·
        refine ⟨16401809446945222049774471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10934539631296814699849647 16401809446945222049774471)
        ·
          refine ⟨24602714170417833074661707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16401809446945222049774471 24602714170417833074661707)
          ·
            refine ⟨36904071255626749611992561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24602714170417833074661707 36904071255626749611992561)
            ·
              refine ⟨27678053441720062208994421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36904071255626749611992561 27678053441720062208994421)
              ·
                refine ⟨2594817510161255832093227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27678053441720062208994421 2594817510161255832093227)
                ·
                  refine ⟨3892226265241883748139841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594817510161255832093227 3892226265241883748139841)
                  ·
                    refine ⟨2919169698931412811104881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892226265241883748139841 2919169698931412811104881)
                    ·
                      refine ⟨2189377274198559608328661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919169698931412811104881 2189377274198559608328661)
                      ·
                        rfl

theorem cell23_4263797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4263797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263797 prefixEnd_4263797 := by exact prefixLift 4263797
  have htrace : WordTrace (prefixWord ++ tailWord_4263797) baseStart_4263797 baseEnd_4263797 := by
    simpa [prefixWord, tailWord_4263797, baseEnd_4263797] using wordTrace_append hprefix tailTrace_4263797
  have hstable : (prefixWord ++ tailWord_4263797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263797).length < 2 ^ (prefixWord ++ tailWord_4263797).sum := by decide
  have hdescent : baseEnd_4263797 < baseStart_4263797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263857 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4263857 : Nat := 118140960795 + 4263857 * 2 ^ 59
def prefixEnd_4263857 : Nat := 4983230072969 + 3 ^ 40 * 4263857 * 2
def baseEnd_4263857 : Nat := 2189408083037829373578385

theorem tailTrace_4263857 : CollatzResearch.WordTrace tailWord_4263857 prefixEnd_4263857 2189408083037829373578385 := by
  unfold tailWord_4263857
  simp only [CollatzResearch.WordTrace]
  refine ⟨155515640913781772645045825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103677093942521181763363883 155515640913781772645045825)
  ·
    refine ⟨116636730685336329483784369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155515640913781772645045825 116636730685336329483784369)
    ·
      refine ⟨87477548014002247112838277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116636730685336329483784369 87477548014002247112838277)
      ·
        refine ⟨16402040252625421333657177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87477548014002247112838277 16402040252625421333657177)
        ·
          refine ⟨12301530189469066000242883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16402040252625421333657177 12301530189469066000242883)
          ·
            refine ⟨18452295284203599000364325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12301530189469066000242883 18452295284203599000364325)
            ·
              refine ⟨3459805365788174812568311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18452295284203599000364325 3459805365788174812568311)
              ·
                refine ⟨5189708048682262218852467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459805365788174812568311 5189708048682262218852467)
                ·
                  refine ⟨7784562073023393328278701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189708048682262218852467 7784562073023393328278701)
                  ·
                    refine ⟨2919210777383772498104513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7784562073023393328278701 2919210777383772498104513)
                    ·
                      refine ⟨2189408083037829373578385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919210777383772498104513 2189408083037829373578385)
                      ·
                        rfl

theorem cell23_4263857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4263857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263857 prefixEnd_4263857 := by exact prefixLift 4263857
  have htrace : WordTrace (prefixWord ++ tailWord_4263857) baseStart_4263857 baseEnd_4263857 := by
    simpa [prefixWord, tailWord_4263857, baseEnd_4263857] using wordTrace_append hprefix tailTrace_4263857
  have hstable : (prefixWord ++ tailWord_4263857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263857).length < 2 ^ (prefixWord ++ tailWord_4263857).sum := by decide
  have hdescent : baseEnd_4263857 < baseStart_4263857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263859 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 9]
def baseStart_4263859 : Nat := 118140960795 + 4263859 * 2 ^ 59
def prefixEnd_4263859 : Nat := 4983230072969 + 3 ^ 40 * 4263859 * 2
def baseEnd_4263859 : Nat := 243267678888793151750375

theorem tailTrace_4263859 : CollatzResearch.WordTrace tailWord_4263859 prefixEnd_4263859 243267678888793151750375 := by
  unfold tailWord_4263859
  simp only [CollatzResearch.WordTrace]
  refine ⟨155515713859774526986618631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103677142573183017991079087 155515713859774526986618631)
  ·
    refine ⟨233273570789661790479927947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155515713859774526986618631 233273570789661790479927947)
    ·
      refine ⟨349910356184492685719891921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233273570789661790479927947 349910356184492685719891921)
      ·
        refine ⟨262432767138369514289918941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349910356184492685719891921 262432767138369514289918941)
        ·
          refine ⟨98412287676888567858719603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262432767138369514289918941 98412287676888567858719603)
          ·
            refine ⟨147618431515332851788079405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98412287676888567858719603 147618431515332851788079405)
            ·
              refine ⟨55356911818249819420529777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147618431515332851788079405 55356911818249819420529777)
              ·
                refine ⟨41517683863687364565397333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55356911818249819420529777 41517683863687364565397333)
                ·
                  refine ⟨243267678888793151750375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41517683863687364565397333 243267678888793151750375)
                  ·
                    rfl

theorem cell23_4263859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 9].length) (baseStart_4263859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263859 prefixEnd_4263859 := by exact prefixLift 4263859
  have htrace : WordTrace (prefixWord ++ tailWord_4263859) baseStart_4263859 baseEnd_4263859 := by
    simpa [prefixWord, tailWord_4263859, baseEnd_4263859] using wordTrace_append hprefix tailTrace_4263859
  have hstable : (prefixWord ++ tailWord_4263859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263859).length < 2 ^ (prefixWord ++ tailWord_4263859).sum := by decide
  have hdescent : baseEnd_4263859 < baseStart_4263859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263887 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 2, 2, 2]
def baseStart_4263887 : Nat := 118140960795 + 4263887 * 2 ^ 59
def prefixEnd_4263887 : Nat := 4983230072969 + 3 ^ 40 * 4263887 * 2
def baseEnd_4263887 : Nat := 2189423487457464256203247

theorem tailTrace_4263887 : CollatzResearch.WordTrace tailWord_4263887 prefixEnd_4263887 2189423487457464256203247 := by
  unfold tailWord_4263887
  simp only [CollatzResearch.WordTrace]
  refine ⟨155516735103673087768637915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103677823402448725179091943 155516735103673087768637915)
  ·
    refine ⟨233275102655509631652956873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155516735103673087768637915 233275102655509631652956873)
    ·
      refine ⟨174956326991632223739717655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233275102655509631652956873 174956326991632223739717655)
      ·
        refine ⟨262434490487448335609576483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174956326991632223739717655 262434490487448335609576483)
        ·
          refine ⟨393651735731172503414364725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262434490487448335609576483 393651735731172503414364725)
          ·
            refine ⟨36904850224797422195096693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393651735731172503414364725 36904850224797422195096693)
            ·
              refine ⟨3459829708574758330790315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36904850224797422195096693 3459829708574758330790315)
              ·
                refine ⟨5189744562862137496185473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459829708574758330790315 5189744562862137496185473)
                ·
                  refine ⟨3892308422146603122139105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5189744562862137496185473 3892308422146603122139105)
                  ·
                    refine ⟨2919231316609952341604329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892308422146603122139105 2919231316609952341604329)
                    ·
                      refine ⟨2189423487457464256203247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919231316609952341604329 2189423487457464256203247)
                      ·
                        rfl

theorem cell23_4263887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 2, 2].length) (baseStart_4263887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263887 prefixEnd_4263887 := by exact prefixLift 4263887
  have htrace : WordTrace (prefixWord ++ tailWord_4263887) baseStart_4263887 baseEnd_4263887 := by
    simpa [prefixWord, tailWord_4263887, baseEnd_4263887] using wordTrace_append hprefix tailTrace_4263887
  have hstable : (prefixWord ++ tailWord_4263887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263887).length < 2 ^ (prefixWord ++ tailWord_4263887).sum := by decide
  have hdescent : baseEnd_4263887 < baseStart_4263887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263987 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 1, 4]
def baseStart_4263987 : Nat := 118140960795 + 4263987 * 2 ^ 59
def prefixEnd_4263987 : Nat := 4983230072969 + 3 ^ 40 * 4263987 * 2
def baseEnd_4263987 : Nat := 729824945174304621650929

theorem tailTrace_4263987 : CollatzResearch.WordTrace tailWord_4263987 prefixEnd_4263987 729824945174304621650929 := by
  unfold tailWord_4263987
  simp only [CollatzResearch.WordTrace]
  refine ⟨155520382403310804847278215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103680254935540536564852143 155520382403310804847278215)
  ·
    refine ⟨233280573604966207270917323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155520382403310804847278215 233280573604966207270917323)
    ·
      refine ⟨349920860407449310906375985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233280573604966207270917323 349920860407449310906375985)
      ·
        refine ⟨262440645305586983179781989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349920860407449310906375985 262440645305586983179781989)
        ·
          refine ⟨49207620994797559346209123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262440645305586983179781989 49207620994797559346209123)
          ·
            refine ⟨73811431492196339019313685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49207620994797559346209123 73811431492196339019313685)
            ·
              refine ⟨3459910851196703391530329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73811431492196339019313685 3459910851196703391530329)
              ·
                refine ⟨2594933138397527543647747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459910851196703391530329 2594933138397527543647747)
                ·
                  refine ⟨3892399707596291315471621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594933138397527543647747 3892399707596291315471621)
                  ·
                    refine ⟨729824945174304621650929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892399707596291315471621 729824945174304621650929)
                    ·
                      rfl

theorem cell23_4263987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 4].length) (baseStart_4263987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263987 prefixEnd_4263987 := by exact prefixLift 4263987
  have htrace : WordTrace (prefixWord ++ tailWord_4263987) baseStart_4263987 baseEnd_4263987 := by
    simpa [prefixWord, tailWord_4263987, baseEnd_4263987] using wordTrace_append hprefix tailTrace_4263987
  have hstable : (prefixWord ++ tailWord_4263987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263987).length < 2 ^ (prefixWord ++ tailWord_4263987).sum := by decide
  have hdescent : baseEnd_4263987 < baseStart_4263987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264034 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_4264034 : Nat := 118140960795 + 4264034 * 2 ^ 59
def prefixEnd_4264034 : Nat := 4983230072969 + 3 ^ 40 * 4264034 * 2
def baseEnd_4264034 : Nat := 243277663234852797896119

theorem tailTrace_4264034 : CollatzResearch.WordTrace tailWord_4264034 prefixEnd_4264034 243277663234852797896119 := by
  unfold tailWord_4264034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38880524158535132968559789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103681397756093687916159437 38880524158535132968559789)
  ·
    refine ⟨14580196559450674863209921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38880524158535132968559789 14580196559450674863209921)
    ·
      refine ⟨10935147419588006147407441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14580196559450674863209921 10935147419588006147407441)
      ·
        refine ⟨8201360564691004610555581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10935147419588006147407441 8201360564691004610555581)
        ·
          refine ⟨3075510211759126728958343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8201360564691004610555581 3075510211759126728958343)
          ·
            refine ⟨4613265317638690093437515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075510211759126728958343 4613265317638690093437515)
            ·
              refine ⟨6919897976458035140156273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613265317638690093437515 6919897976458035140156273)
              ·
                refine ⟨5189923482343526355117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919897976458035140156273 5189923482343526355117205)
                ·
                  refine ⟨243277663234852797896119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5189923482343526355117205 243277663234852797896119)
                  ·
                    rfl

theorem cell23_4264034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_4264034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264034 prefixEnd_4264034 := by exact prefixLift 4264034
  have htrace : WordTrace (prefixWord ++ tailWord_4264034) baseStart_4264034 baseEnd_4264034 := by
    simpa [prefixWord, tailWord_4264034, baseEnd_4264034] using wordTrace_append hprefix tailTrace_4264034
  have hstable : (prefixWord ++ tailWord_4264034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264034).length < 2 ^ (prefixWord ++ tailWord_4264034).sum := by decide
  have hdescent : baseEnd_4264034 < baseStart_4264034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264056 : List Nat := [2, 1, 2, 1, 1, 1, 3, 12]
def baseStart_4264056 : Nat := 118140960795 + 4264056 * 2 ^ 59
def prefixEnd_4264056 : Nat := 4983230072969 + 3 ^ 40 * 4264056 * 2
def baseEnd_4264056 : Nat := 81092972803262003518147

theorem tailTrace_4264056 : CollatzResearch.WordTrace tailWord_4264056 prefixEnd_4264056 81092972803262003518147 := by
  unfold tailWord_4264056
  simp only [CollatzResearch.WordTrace]
  refine ⟨77761449520030414815770011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103681932693373886421026681 77761449520030414815770011)
  ·
    refine ⟨116642174280045622223655017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77761449520030414815770011 116642174280045622223655017)
    ·
      refine ⟨87481630710034216667741263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116642174280045622223655017 87481630710034216667741263)
      ·
        refine ⟨131222446065051325001611895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87481630710034216667741263 131222446065051325001611895)
        ·
          refine ⟨196833669097576987502417843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131222446065051325001611895 196833669097576987502417843)
          ·
            refine ⟨295250503646365481253626765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196833669097576987502417843 295250503646365481253626765)
            ·
              refine ⟨110718938867387055470110037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295250503646365481253626765 110718938867387055470110037)
              ·
                refine ⟨81092972803262003518147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 110718938867387055470110037 81092972803262003518147)
                ·
                  rfl

theorem cell23_4264056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 12].length) (baseStart_4264056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264056 prefixEnd_4264056 := by exact prefixLift 4264056
  have htrace : WordTrace (prefixWord ++ tailWord_4264056) baseStart_4264056 baseEnd_4264056 := by
    simpa [prefixWord, tailWord_4264056, baseEnd_4264056] using wordTrace_append hprefix tailTrace_4264056
  have hstable : (prefixWord ++ tailWord_4264056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264056).length < 2 ^ (prefixWord ++ tailWord_4264056).sum := by decide
  have hdescent : baseEnd_4264056 < baseStart_4264056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264060 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_4264060 : Nat := 118140960795 + 4264060 * 2 ^ 59
def prefixEnd_4264060 : Nat := 4983230072969 + 3 ^ 40 * 4264060 * 2
def baseEnd_4264060 : Nat := 729837439870230693113317

theorem tailTrace_4264060 : CollatzResearch.WordTrace tailWord_4264060 prefixEnd_4264060 729837439870230693113317 := by
  unfold tailWord_4264060
  simp only [CollatzResearch.WordTrace]
  refine ⟨77761522466023169157342817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103682029954697558876457089 77761522466023169157342817)
  ·
    refine ⟨58321141849517376868007113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77761522466023169157342817 58321141849517376868007113)
    ·
      refine ⟨43740856387138032651005335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58321141849517376868007113 43740856387138032651005335)
      ·
        refine ⟨65611284580707048976508003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43740856387138032651005335 65611284580707048976508003)
        ·
          refine ⟨98416926871060573464762005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65611284580707048976508003 98416926871060573464762005)
          ·
            refine ⟨4613293447080964381160719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98416926871060573464762005 4613293447080964381160719)
            ·
              refine ⟨6919940170621446571741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613293447080964381160719 6919940170621446571741079)
              ·
                refine ⟨10379910255932169857611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6919940170621446571741079 10379910255932169857611619)
                ·
                  refine ⟨15569865383898254786417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10379910255932169857611619 15569865383898254786417429)
                  ·
                    refine ⟨729837439870230693113317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15569865383898254786417429 729837439870230693113317)
                    ·
                      rfl

theorem cell23_4264060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_4264060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264060 prefixEnd_4264060 := by exact prefixLift 4264060
  have htrace : WordTrace (prefixWord ++ tailWord_4264060) baseStart_4264060 baseEnd_4264060 := by
    simpa [prefixWord, tailWord_4264060, baseEnd_4264060] using wordTrace_append hprefix tailTrace_4264060
  have hstable : (prefixWord ++ tailWord_4264060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264060).length < 2 ^ (prefixWord ++ tailWord_4264060).sum := by decide
  have hdescent : baseEnd_4264060 < baseStart_4264060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264067 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 3, 2, 2]
def baseStart_4264067 : Nat := 118140960795 + 4264067 * 2 ^ 59
def prefixEnd_4264067 : Nat := 4983230072969 + 3 ^ 40 * 4264067 * 2
def baseEnd_4264067 : Nat := 2189515913975273551952419

theorem tailTrace_4264067 : CollatzResearch.WordTrace tailWord_4264067 prefixEnd_4264067 2189515913975273551952419 := by
  unfold tailWord_4264067
  simp only [CollatzResearch.WordTrace]
  refine ⟨155523300243020978510190455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103682200162013985673460303 155523300243020978510190455)
  ·
    refine ⟨233284950364531467765285683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155523300243020978510190455 233284950364531467765285683)
    ·
      refine ⟨349927425546797201647928525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233284950364531467765285683 349927425546797201647928525)
      ·
        refine ⟨131222784580048950617973197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349927425546797201647928525 131222784580048950617973197)
        ·
          refine ⟨49208544217518356481739949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131222784580048950617973197 49208544217518356481739949)
          ·
            refine ⟨18453204081569383680652481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49208544217518356481739949 18453204081569383680652481)
            ·
              refine ⟨13839903061177037760489361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18453204081569383680652481 13839903061177037760489361)
              ·
                refine ⟨10379927295882778320367021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13839903061177037760489361 10379927295882778320367021)
                ·
                  refine ⟨3892472735956041870137633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10379927295882778320367021 3892472735956041870137633)
                  ·
                    refine ⟨2919354551967031402603225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892472735956041870137633 2919354551967031402603225)
                    ·
                      refine ⟨2189515913975273551952419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919354551967031402603225 2189515913975273551952419)
                      ·
                        rfl

theorem cell23_4264067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_4264067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264067 prefixEnd_4264067 := by exact prefixLift 4264067
  have htrace : WordTrace (prefixWord ++ tailWord_4264067) baseStart_4264067 baseEnd_4264067 := by
    simpa [prefixWord, tailWord_4264067, baseEnd_4264067] using wordTrace_append hprefix tailTrace_4264067
  have hstable : (prefixWord ++ tailWord_4264067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264067).length < 2 ^ (prefixWord ++ tailWord_4264067).sum := by decide
  have hdescent : baseEnd_4264067 < baseStart_4264067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264078 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4264078 : Nat := 118140960795 + 4264078 * 2 ^ 59
def prefixEnd_4264078 : Nat := 4983230072969 + 3 ^ 40 * 4264078 * 2
def baseEnd_4264078 : Nat := 2189521562262473008914869

theorem tailTrace_4264078 : CollatzResearch.WordTrace tailWord_4264078 prefixEnd_4264078 2189521562262473008914869 := by
  unfold tailWord_4264078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440462680747640923605111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103682467630654084925893925 19440462680747640923605111)
  ·
    refine ⟨29160694021121461385407667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19440462680747640923605111 29160694021121461385407667)
    ·
      refine ⟨43741041031682192078111501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29160694021121461385407667 43741041031682192078111501)
      ·
        refine ⟨16402890386880822029291813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43741041031682192078111501 16402890386880822029291813)
        ·
          refine ⟨3075541947540154130492215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16402890386880822029291813 3075541947540154130492215)
          ·
            refine ⟨4613312921310231195738323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075541947540154130492215 4613312921310231195738323)
            ·
              refine ⟨6919969381965346793607485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613312921310231195738323 6919969381965346793607485)
              ·
                refine ⟨2594988518237005047602807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6919969381965346793607485 2594988518237005047602807)
                ·
                  refine ⟨3892482777355507571404211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594988518237005047602807 3892482777355507571404211)
                  ·
                    refine ⟨5838724166033261357106317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892482777355507571404211 5838724166033261357106317)
                    ·
                      refine ⟨2189521562262473008914869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5838724166033261357106317 2189521562262473008914869)
                      ·
                        rfl

theorem cell23_4264078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4264078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264078 prefixEnd_4264078 := by exact prefixLift 4264078
  have htrace : WordTrace (prefixWord ++ tailWord_4264078) baseStart_4264078 baseEnd_4264078 := by
    simpa [prefixWord, tailWord_4264078, baseEnd_4264078] using wordTrace_append hprefix tailTrace_4264078
  have hstable : (prefixWord ++ tailWord_4264078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264078).length < 2 ^ (prefixWord ++ tailWord_4264078).sum := by decide
  have hdescent : baseEnd_4264078 < baseStart_4264078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264083 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3]
def baseStart_4264083 : Nat := 118140960795 + 4264083 * 2 ^ 59
def prefixEnd_4264083 : Nat := 4983230072969 + 3 ^ 40 * 4264083 * 2
def baseEnd_4264083 : Nat := 2189524129665745489352345

theorem tailTrace_4264083 : CollatzResearch.WordTrace tailWord_4264083 prefixEnd_4264083 2189524129665745489352345 := by
  unfold tailWord_4264083
  simp only [CollatzResearch.WordTrace]
  refine ⟨155523883810963013242772903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103682589207308675495181935 155523883810963013242772903)
  ·
    refine ⟨233285825716444519864159355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155523883810963013242772903 233285825716444519864159355)
    ·
      refine ⟨349928738574666779796239033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233285825716444519864159355 349928738574666779796239033)
      ·
        refine ⟨262446553931000084847179275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349928738574666779796239033 262446553931000084847179275)
        ·
          refine ⟨393669830896500127270768913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262446553931000084847179275 393669830896500127270768913)
          ·
            refine ⟨295252373172375095453076685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393669830896500127270768913 295252373172375095453076685)
            ·
              refine ⟨110719639939640660794903757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295252373172375095453076685 110719639939640660794903757)
              ·
                refine ⟨41519864977365247798088909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110719639939640660794903757 41519864977365247798088909)
                ·
                  refine ⟨15569949366511967924283341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41519864977365247798088909 15569949366511967924283341)
                  ·
                    refine ⟨5838731012441987971606253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15569949366511967924283341 5838731012441987971606253)
                    ·
                      refine ⟨2189524129665745489352345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5838731012441987971606253 2189524129665745489352345)
                      ·
                        rfl

theorem cell23_4264083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_4264083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264083 prefixEnd_4264083 := by exact prefixLift 4264083
  have htrace : WordTrace (prefixWord ++ tailWord_4264083) baseStart_4264083 baseEnd_4264083 := by
    simpa [prefixWord, tailWord_4264083, baseEnd_4264083] using wordTrace_append hprefix tailTrace_4264083
  have hstable : (prefixWord ++ tailWord_4264083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264083).length < 2 ^ (prefixWord ++ tailWord_4264083).sum := by decide
  have hdescent : baseEnd_4264083 < baseStart_4264083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264090 : List Nat := [3, 1, 1, 5, 2, 2, 9]
def baseStart_4264090 : Nat := 118140960795 + 4264090 * 2 ^ 59
def prefixEnd_4264090 : Nat := 4983230072969 + 3 ^ 40 * 4264090 * 2
def baseEnd_4264090 : Nat := 27031206469510209406973

theorem tailTrace_4264090 : CollatzResearch.WordTrace tailWord_4264090 prefixEnd_4264090 27031206469510209406973 := by
  unfold tailWord_4264090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38881034780484413359569431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103682759414625102292185149 38881034780484413359569431)
  ·
    refine ⟨58321552170726620039354147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38881034780484413359569431 58321552170726620039354147)
    ·
      refine ⟨87482328256089930059031221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58321552170726620039354147 87482328256089930059031221)
      ·
        refine ⟨8201468274008430943034177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87482328256089930059031221 8201468274008430943034177)
        ·
          refine ⟨6151101205506323207275633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8201468274008430943034177 6151101205506323207275633)
          ·
            refine ⟨4613325904129742405456725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151101205506323207275633 4613325904129742405456725)
            ·
              refine ⟨27031206469510209406973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4613325904129742405456725 27031206469510209406973)
              ·
                rfl

theorem cell23_4264090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 9].length) (baseStart_4264090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264090 prefixEnd_4264090 := by exact prefixLift 4264090
  have htrace : WordTrace (prefixWord ++ tailWord_4264090) baseStart_4264090 baseEnd_4264090 := by
    simpa [prefixWord, tailWord_4264090, baseEnd_4264090] using wordTrace_append hprefix tailTrace_4264090
  have hstable : (prefixWord ++ tailWord_4264090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264090).length < 2 ^ (prefixWord ++ tailWord_4264090).sum := by decide
  have hdescent : baseEnd_4264090 < baseStart_4264090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264101 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_4264101 : Nat := 118140960795 + 4264101 * 2 ^ 59
def prefixEnd_4264101 : Nat := 4983230072969 + 3 ^ 40 * 4264101 * 2
def baseEnd_4264101 : Nat := 2189533372317526418927263

theorem tailTrace_4264101 : CollatzResearch.WordTrace tailWord_4264101 prefixEnd_4264101 2189533372317526418927263 := by
  unfold tailWord_4264101
  simp only [CollatzResearch.WordTrace]
  refine ⟨155524540324897802316928157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103683026883265201544618771 155524540324897802316928157)
  ·
    refine ⟨58321702621836675868848059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155524540324897802316928157 58321702621836675868848059)
    ·
      refine ⟨87482553932755013803272089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58321702621836675868848059 87482553932755013803272089)
      ·
        refine ⟨65611915449566260352454067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87482553932755013803272089 65611915449566260352454067)
        ·
          refine ⟨98417873174349390528681101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65611915449566260352454067 98417873174349390528681101)
          ·
            refine ⟨36906702440381021448255413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98417873174349390528681101 36906702440381021448255413)
            ·
              refine ⟨3460003353785720760773945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36906702440381021448255413 3460003353785720760773945)
              ·
                refine ⟨2595002515339290570580459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460003353785720760773945 2595002515339290570580459)
                ·
                  refine ⟨3892503773008935855870689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595002515339290570580459 3892503773008935855870689)
                  ·
                    refine ⟨2919377829756701891903017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892503773008935855870689 2919377829756701891903017)
                    ·
                      refine ⟨2189533372317526418927263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919377829756701891903017 2189533372317526418927263)
                      ·
                        rfl

theorem cell23_4264101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_4264101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264101 prefixEnd_4264101 := by exact prefixLift 4264101
  have htrace : WordTrace (prefixWord ++ tailWord_4264101) baseStart_4264101 baseEnd_4264101 := by
    simpa [prefixWord, tailWord_4264101, baseEnd_4264101] using wordTrace_append hprefix tailTrace_4264101
  have hstable : (prefixWord ++ tailWord_4264101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264101).length < 2 ^ (prefixWord ++ tailWord_4264101).sum := by decide
  have hdescent : baseEnd_4264101 < baseStart_4264101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264143 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_4264143 : Nat := 118140960795 + 4264143 * 2 ^ 59
def prefixEnd_4264143 : Nat := 4983230072969 + 3 ^ 40 * 4264143 * 2
def baseEnd_4264143 : Nat := 2189554938505015254602069

theorem tailTrace_4264143 : CollatzResearch.WordTrace tailWord_4264143 prefixEnd_4264143 2189554938505015254602069 := by
  unfold tailWord_4264143
  simp only [CollatzResearch.WordTrace]
  refine ⟨155526072190745643489957083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103684048127163762326638055 155526072190745643489957083)
  ·
    refine ⟨233289108286118465234935625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155526072190745643489957083 233289108286118465234935625)
    ·
      refine ⟨174966831214588848926201719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233289108286118465234935625 174966831214588848926201719)
      ·
        refine ⟨262450246821883273389302579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174966831214588848926201719 262450246821883273389302579)
        ·
          refine ⟨393675370232824910083953869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262450246821883273389302579 393675370232824910083953869)
          ·
            refine ⟨147628263837309341281482701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393675370232824910083953869 147628263837309341281482701)
            ·
              refine ⟨55360598938991002980556013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147628263837309341281482701 55360598938991002980556013)
              ·
                refine ⟨20760224602121626117708505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55360598938991002980556013 20760224602121626117708505)
                ·
                  refine ⟨15570168451591219588281379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20760224602121626117708505 15570168451591219588281379)
                  ·
                    refine ⟨23355252677386829382422069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15570168451591219588281379 23355252677386829382422069)
                    ·
                      refine ⟨2189554938505015254602069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23355252677386829382422069 2189554938505015254602069)
                      ·
                        rfl

theorem cell23_4264143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_4264143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264143 prefixEnd_4264143 := by exact prefixLift 4264143
  have htrace : WordTrace (prefixWord ++ tailWord_4264143) baseStart_4264143 baseEnd_4264143 := by
    simpa [prefixWord, tailWord_4264143, baseEnd_4264143] using wordTrace_append hprefix tailTrace_4264143
  have hstable : (prefixWord ++ tailWord_4264143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264143).length < 2 ^ (prefixWord ++ tailWord_4264143).sum := by decide
  have hdescent : baseEnd_4264143 < baseStart_4264143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264170 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_4264170 : Nat := 118140960795 + 4264170 * 2 ^ 59
def prefixEnd_4264170 : Nat := 4983230072969 + 3 ^ 40 * 4264170 * 2
def baseEnd_4264170 : Nat := 2189568802482686648964445

theorem tailTrace_4264170 : CollatzResearch.WordTrace tailWord_4264170 prefixEnd_4264170 2189568802482686648964445 := by
  unfold tailWord_4264170
  simp only [CollatzResearch.WordTrace]
  refine ⟨38881764240411956775297491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103684704641098551400793309 38881764240411956775297491)
  ·
    refine ⟨58322646360617935162946237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38881764240411956775297491 58322646360617935162946237)
    ·
      refine ⟨21870992385231725686104839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58322646360617935162946237 21870992385231725686104839)
      ·
        refine ⟨32806488577847588529157259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870992385231725686104839 32806488577847588529157259)
        ·
          refine ⟨49209732866771382793735889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32806488577847588529157259 49209732866771382793735889)
          ·
            refine ⟨36907299650078537095301917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49209732866771382793735889 36907299650078537095301917)
            ·
              refine ⟨13840237368779451410738219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36907299650078537095301917 13840237368779451410738219)
              ·
                refine ⟨20760356053169177116107329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13840237368779451410738219 20760356053169177116107329)
                ·
                  refine ⟨15570267039876882837080497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20760356053169177116107329 15570267039876882837080497)
                  ·
                    refine ⟨11677700279907662127810373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15570267039876882837080497 11677700279907662127810373)
                    ·
                      refine ⟨2189568802482686648964445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11677700279907662127810373 2189568802482686648964445)
                      ·
                        rfl

theorem cell23_4264170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_4264170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264170 prefixEnd_4264170 := by exact prefixLift 4264170
  have htrace : WordTrace (prefixWord ++ tailWord_4264170) baseStart_4264170 baseEnd_4264170 := by
    simpa [prefixWord, tailWord_4264170, baseEnd_4264170] using wordTrace_append hprefix tailTrace_4264170
  have hstable : (prefixWord ++ tailWord_4264170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264170).length < 2 ^ (prefixWord ++ tailWord_4264170).sum := by decide
  have hdescent : baseEnd_4264170 < baseStart_4264170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264240 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_4264240 : Nat := 118140960795 + 4264240 * 2 ^ 59
def prefixEnd_4264240 : Nat := 4983230072969 + 3 ^ 40 * 4264240 * 2
def baseEnd_4264240 : Nat := 729868248709500458363041

theorem tailTrace_4264240 : CollatzResearch.WordTrace tailWord_4264240 prefixEnd_4264240 729868248709500458363041 := by
  unfold tailWord_4264240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77764805035697114528119087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103686406714262819370825449 77764805035697114528119087)
  ·
    refine ⟨116647207553545671792178631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77764805035697114528119087 116647207553545671792178631)
    ·
      refine ⟨174970811330318507688267947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116647207553545671792178631 174970811330318507688267947)
      ·
        refine ⟨262456216995477761532401921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174970811330318507688267947 262456216995477761532401921)
        ·
          refine ⟨196842162746608321149301441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262456216995477761532401921 196842162746608321149301441)
          ·
            refine ⟨147631622059956240861976081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196842162746608321149301441 147631622059956240861976081)
            ·
              refine ⟨110723716544967180646482061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147631622059956240861976081 110723716544967180646482061)
              ·
                refine ⟨41521393704362692742430773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110723716544967180646482061 41521393704362692742430773)
                ·
                  refine ⟨3892630659784002444602885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41521393704362692742430773 3892630659784002444602885)
                  ·
                    refine ⟨729868248709500458363041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892630659784002444602885 729868248709500458363041)
                    ·
                      rfl

theorem cell23_4264240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_4264240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264240 prefixEnd_4264240 := by exact prefixLift 4264240
  have htrace : WordTrace (prefixWord ++ tailWord_4264240) baseStart_4264240 baseEnd_4264240 := by
    simpa [prefixWord, tailWord_4264240, baseEnd_4264240] using wordTrace_append hprefix tailTrace_4264240
  have hstable : (prefixWord ++ tailWord_4264240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264240).length < 2 ^ (prefixWord ++ tailWord_4264240).sum := by decide
  have hdescent : baseEnd_4264240 < baseStart_4264240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264274 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_4264274 : Nat := 118140960795 + 4264274 * 2 ^ 59
def prefixEnd_4264274 : Nat := 4983230072969 + 3 ^ 40 * 4264274 * 2
def baseEnd_4264274 : Nat := 729874068156918080687989

theorem tailTrace_4264274 : CollatzResearch.WordTrace tailWord_4264274 prefixEnd_4264274 729874068156918080687989 := by
  unfold tailWord_4264274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38882712538317763215743969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103687233435514035241983917 38882712538317763215743969)
  ·
    refine ⟨29162034403738322411807977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38882712538317763215743969 29162034403738322411807977)
    ·
      refine ⟨21871525802803741808855983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29162034403738322411807977 21871525802803741808855983)
      ·
        refine ⟨32807288704205612713283975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21871525802803741808855983 32807288704205612713283975)
        ·
          refine ⟨49210933056308419069925963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32807288704205612713283975 49210933056308419069925963)
          ·
            refine ⟨73816399584462628604888945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49210933056308419069925963 73816399584462628604888945)
            ·
              refine ⟨55362299688346971453666709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73816399584462628604888945 55362299688346971453666709)
              ·
                refine ⟨2595107797891264286890627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55362299688346971453666709 2595107797891264286890627)
                ·
                  refine ⟨3892661696836896430335941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595107797891264286890627 3892661696836896430335941)
                  ·
                    refine ⟨729874068156918080687989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892661696836896430335941 729874068156918080687989)
                    ·
                      rfl

theorem cell23_4264274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_4264274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264274 prefixEnd_4264274 := by exact prefixLift 4264274
  have htrace : WordTrace (prefixWord ++ tailWord_4264274) baseStart_4264274 baseEnd_4264274 := by
    simpa [prefixWord, tailWord_4264274, baseEnd_4264274] using wordTrace_append hprefix tailTrace_4264274
  have hstable : (prefixWord ++ tailWord_4264274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264274).length < 2 ^ (prefixWord ++ tailWord_4264274).sum := by decide
  have hdescent : baseEnd_4264274 < baseStart_4264274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264280 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4264280 : Nat := 118140960795 + 4264280 * 2 ^ 59
def prefixEnd_4264280 : Nat := 4983230072969 + 3 ^ 40 * 4264280 * 2
def baseEnd_4264280 : Nat := 2189625285354681218588939

theorem tailTrace_4264280 : CollatzResearch.WordTrace tailWord_4264280 prefixEnd_4264280 2189625285354681218588939 := by
  unfold tailWord_4264280
  simp only [CollatzResearch.WordTrace]
  refine ⟨77765534495624657943847147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103687379327499543925129529 77765534495624657943847147)
  ·
    refine ⟨116648301743436986915770721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77765534495624657943847147 116648301743436986915770721)
    ·
      refine ⟨87486226307577740186828041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116648301743436986915770721 87486226307577740186828041)
      ·
        refine ⟨65614669730683305140121031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87486226307577740186828041 65614669730683305140121031)
        ·
          refine ⟨98422004596024957710181547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65614669730683305140121031 98422004596024957710181547)
          ·
            refine ⟨147633006894037436565272321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98422004596024957710181547 147633006894037436565272321)
            ·
              refine ⟨110724755170528077423954241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147633006894037436565272321 110724755170528077423954241)
              ·
                refine ⟨83043566377896058067965681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110724755170528077423954241 83043566377896058067965681)
                ·
                  refine ⟨62282674783422043550974261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83043566377896058067965681 62282674783422043550974261)
                  ·
                    refine ⟨5839000760945816582903837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62282674783422043550974261 5839000760945816582903837)
                    ·
                      refine ⟨2189625285354681218588939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839000760945816582903837 2189625285354681218588939)
                      ·
                        rfl

theorem cell23_4264280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4264280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264280 prefixEnd_4264280 := by exact prefixLift 4264280
  have htrace : WordTrace (prefixWord ++ tailWord_4264280) baseStart_4264280 baseEnd_4264280 := by
    simpa [prefixWord, tailWord_4264280, baseEnd_4264280] using wordTrace_append hprefix tailTrace_4264280
  have hstable : (prefixWord ++ tailWord_4264280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264280).length < 2 ^ (prefixWord ++ tailWord_4264280).sum := by decide
  have hdescent : baseEnd_4264280 < baseStart_4264280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264287 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 6]
def baseStart_4264287 : Nat := 118140960795 + 4264287 * 2 ^ 59
def prefixEnd_4264287 : Nat := 4983230072969 + 3 ^ 40 * 4264287 * 2
def baseEnd_4264287 : Nat := 243292097746584743466823

theorem tailTrace_4264287 : CollatzResearch.WordTrace tailWord_4264287 prefixEnd_4264287 243292097746584743466823 := by
  unfold tailWord_4264287
  simp only [CollatzResearch.WordTrace]
  refine ⟨155531324302223956083199115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103687549534815970722132743 155531324302223956083199115)
  ·
    refine ⟨233296986453335934124798673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155531324302223956083199115 233296986453335934124798673)
    ·
      refine ⟨174972739840001950593599005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233296986453335934124798673 174972739840001950593599005)
      ·
        refine ⟨65614777440000731472599627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174972739840001950593599005 65614777440000731472599627)
        ·
          refine ⟨98422166160001097208899441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65614777440000731472599627 98422166160001097208899441)
          ·
            refine ⟨73816624620000822906674581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98422166160001097208899441 73816624620000822906674581)
            ·
              refine ⟨3460154279062538573750371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73816624620000822906674581 3460154279062538573750371)
              ·
                refine ⟨5190231418593807860625557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460154279062538573750371 5190231418593807860625557)
                ·
                  refine ⟨243292097746584743466823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5190231418593807860625557 243292097746584743466823)
                  ·
                    rfl

theorem cell23_4264287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 6].length) (baseStart_4264287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264287 prefixEnd_4264287 := by exact prefixLift 4264287
  have htrace : WordTrace (prefixWord ++ tailWord_4264287) baseStart_4264287 baseEnd_4264287 := by
    simpa [prefixWord, tailWord_4264287, baseEnd_4264287] using wordTrace_append hprefix tailTrace_4264287
  have hstable : (prefixWord ++ tailWord_4264287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264287).length < 2 ^ (prefixWord ++ tailWord_4264287).sum := by decide
  have hdescent : baseEnd_4264287 < baseStart_4264287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264297 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_4264297 : Nat := 118140960795 + 4264297 * 2 ^ 59
def prefixEnd_4264297 : Nat := 4983230072969 + 3 ^ 40 * 4264297 * 2
def baseEnd_4264297 : Nat := 2189634014525807652076361

theorem tailTrace_4264297 : CollatzResearch.WordTrace tailWord_4264297 prefixEnd_4264297 2189634014525807652076361 := by
  unfold tailWord_4264297
  simp only [CollatzResearch.WordTrace]
  refine ⟨155531689032187727791063145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103687792688125151860708763 155531689032187727791063145)
  ·
    refine ⟨116648766774140795843297359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155531689032187727791063145 116648766774140795843297359)
    ·
      refine ⟨174973150161211193764946039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116648766774140795843297359 174973150161211193764946039)
      ·
        refine ⟨262459725241816790647419059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174973150161211193764946039 262459725241816790647419059)
        ·
          refine ⟨393689587862725185971128589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262459725241816790647419059 393689587862725185971128589)
          ·
            refine ⟨147633595448521944739173221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393689587862725185971128589 147633595448521944739173221)
            ·
              refine ⟨27681299146597864638594979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147633595448521944739173221 27681299146597864638594979)
              ·
                refine ⟨41521948719896796957892469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27681299146597864638594979 41521948719896796957892469)
                ·
                  refine ⟨3892682692490324714802419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41521948719896796957892469 3892682692490324714802419)
                  ·
                    refine ⟨5839024038735487072203629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892682692490324714802419 5839024038735487072203629)
                    ·
                      refine ⟨2189634014525807652076361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839024038735487072203629 2189634014525807652076361)
                      ·
                        rfl

theorem cell23_4264297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_4264297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264297 prefixEnd_4264297 := by exact prefixLift 4264297
  have htrace : WordTrace (prefixWord ++ tailWord_4264297) baseStart_4264297 baseEnd_4264297 := by
    simpa [prefixWord, tailWord_4264297, baseEnd_4264297] using wordTrace_append hprefix tailTrace_4264297
  have hstable : (prefixWord ++ tailWord_4264297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264297).length < 2 ^ (prefixWord ++ tailWord_4264297).sum := by decide
  have hdescent : baseEnd_4264297 < baseStart_4264297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264307 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 6, 3, 2]
def baseStart_4264307 : Nat := 118140960795 + 4264307 * 2 ^ 59
def prefixEnd_4264307 : Nat := 4983230072969 + 3 ^ 40 * 4264307 * 2
def baseEnd_4264307 : Nat := 2189639149332352612951315

theorem tailTrace_4264307 : CollatzResearch.WordTrace tailWord_4264307 prefixEnd_4264307 2189639149332352612951315 := by
  unfold tailWord_4264307
  simp only [CollatzResearch.WordTrace]
  refine ⟨155532053762151499498927175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103688035841434332999284783 155532053762151499498927175)
  ·
    refine ⟨233298080643227249248390763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155532053762151499498927175 233298080643227249248390763)
    ·
      refine ⟨349947120964840873872586145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233298080643227249248390763 349947120964840873872586145)
      ·
        refine ⟨262460340723630655404439609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349947120964840873872586145 262460340723630655404439609)
        ·
          refine ⟨196845255542722991553329707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262460340723630655404439609 196845255542722991553329707)
          ·
            refine ⟨295267883314084487329994561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196845255542722991553329707 295267883314084487329994561)
            ·
              refine ⟨221450912485563365497495921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295267883314084487329994561 221450912485563365497495921)
              ·
                refine ⟨166088184364172524123121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221450912485563365497495921 166088184364172524123121941)
                ·
                  refine ⟨7785383642070587068271341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 166088184364172524123121941 7785383642070587068271341)
                  ·
                    refine ⟨2919518865776470150601753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7785383642070587068271341 2919518865776470150601753)
                    ·
                      refine ⟨2189639149332352612951315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919518865776470150601753 2189639149332352612951315)
                      ·
                        rfl

theorem cell23_4264307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3, 2].length) (baseStart_4264307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264307 prefixEnd_4264307 := by exact prefixLift 4264307
  have htrace : WordTrace (prefixWord ++ tailWord_4264307) baseStart_4264307 baseEnd_4264307 := by
    simpa [prefixWord, tailWord_4264307, baseEnd_4264307] using wordTrace_append hprefix tailTrace_4264307
  have hstable : (prefixWord ++ tailWord_4264307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264307).length < 2 ^ (prefixWord ++ tailWord_4264307).sum := by decide
  have hdescent : baseEnd_4264307 < baseStart_4264307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264324 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_4264324 : Nat := 118140960795 + 4264324 * 2 ^ 59
def prefixEnd_4264324 : Nat := 4983230072969 + 3 ^ 40 * 4264324 * 2
def baseEnd_4264324 : Nat := 2189647878503479046438737

theorem tailTrace_4264324 : CollatzResearch.WordTrace tailWord_4264324 prefixEnd_4264324 2189647878503479046438737 := by
  unfold tailWord_4264324
  simp only [CollatzResearch.WordTrace]
  refine ⟨77766336901544955701148013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103688449202059940934864017 77766336901544955701148013)
  ·
    refine ⟨29162376338079358387930505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77766336901544955701148013 29162376338079358387930505)
    ·
      refine ⟨21871782253559518790947879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29162376338079358387930505 21871782253559518790947879)
      ·
        refine ⟨32807673380339278186421819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21871782253559518790947879 32807673380339278186421819)
        ·
          refine ⟨49211510070508917279632729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32807673380339278186421819 49211510070508917279632729)
          ·
            refine ⟨36908632552881687959724547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49211510070508917279632729 36908632552881687959724547)
            ·
              refine ⟨55362948829322531939586821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36908632552881687959724547 55362948829322531939586821)
              ·
                refine ⟨10380552905497974738672529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55362948829322531939586821 10380552905497974738672529)
                ·
                  refine ⟨7785414679123481054004397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10380552905497974738672529 7785414679123481054004397)
                  ·
                    refine ⟨2919530504671305395251649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7785414679123481054004397 2919530504671305395251649)
                    ·
                      refine ⟨2189647878503479046438737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919530504671305395251649 2189647878503479046438737)
                      ·
                        rfl

theorem cell23_4264324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_4264324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264324 prefixEnd_4264324 := by exact prefixLift 4264324
  have htrace : WordTrace (prefixWord ++ tailWord_4264324) baseStart_4264324 baseEnd_4264324 := by
    simpa [prefixWord, tailWord_4264324, baseEnd_4264324] using wordTrace_append hprefix tailTrace_4264324
  have hstable : (prefixWord ++ tailWord_4264324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264324).length < 2 ^ (prefixWord ++ tailWord_4264324).sum := by decide
  have hdescent : baseEnd_4264324 < baseStart_4264324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264331 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 1, 1, 3]
def baseStart_4264331 : Nat := 118140960795 + 4264331 * 2 ^ 59
def prefixEnd_4264331 : Nat := 4983230072969 + 3 ^ 40 * 4264331 * 2
def baseEnd_4264331 : Nat := 2189651472868060519051205

theorem tailTrace_4264331 : CollatzResearch.WordTrace tailWord_4264331 prefixEnd_4264331 2189651472868060519051205 := by
  unfold tailWord_4264331
  simp only [CollatzResearch.WordTrace]
  refine ⟨155532929114064551597800847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103688619409376367731867231 155532929114064551597800847)
  ·
    refine ⟨233299393671096827396701271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155532929114064551597800847 233299393671096827396701271)
    ·
      refine ⟨349949090506645241095051907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233299393671096827396701271 349949090506645241095051907)
      ·
        refine ⟨524923635759967861642577861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349949090506645241095051907 524923635759967861642577861)
        ·
          refine ⟨98423181704993974057983349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 524923635759967861642577861 98423181704993974057983349)
          ·
            refine ⟨9227173284843185067935939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98423181704993974057983349 9227173284843185067935939)
            ·
              refine ⟨13840759927264777601903909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227173284843185067935939 13840759927264777601903909)
              ·
                refine ⟨2595142486362145800356983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13840759927264777601903909 2595142486362145800356983)
                ·
                  refine ⟨3892713729543218700535475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595142486362145800356983 3892713729543218700535475)
                  ·
                    refine ⟨5839070594314828050803213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892713729543218700535475 5839070594314828050803213)
                    ·
                      refine ⟨2189651472868060519051205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839070594314828050803213 2189651472868060519051205)
                      ·
                        rfl

theorem cell23_4264331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 1, 3].length) (baseStart_4264331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264331 prefixEnd_4264331 := by exact prefixLift 4264331
  have htrace : WordTrace (prefixWord ++ tailWord_4264331) baseStart_4264331 baseEnd_4264331 := by
    simpa [prefixWord, tailWord_4264331, baseEnd_4264331] using wordTrace_append hprefix tailTrace_4264331
  have hstable : (prefixWord ++ tailWord_4264331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264331).length < 2 ^ (prefixWord ++ tailWord_4264331).sum := by decide
  have hdescent : baseEnd_4264331 < baseStart_4264331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264354 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4264354 : Nat := 118140960795 + 4264354 * 2 ^ 59
def prefixEnd_4264354 : Nat := 4983230072969 + 3 ^ 40 * 4264354 * 2
def baseEnd_4264354 : Nat := 2189663282923113929063599

theorem tailTrace_4264354 : CollatzResearch.WordTrace tailWord_4264354 prefixEnd_4264354 2189663282923113929063599 := by
  unfold tailWord_4264354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38883441998245306631472029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103689178661987484350592077 38883441998245306631472029)
  ·
    refine ⟨14581290749341989986802011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38883441998245306631472029 14581290749341989986802011)
    ·
      refine ⟨21871936124012984980203017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14581290749341989986802011 21871936124012984980203017)
      ·
        refine ⟨16403952093009738735152263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21871936124012984980203017 16403952093009738735152263)
        ·
          refine ⟨24605928139514608102728395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16403952093009738735152263 24605928139514608102728395)
          ·
            refine ⟨36908892209271912154092593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24605928139514608102728395 36908892209271912154092593)
            ·
              refine ⟨27681669156953934115569445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36908892209271912154092593 27681669156953934115569445)
              ·
                refine ⟨5190312966928862646669271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27681669156953934115569445 5190312966928862646669271)
                ·
                  refine ⟨7785469450393293970003907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5190312966928862646669271 7785469450393293970003907)
                  ·
                    refine ⟨11678204175589940955005861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7785469450393293970003907 11678204175589940955005861)
                    ·
                      refine ⟨2189663282923113929063599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11678204175589940955005861 2189663282923113929063599)
                      ·
                        rfl

theorem cell23_4264354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4264354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264354 prefixEnd_4264354 := by exact prefixLift 4264354
  have htrace : WordTrace (prefixWord ++ tailWord_4264354) baseStart_4264354 baseEnd_4264354 := by
    simpa [prefixWord, tailWord_4264354, baseEnd_4264354] using wordTrace_append hprefix tailTrace_4264354
  have hstable : (prefixWord ++ tailWord_4264354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264354).length < 2 ^ (prefixWord ++ tailWord_4264354).sum := by decide
  have hdescent : baseEnd_4264354 < baseStart_4264354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264357 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_4264357 : Nat := 118140960795 + 4264357 * 2 ^ 59
def prefixEnd_4264357 : Nat := 4983230072969 + 3 ^ 40 * 4264357 * 2
def baseEnd_4264357 : Nat := 2189664823365077417326085

theorem tailTrace_4264357 : CollatzResearch.WordTrace tailWord_4264357 prefixEnd_4264357 2189664823365077417326085 := by
  unfold tailWord_4264357
  simp only [CollatzResearch.WordTrace]
  refine ⟨155533877411970358038247325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103689251607980238692164883 155533877411970358038247325)
  ·
    refine ⟨58325204029488884264342747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155533877411970358038247325 58325204029488884264342747)
    ·
      refine ⟨87487806044233326396514121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58325204029488884264342747 87487806044233326396514121)
      ·
        refine ⟨65615854533174994797385591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87487806044233326396514121 65615854533174994797385591)
        ·
          refine ⟨98423781799762492196078387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65615854533174994797385591 98423781799762492196078387)
          ·
            refine ⟨147635672699643738294117581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98423781799762492196078387 147635672699643738294117581)
            ·
              refine ⟨55363377262366401860294093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147635672699643738294117581 55363377262366401860294093)
              ·
                refine ⟨20761266473387400697610285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55363377262366401860294093 20761266473387400697610285)
                ·
                  refine ⟨7785474927520275261603857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20761266473387400697610285 7785474927520275261603857)
                  ·
                    refine ⟨5839106195640206446202893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7785474927520275261603857 5839106195640206446202893)
                    ·
                      refine ⟨2189664823365077417326085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839106195640206446202893 2189664823365077417326085)
                      ·
                        rfl

theorem cell23_4264357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_4264357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264357 prefixEnd_4264357 := by exact prefixLift 4264357
  have htrace : WordTrace (prefixWord ++ tailWord_4264357) baseStart_4264357 baseEnd_4264357 := by
    simpa [prefixWord, tailWord_4264357, baseEnd_4264357] using wordTrace_append hprefix tailTrace_4264357
  have hstable : (prefixWord ++ tailWord_4264357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264357).length < 2 ^ (prefixWord ++ tailWord_4264357).sum := by decide
  have hdescent : baseEnd_4264357 < baseStart_4264357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264365 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4264365 : Nat := 118140960795 + 4264365 * 2 ^ 59
def prefixEnd_4264365 : Nat := 4983230072969 + 3 ^ 40 * 4264365 * 2
def baseEnd_4264365 : Nat := 2189668931210313386026049

theorem tailTrace_4264365 : CollatzResearch.WordTrace tailWord_4264365 prefixEnd_4264365 2189668931210313386026049 := by
  unfold tailWord_4264365
  simp only [CollatzResearch.WordTrace]
  refine ⟨155534169195941375404538549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103689446130627583603025699 155534169195941375404538549)
  ·
    refine ⟨14581328362119503944175489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155534169195941375404538549 14581328362119503944175489)
    ·
      refine ⟨10935996271589627958131617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14581328362119503944175489 10935996271589627958131617)
      ·
        refine ⟨8201997203692220968598713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10935996271589627958131617 8201997203692220968598713)
        ·
          refine ⟨6151497902769165726449035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8201997203692220968598713 6151497902769165726449035)
          ·
            refine ⟨9227246854153748589673553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151497902769165726449035 9227246854153748589673553)
            ·
              refine ⟨6920435140615311442255165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9227246854153748589673553 6920435140615311442255165)
              ·
                refine ⟨2595163177730741790845687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6920435140615311442255165 2595163177730741790845687)
                ·
                  refine ⟨3892744766596112686268531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595163177730741790845687 3892744766596112686268531)
                  ·
                    refine ⟨5839117149894169029402797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892744766596112686268531 5839117149894169029402797)
                    ·
                      refine ⟨2189668931210313386026049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839117149894169029402797 2189668931210313386026049)
                      ·
                        rfl

theorem cell23_4264365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4264365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264365 prefixEnd_4264365 := by exact prefixLift 4264365
  have htrace : WordTrace (prefixWord ++ tailWord_4264365) baseStart_4264365 baseEnd_4264365 := by
    simpa [prefixWord, tailWord_4264365, baseEnd_4264365] using wordTrace_append hprefix tailTrace_4264365
  have hstable : (prefixWord ++ tailWord_4264365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264365).length < 2 ^ (prefixWord ++ tailWord_4264365).sum := by decide
  have hdescent : baseEnd_4264365 < baseStart_4264365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264381 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_4264381 : Nat := 118140960795 + 4264381 * 2 ^ 59
def prefixEnd_4264381 : Nat := 4983230072969 + 3 ^ 40 * 4264381 * 2
def baseEnd_4264381 : Nat := 729892382300261774475325

theorem tailTrace_4264381 : CollatzResearch.WordTrace tailWord_4264381 prefixEnd_4264381 729892382300261774475325 := by
  unfold tailWord_4264381
  simp only [CollatzResearch.WordTrace]
  refine ⟨155534752763883410137120997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103689835175922273424747331 155534752763883410137120997)
  ·
    refine ⟨29162766143228139400710187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155534752763883410137120997 29162766143228139400710187)
    ·
      refine ⟨43744149214842209101065281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29162766143228139400710187 43744149214842209101065281)
      ·
        refine ⟨32808111911131656825798961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43744149214842209101065281 32808111911131656825798961)
        ·
          refine ⟨24606083933348742619349221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32808111911131656825798961 24606083933348742619349221)
          ·
            refine ⟨4613640737502889241127979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24606083933348742619349221 4613640737502889241127979)
            ·
              refine ⟨6920461106254333861691969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613640737502889241127979 6920461106254333861691969)
              ·
                refine ⟨5190345829690750396268977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6920461106254333861691969 5190345829690750396268977)
                ·
                  refine ⟨3892759372268062797201733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5190345829690750396268977 3892759372268062797201733)
                  ·
                    refine ⟨729892382300261774475325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892759372268062797201733 729892382300261774475325)
                    ·
                      rfl

theorem cell23_4264381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_4264381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264381 prefixEnd_4264381 := by exact prefixLift 4264381
  have htrace : WordTrace (prefixWord ++ tailWord_4264381) baseStart_4264381 baseEnd_4264381 := by
    simpa [prefixWord, tailWord_4264381, baseEnd_4264381] using wordTrace_append hprefix tailTrace_4264381
  have hstable : (prefixWord ++ tailWord_4264381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264381).length < 2 ^ (prefixWord ++ tailWord_4264381).sum := by decide
  have hdescent : baseEnd_4264381 < baseStart_4264381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264400 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_4264400 : Nat := 118140960795 + 4264400 * 2 ^ 59
def prefixEnd_4264400 : Nat := 4983230072969 + 3 ^ 40 * 4264400 * 2
def baseEnd_4264400 : Nat := 2189686903033220749088387

theorem tailTrace_4264400 : CollatzResearch.WordTrace tailWord_4264400 prefixEnd_4264400 2189686903033220749088387 := by
  unfold tailWord_4264400
  simp only [CollatzResearch.WordTrace]
  refine ⟨77767722875407288191031327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103690297167209717588041769 77767722875407288191031327)
  ·
    refine ⟨116651584313110932286546991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77767722875407288191031327 116651584313110932286546991)
    ·
      refine ⟨174977376469666398429820487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116651584313110932286546991 174977376469666398429820487)
      ·
        refine ⟨262466064704499597644730731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174977376469666398429820487 262466064704499597644730731)
        ·
          refine ⟨393699097056749396467096097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262466064704499597644730731 393699097056749396467096097)
          ·
            refine ⟨295274322792562047350322073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393699097056749396467096097 295274322792562047350322073)
            ·
              refine ⟨221455742094421535512741555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295274322792562047350322073 221455742094421535512741555)
              ·
                refine ⟨332183613141632303269112333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221455742094421535512741555 332183613141632303269112333)
                ·
                  refine ⟨124568854928112113725917125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332183613141632303269112333 124568854928112113725917125)
                  ·
                    refine ⟨23356660299021021323609461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124568854928112113725917125 23356660299021021323609461)
                    ·
                      refine ⟨2189686903033220749088387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23356660299021021323609461 2189686903033220749088387)
                      ·
                        rfl

theorem cell23_4264400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_4264400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264400 prefixEnd_4264400 := by exact prefixLift 4264400
  have htrace : WordTrace (prefixWord ++ tailWord_4264400) baseStart_4264400 baseEnd_4264400 := by
    simpa [prefixWord, tailWord_4264400, baseEnd_4264400] using wordTrace_append hprefix tailTrace_4264400
  have hstable : (prefixWord ++ tailWord_4264400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264400).length < 2 ^ (prefixWord ++ tailWord_4264400).sum := by decide
  have hdescent : baseEnd_4264400 < baseStart_4264400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264447 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_4264447 : Nat := 118140960795 + 4264447 * 2 ^ 59
def prefixEnd_4264447 : Nat := 4983230072969 + 3 ^ 40 * 4264447 * 2
def baseEnd_4264447 : Nat := 2189711036623982065200671

theorem tailTrace_4264447 : CollatzResearch.WordTrace tailWord_4264447 prefixEnd_4264447 2189711036623982065200671 := by
  unfold tailWord_4264447
  simp only [CollatzResearch.WordTrace]
  refine ⟨155537159981644303409023595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103691439987762868939349063 155537159981644303409023595)
  ·
    refine ⟨233305739972466455113535393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155537159981644303409023595 233305739972466455113535393)
    ·
      refine ⟨174979304979349841335151545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233305739972466455113535393 174979304979349841335151545)
      ·
        refine ⟨131234478734512381001363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174979304979349841335151545 131234478734512381001363659)
        ·
          refine ⟨196851718101768571502045489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131234478734512381001363659 196851718101768571502045489)
          ·
            refine ⟨147638788576326428626534117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196851718101768571502045489 147638788576326428626534117)
            ·
              refine ⟨27682272858061205367475147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147638788576326428626534117 27682272858061205367475147)
              ·
                refine ⟨41523409287091808051212721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27682272858061205367475147 41523409287091808051212721)
                ·
                  refine ⟨31142556965318856038409541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41523409287091808051212721 31142556965318856038409541)
                  ·
                    refine ⟨5839229430997285507201789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31142556965318856038409541 5839229430997285507201789)
                    ·
                      refine ⟨2189711036623982065200671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839229430997285507201789 2189711036623982065200671)
                      ·
                        rfl

theorem cell23_4264447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_4264447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264447 prefixEnd_4264447 := by exact prefixLift 4264447
  have htrace : WordTrace (prefixWord ++ tailWord_4264447) baseStart_4264447 baseEnd_4264447 := by
    simpa [prefixWord, tailWord_4264447, baseEnd_4264447] using wordTrace_append hprefix tailTrace_4264447
  have hstable : (prefixWord ++ tailWord_4264447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264447).length < 2 ^ (prefixWord ++ tailWord_4264447).sum := by decide
  have hdescent : baseEnd_4264447 < baseStart_4264447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264455 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4264455 : Nat := 118140960795 + 4264455 * 2 ^ 59
def prefixEnd_4264455 : Nat := 4983230072969 + 3 ^ 40 * 4264455 * 2
def baseEnd_4264455 : Nat := 2189715144469218033900635

theorem tailTrace_4264455 : CollatzResearch.WordTrace tailWord_4264455 prefixEnd_4264455 2189715144469218033900635 := by
  unfold tailWord_4264455
  simp only [CollatzResearch.WordTrace]
  refine ⟨155537451765615320775314819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103691634510410213850209879 155537451765615320775314819)
  ·
    refine ⟨233306177648422981162972229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155537451765615320775314819 233306177648422981162972229)
    ·
      refine ⟨43744908309079308968057293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233306177648422981162972229 43744908309079308968057293)
      ·
        refine ⟨16404340615904740863021485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43744908309079308968057293 16404340615904740863021485)
        ·
          refine ⟨6151627730964277823633057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16404340615904740863021485 6151627730964277823633057)
          ·
            refine ⟨4613720798223208367724793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151627730964277823633057 4613720798223208367724793)
            ·
              refine ⟨3460290598667406275793595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613720798223208367724793 3460290598667406275793595)
              ·
                refine ⟨5190435898001109413690393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460290598667406275793595 5190435898001109413690393)
                ·
                  refine ⟨3892826923500832060267795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5190435898001109413690393 3892826923500832060267795)
                  ·
                    refine ⟨5839240385251248090401693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892826923500832060267795 5839240385251248090401693)
                    ·
                      refine ⟨2189715144469218033900635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839240385251248090401693 2189715144469218033900635)
                      ·
                        rfl

theorem cell23_4264455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4264455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264455 prefixEnd_4264455 := by exact prefixLift 4264455
  have htrace : WordTrace (prefixWord ++ tailWord_4264455) baseStart_4264455 baseEnd_4264455 := by
    simpa [prefixWord, tailWord_4264455, baseEnd_4264455] using wordTrace_append hprefix tailTrace_4264455
  have hstable : (prefixWord ++ tailWord_4264455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264455).length < 2 ^ (prefixWord ++ tailWord_4264455).sum := by decide
  have hdescent : baseEnd_4264455 < baseStart_4264455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264504 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_4264504 : Nat := 118140960795 + 4264504 * 2 ^ 59
def prefixEnd_4264504 : Nat := 4983230072969 + 3 ^ 40 * 4264504 * 2
def baseEnd_4264504 : Nat := 2189740305021288342187909

theorem tailTrace_4264504 : CollatzResearch.WordTrace tailWord_4264504 prefixEnd_4264504 2189740305021288342187909 := by
  unfold tailWord_4264504
  simp only [CollatzResearch.WordTrace]
  refine ⟨77769619471218901071924283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103692825961625201429232377 77769619471218901071924283)
  ·
    refine ⟨116654429206828351607886425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77769619471218901071924283 116654429206828351607886425)
    ·
      refine ⟨87490821905121263705914819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116654429206828351607886425 87490821905121263705914819)
      ·
        refine ⟨131236232857681895558872229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87490821905121263705914819 131236232857681895558872229)
        ·
          refine ⟨24606793660815355417288543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131236232857681895558872229 24606793660815355417288543)
          ·
            refine ⟨36910190491223033125932815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24606793660815355417288543 36910190491223033125932815)
            ·
              refine ⟨55365285736834549688899223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36910190491223033125932815 55365285736834549688899223)
              ·
                refine ⟨83047928605251824533348835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55365285736834549688899223 83047928605251824533348835)
                ·
                  refine ⟨124571892907877736800023253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83047928605251824533348835 124571892907877736800023253)
                  ·
                    refine ⟨2919653740028384456250545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 124571892907877736800023253 2919653740028384456250545)
                    ·
                      refine ⟨2189740305021288342187909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2919653740028384456250545 2189740305021288342187909)
                      ·
                        rfl

theorem cell23_4264504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_4264504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264504 prefixEnd_4264504 := by exact prefixLift 4264504
  have htrace : WordTrace (prefixWord ++ tailWord_4264504) baseStart_4264504 baseEnd_4264504 := by
    simpa [prefixWord, tailWord_4264504, baseEnd_4264504] using wordTrace_append hprefix tailTrace_4264504
  have hstable : (prefixWord ++ tailWord_4264504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264504).length < 2 ^ (prefixWord ++ tailWord_4264504).sum := by decide
  have hdescent : baseEnd_4264504 < baseStart_4264504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264547 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4264547 : Nat := 118140960795 + 4264547 * 2 ^ 59
def prefixEnd_4264547 : Nat := 4983230072969 + 3 ^ 40 * 4264547 * 2
def baseEnd_4264547 : Nat := 2189762384689431673950211

theorem tailTrace_4264547 : CollatzResearch.WordTrace tailWord_4264547 prefixEnd_4264547 2189762384689431673950211 := by
  unfold tailWord_4264547
  simp only [CollatzResearch.WordTrace]
  refine ⟨155540807281282020487663895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103693871520854680325109263 155540807281282020487663895)
  ·
    refine ⟨233311210921923030731495843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155540807281282020487663895 233311210921923030731495843)
    ·
      refine ⟨349966816382884546097243765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233311210921923030731495843 349966816382884546097243765)
      ·
        refine ⟨32809389035895426196616603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 349966816382884546097243765 32809389035895426196616603)
        ·
          refine ⟨49214083553843139294924905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32809389035895426196616603 49214083553843139294924905)
          ·
            refine ⟨36910562665382354471193679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49214083553843139294924905 36910562665382354471193679)
            ·
              refine ⟨55365843998073531706790519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36910562665382354471193679 55365843998073531706790519)
              ·
                refine ⟨83048765997110297560185779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55365843998073531706790519 83048765997110297560185779)
                ·
                  refine ⟨124573148995665446340278669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83048765997110297560185779 124573148995665446340278669)
                  ·
                    refine ⟨46714930873374542377604501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124573148995665446340278669 46714930873374542377604501)
                    ·
                      refine ⟨2189762384689431673950211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46714930873374542377604501 2189762384689431673950211)
                      ·
                        rfl

theorem cell23_4264547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4264547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264547 prefixEnd_4264547 := by exact prefixLift 4264547
  have htrace : WordTrace (prefixWord ++ tailWord_4264547) baseStart_4264547 baseEnd_4264547 := by
    simpa [prefixWord, tailWord_4264547, baseEnd_4264547] using wordTrace_append hprefix tailTrace_4264547
  have hstable : (prefixWord ++ tailWord_4264547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264547).length < 2 ^ (prefixWord ++ tailWord_4264547).sum := by decide
  have hdescent : baseEnd_4264547 < baseStart_4264547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264624 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_4264624 : Nat := 118140960795 + 4264624 * 2 ^ 59
def prefixEnd_4264624 : Nat := 4983230072969 + 3 ^ 40 * 4264624 * 2
def baseEnd_4264624 : Nat := 2189801922699827872687357

theorem tailTrace_4264624 : CollatzResearch.WordTrace tailWord_4264624 prefixEnd_4264624 2189801922699827872687357 := by
  unfold tailWord_4264624
  simp only [CollatzResearch.WordTrace]
  refine ⟨77771807851001531319108463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103695743801335375092144617 77771807851001531319108463)
  ·
    refine ⟨116657711776502296978662695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77771807851001531319108463 116657711776502296978662695)
    ·
      refine ⟨174986567664753445467994043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116657711776502296978662695 174986567664753445467994043)
      ·
        refine ⟨262479851497130168201991065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174986567664753445467994043 262479851497130168201991065)
        ·
          refine ⟨196859888622847626151493299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262479851497130168201991065 196859888622847626151493299)
          ·
            refine ⟨295289832934271439227239949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196859888622847626151493299 295289832934271439227239949)
            ·
              refine ⟨110733687350351789710214981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295289832934271439227239949 110733687350351789710214981)
              ·
                refine ⟨20762566378190960570665309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110733687350351789710214981 20762566378190960570665309)
                ·
                  refine ⟨7785962391821610213999491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20762566378190960570665309 7785962391821610213999491)
                  ·
                    refine ⟨11678943587732415320999237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7785962391821610213999491 11678943587732415320999237)
                    ·
                      refine ⟨2189801922699827872687357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11678943587732415320999237 2189801922699827872687357)
                      ·
                        rfl

theorem cell23_4264624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_4264624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264624 prefixEnd_4264624 := by exact prefixLift 4264624
  have htrace : WordTrace (prefixWord ++ tailWord_4264624) baseStart_4264624 baseEnd_4264624 := by
    simpa [prefixWord, tailWord_4264624, baseEnd_4264624] using wordTrace_append hprefix tailTrace_4264624
  have hstable : (prefixWord ++ tailWord_4264624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264624).length < 2 ^ (prefixWord ++ tailWord_4264624).sum := by decide
  have hdescent : baseEnd_4264624 < baseStart_4264624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264625 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 6]
def baseStart_4264625 : Nat := 118140960795 + 4264625 * 2 ^ 59
def prefixEnd_4264625 : Nat := 4983230072969 + 3 ^ 40 * 4264625 * 2
def baseEnd_4264625 : Nat := 243311381797831374308317

theorem tailTrace_4264625 : CollatzResearch.WordTrace tailWord_4264625 prefixEnd_4264625 243311381797831374308317 := by
  unfold tailWord_4264625
  simp only [CollatzResearch.WordTrace]
  refine ⟨155543652174999439809003329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103695768116666293206002219 155543652174999439809003329)
  ·
    refine ⟨116657739131249579856752497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155543652174999439809003329 116657739131249579856752497)
    ·
      refine ⟨87493304348437184892564373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116657739131249579856752497 87493304348437184892564373)
      ·
        refine ⟨4101248641332993041838955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87493304348437184892564373 4101248641332993041838955)
        ·
          refine ⟨6151872961999489562758433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101248641332993041838955 6151872961999489562758433)
          ·
            refine ⟨4613904721499617172068825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151872961999489562758433 4613904721499617172068825)
            ·
              refine ⟨3460428541124712879051619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613904721499617172068825 3460428541124712879051619)
              ·
                refine ⟨5190642811687069318577429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460428541124712879051619 5190642811687069318577429)
                ·
                  refine ⟨243311381797831374308317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5190642811687069318577429 243311381797831374308317)
                  ·
                    rfl

theorem cell23_4264625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_4264625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264625 prefixEnd_4264625 := by exact prefixLift 4264625
  have htrace : WordTrace (prefixWord ++ tailWord_4264625) baseStart_4264625 baseEnd_4264625 := by
    simpa [prefixWord, tailWord_4264625, baseEnd_4264625] using wordTrace_append hprefix tailTrace_4264625
  have hstable : (prefixWord ++ tailWord_4264625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264625).length < 2 ^ (prefixWord ++ tailWord_4264625).sum := by decide
  have hdescent : baseEnd_4264625 < baseStart_4264625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264634 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_4264634 : Nat := 118140960795 + 4264634 * 2 ^ 59
def prefixEnd_4264634 : Nat := 4983230072969 + 3 ^ 40 * 4264634 * 2
def baseEnd_4264634 : Nat := 729935685835457611187437

theorem tailTrace_4264634 : CollatzResearch.WordTrace tailWord_4264634 prefixEnd_4264634 729935685835457611187437 := by
  unfold tailWord_4264634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38885995107991708586520239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103695986954644556230720637 38885995107991708586520239)
  ·
    refine ⟨58328992661987562879780359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38885995107991708586520239 58328992661987562879780359)
    ·
      refine ⟨87493488992981344319670539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58328992661987562879780359 87493488992981344319670539)
      ·
        refine ⟨131240233489472016479505809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87493488992981344319670539 131240233489472016479505809)
        ·
          refine ⟨98430175117104012359629357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131240233489472016479505809 98430175117104012359629357)
          ·
            refine ⟨36911315668914004634861009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98430175117104012359629357 36911315668914004634861009)
            ·
              refine ⟨27683486751685503476145757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36911315668914004634861009 27683486751685503476145757)
              ·
                refine ⟨10381307531882063803554659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27683486751685503476145757 10381307531882063803554659)
                ·
                  refine ⟨15571961297823095705331989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10381307531882063803554659 15571961297823095705331989)
                  ·
                    refine ⟨729935685835457611187437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15571961297823095705331989 729935685835457611187437)
                    ·
                      rfl

theorem cell23_4264634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_4264634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264634 prefixEnd_4264634 := by exact prefixLift 4264634
  have htrace : WordTrace (prefixWord ++ tailWord_4264634) baseStart_4264634 baseEnd_4264634 := by
    simpa [prefixWord, tailWord_4264634, baseEnd_4264634] using wordTrace_append hprefix tailTrace_4264634
  have hstable : (prefixWord ++ tailWord_4264634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264634).length < 2 ^ (prefixWord ++ tailWord_4264634).sum := by decide
  have hdescent : baseEnd_4264634 < baseStart_4264634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264691 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 3]
def baseStart_4264691 : Nat := 118140960795 + 4264691 * 2 ^ 59
def prefixEnd_4264691 : Nat := 4983230072969 + 3 ^ 40 * 4264691 * 2
def baseEnd_4264691 : Nat := 2189836325903679110549549

theorem tailTrace_4264691 : CollatzResearch.WordTrace tailWord_4264691 prefixEnd_4264691 2189836325903679110549549 := by
  unfold tailWord_4264691
  simp only [CollatzResearch.WordTrace]
  refine ⟨155546059392760333080905927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103697372928506888720603951 155546059392760333080905927)
  ·
    refine ⟨233319089089140499621358891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155546059392760333080905927 233319089089140499621358891)
    ·
      refine ⟨349978633633710749432038337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233319089089140499621358891 349978633633710749432038337)
      ·
        refine ⟨262483975225283062074028753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349978633633710749432038337 262483975225283062074028753)
        ·
          refine ⟨196862981418962296555521565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262483975225283062074028753 196862981418962296555521565)
          ·
            refine ⟨73823618032110861208320587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196862981418962296555521565 73823618032110861208320587)
            ·
              refine ⟨110735427048166291812480881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73823618032110861208320587 110735427048166291812480881)
              ·
                refine ⟨83051570286124718859360661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110735427048166291812480881 83051570286124718859360661)
                ·
                  refine ⟨3893042357162096196532531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83051570286124718859360661 3893042357162096196532531)
                  ·
                    refine ⟨5839563535743144294798797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893042357162096196532531 5839563535743144294798797)
                    ·
                      refine ⟨2189836325903679110549549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839563535743144294798797 2189836325903679110549549)
                      ·
                        rfl

theorem cell23_4264691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_4264691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264691 prefixEnd_4264691 := by exact prefixLift 4264691
  have htrace : WordTrace (prefixWord ++ tailWord_4264691) baseStart_4264691 baseEnd_4264691 := by
    simpa [prefixWord, tailWord_4264691, baseEnd_4264691] using wordTrace_append hprefix tailTrace_4264691
  have hstable : (prefixWord ++ tailWord_4264691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264691).length < 2 ^ (prefixWord ++ tailWord_4264691).sum := by decide
  have hdescent : baseEnd_4264691 < baseStart_4264691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264708 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_4264708 : Nat := 118140960795 + 4264708 * 2 ^ 59
def prefixEnd_4264708 : Nat := 4983230072969 + 3 ^ 40 * 4264708 * 2
def baseEnd_4264708 : Nat := 2189845055074805544036971

theorem tailTrace_4264708 : CollatzResearch.WordTrace tailWord_4264708 prefixEnd_4264708 2189845055074805544036971 := by
  unfold tailWord_4264708
  simp only [CollatzResearch.WordTrace]
  refine ⟨77773339716849372492137389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103697786289132496656183185 77773339716849372492137389)
  ·
    refine ⟨29165002393818514684551521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77773339716849372492137389 29165002393818514684551521)
    ·
      refine ⟨21873751795363886013413641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29165002393818514684551521 21873751795363886013413641)
      ·
        refine ⟨16405313846522914510060231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21873751795363886013413641 16405313846522914510060231)
        ·
          refine ⟨24607970769784371765090347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16405313846522914510060231 24607970769784371765090347)
          ·
            refine ⟨36911956154676557647635521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24607970769784371765090347 36911956154676557647635521)
            ·
              refine ⟨27683967116007418235726641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36911956154676557647635521 27683967116007418235726641)
              ·
                refine ⟨20762975337005563676794981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27683967116007418235726641 20762975337005563676794981)
                ·
                  refine ⟨3893057875688543189399059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20762975337005563676794981 3893057875688543189399059)
                  ·
                    refine ⟨5839586813532814784098589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893057875688543189399059 5839586813532814784098589)
                    ·
                      refine ⟨2189845055074805544036971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839586813532814784098589 2189845055074805544036971)
                      ·
                        rfl

theorem cell23_4264708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_4264708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264708 prefixEnd_4264708 := by exact prefixLift 4264708
  have htrace : WordTrace (prefixWord ++ tailWord_4264708) baseStart_4264708 baseEnd_4264708 := by
    simpa [prefixWord, tailWord_4264708, baseEnd_4264708] using wordTrace_append hprefix tailTrace_4264708
  have hstable : (prefixWord ++ tailWord_4264708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264708).length < 2 ^ (prefixWord ++ tailWord_4264708).sum := by decide
  have hdescent : baseEnd_4264708 < baseStart_4264708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264865 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_4264865 : Nat := 118140960795 + 4264865 * 2 ^ 59
def prefixEnd_4264865 : Nat := 4983230072969 + 3 ^ 40 * 4264865 * 2
def baseEnd_4264865 : Nat := 729975223845853809924583

theorem tailTrace_4264865 : CollatzResearch.WordTrace tailWord_4264865 prefixEnd_4264865 729975223845853809924583 := by
  unfold tailWord_4264865
  simp only [CollatzResearch.WordTrace]
  refine ⟨155552405694129960797740049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103701603796086640531826699 155552405694129960797740049)
  ·
    refine ⟨116664304270597470598305037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155552405694129960797740049 116664304270597470598305037)
    ·
      refine ⟨43749114101474051474364389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116664304270597470598305037 43749114101474051474364389)
      ·
        refine ⟨8202958894026384651443323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43749114101474051474364389 8202958894026384651443323)
        ·
          refine ⟨12304438341039576977164985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202958894026384651443323 12304438341039576977164985)
          ·
            refine ⟨9228328755779682732873739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12304438341039576977164985 9228328755779682732873739)
            ·
              refine ⟨13842493133669524099310609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9228328755779682732873739 13842493133669524099310609)
              ·
                refine ⟨10381869850252143074482957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13842493133669524099310609 10381869850252143074482957)
                ·
                  refine ⟨3893201193844553652931109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10381869850252143074482957 3893201193844553652931109)
                  ·
                    refine ⟨729975223845853809924583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893201193844553652931109 729975223845853809924583)
                    ·
                      rfl

theorem cell23_4264865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_4264865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264865 prefixEnd_4264865 := by exact prefixLift 4264865
  have htrace : WordTrace (prefixWord ++ tailWord_4264865) baseStart_4264865 baseEnd_4264865 := by
    simpa [prefixWord, tailWord_4264865, baseEnd_4264865] using wordTrace_append hprefix tailTrace_4264865
  have hstable : (prefixWord ++ tailWord_4264865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264865).length < 2 ^ (prefixWord ++ tailWord_4264865).sum := by decide
  have hdescent : baseEnd_4264865 < baseStart_4264865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264925 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4264925 : Nat := 118140960795 + 4264925 * 2 ^ 59
def prefixEnd_4264925 : Nat := 4983230072969 + 3 ^ 40 * 4264925 * 2
def baseEnd_4264925 : Nat := 729985493458943731674491

theorem tailTrace_4264925 : CollatzResearch.WordTrace tailWord_4264925 prefixEnd_4264925 729985493458943731674491 := by
  unfold tailWord_4264925
  simp only [CollatzResearch.WordTrace]
  refine ⟨155554594073912591044924229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103703062715941727363282819 155554594073912591044924229)
  ·
    refine ⟨29166486388858610820923293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155554594073912591044924229 29166486388858610820923293)
    ·
      refine ⟨10937432395821979057846235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29166486388858610820923293 10937432395821979057846235)
      ·
        refine ⟨16406148593732968586769353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10937432395821979057846235 16406148593732968586769353)
        ·
          refine ⟨12304611445299726440077015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16406148593732968586769353 12304611445299726440077015)
          ·
            refine ⟨18456917167949589660115523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12304611445299726440077015 18456917167949589660115523)
            ·
              refine ⟨27685375751924384490173285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18456917167949589660115523 27685375751924384490173285)
              ·
                refine ⟨5191007953485822091907491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27685375751924384490173285 5191007953485822091907491)
                ·
                  refine ⟨7786511930228733137861237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191007953485822091907491 7786511930228733137861237)
                  ·
                    refine ⟨729985493458943731674491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7786511930228733137861237 729985493458943731674491)
                    ·
                      rfl

theorem cell23_4264925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4264925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264925 prefixEnd_4264925 := by exact prefixLift 4264925
  have htrace : WordTrace (prefixWord ++ tailWord_4264925) baseStart_4264925 baseEnd_4264925 := by
    simpa [prefixWord, tailWord_4264925, baseEnd_4264925] using wordTrace_append hprefix tailTrace_4264925
  have hstable : (prefixWord ++ tailWord_4264925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264925).length < 2 ^ (prefixWord ++ tailWord_4264925).sum := by decide
  have hdescent : baseEnd_4264925 < baseStart_4264925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264945 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_4264945 : Nat := 118140960795 + 4264945 * 2 ^ 59
def prefixEnd_4264945 : Nat := 4983230072969 + 3 ^ 40 * 4264945 * 2
def baseEnd_4264945 : Nat := 2189966749989921116773381

theorem tailTrace_4264945 : CollatzResearch.WordTrace tailWord_4264945 prefixEnd_4264945 2189966749989921116773381 := by
  unfold tailWord_4264945
  simp only [CollatzResearch.WordTrace]
  refine ⟨155555323533840134460652289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103703549022560089640434859 155555323533840134460652289)
  ·
    refine ⟨116666492650380100845489217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155555323533840134460652289 116666492650380100845489217)
    ·
      refine ⟨87499869487785075634116913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116666492650380100845489217 87499869487785075634116913)
      ·
        refine ⟨65624902115838806725587685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87499869487785075634116913 65624902115838806725587685)
        ·
          refine ⟨12304669146719776261047691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65624902115838806725587685 12304669146719776261047691)
          ·
            refine ⟨18457003720079664391571537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12304669146719776261047691 18457003720079664391571537)
            ·
              refine ⟨13842752790059748293678653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18457003720079664391571537 13842752790059748293678653)
              ·
                refine ⟨5191032296272405610129495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13842752790059748293678653 5191032296272405610129495)
                ·
                  refine ⟨7786548444408608415194243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191032296272405610129495 7786548444408608415194243)
                  ·
                    refine ⟨11679822666612912622791365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7786548444408608415194243 11679822666612912622791365)
                    ·
                      refine ⟨2189966749989921116773381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11679822666612912622791365 2189966749989921116773381)
                      ·
                        rfl

theorem cell23_4264945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_4264945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264945 prefixEnd_4264945 := by exact prefixLift 4264945
  have htrace : WordTrace (prefixWord ++ tailWord_4264945) baseStart_4264945 baseEnd_4264945 := by
    simpa [prefixWord, tailWord_4264945, baseEnd_4264945] using wordTrace_append hprefix tailTrace_4264945
  have hstable : (prefixWord ++ tailWord_4264945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264945).length < 2 ^ (prefixWord ++ tailWord_4264945).sum := by decide
  have hdescent : baseEnd_4264945 < baseStart_4264945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264968 : List Nat := [2, 1, 3, 2, 1, 4, 2, 8]
def baseStart_4264968 : Nat := 118140960795 + 4264968 * 2 ^ 59
def prefixEnd_4264968 : Nat := 4983230072969 + 3 ^ 40 * 4264968 * 2
def baseEnd_4264968 : Nat := 81110317038702760251325

theorem tailTrace_4264968 : CollatzResearch.WordTrace tailWord_4264968 prefixEnd_4264968 81110317038702760251325 := by
  unfold tailWord_4264968
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778081206378404694369779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103704108275171206259159705 77778081206378404694369779)
  ·
    refine ⟨116667121809567607041554669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77778081206378404694369779 116667121809567607041554669)
    ·
      refine ⟨43750170678587852640583001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116667121809567607041554669 43750170678587852640583001)
      ·
        refine ⟨32812628008940889480437251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43750170678587852640583001 32812628008940889480437251)
        ·
          refine ⟨49218942013411334220655877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32812628008940889480437251 49218942013411334220655877)
          ·
            refine ⟨9228551627514625166372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49218942013411334220655877 9228551627514625166372977)
            ·
              refine ⟨6921413720635968874779733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9228551627514625166372977 6921413720635968874779733)
              ·
                refine ⟨81110317038702760251325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6921413720635968874779733 81110317038702760251325)
                ·
                  rfl

theorem cell23_4264968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 8].length) (baseStart_4264968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264968 prefixEnd_4264968 := by exact prefixLift 4264968
  have htrace : WordTrace (prefixWord ++ tailWord_4264968) baseStart_4264968 baseEnd_4264968 := by
    simpa [prefixWord, tailWord_4264968, baseEnd_4264968] using wordTrace_append hprefix tailTrace_4264968
  have hstable : (prefixWord ++ tailWord_4264968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264968).length < 2 ^ (prefixWord ++ tailWord_4264968).sum := by decide
  have hdescent : baseEnd_4264968 < baseStart_4264968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264972 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_4264972 : Nat := 118140960795 + 4264972 * 2 ^ 59
def prefixEnd_4264972 : Nat := 4983230072969 + 3 ^ 40 * 4264972 * 2
def baseEnd_4264972 : Nat := 729993537989197503711919

theorem tailTrace_4264972 : CollatzResearch.WordTrace tailWord_4264972 prefixEnd_4264972 729993537989197503711919 := by
  unfold tailWord_4264972
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778154152371159035942585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103704205536494878714590113 77778154152371159035942585)
  ·
    refine ⟨58333615614278369276956939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77778154152371159035942585 58333615614278369276956939)
    ·
      refine ⟨87500423421417553915435409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58333615614278369276956939 87500423421417553915435409)
      ·
        refine ⟨65625317566063165436576557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87500423421417553915435409 65625317566063165436576557)
        ·
          refine ⟨24609494087273687038716209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65625317566063165436576557 24609494087273687038716209)
          ·
            refine ⟨18457120565455265279037157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24609494087273687038716209 18457120565455265279037157)
            ·
              refine ⟨3460710106022862239819467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18457120565455265279037157 3460710106022862239819467)
              ·
                refine ⟨5191065159034293359729201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460710106022862239819467 5191065159034293359729201)
                ·
                  refine ⟨3893298869275720019796901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191065159034293359729201 3893298869275720019796901)
                  ·
                    refine ⟨729993537989197503711919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893298869275720019796901 729993537989197503711919)
                    ·
                      rfl

theorem cell23_4264972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_4264972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264972 prefixEnd_4264972 := by exact prefixLift 4264972
  have htrace : WordTrace (prefixWord ++ tailWord_4264972) baseStart_4264972 baseEnd_4264972 := by
    simpa [prefixWord, tailWord_4264972, baseEnd_4264972] using wordTrace_append hprefix tailTrace_4264972
  have hstable : (prefixWord ++ tailWord_4264972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264972).length < 2 ^ (prefixWord ++ tailWord_4264972).sum := by decide
  have hdescent : baseEnd_4264972 < baseStart_4264972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264992 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4264992 : Nat := 118140960795 + 4264992 * 2 ^ 59
def prefixEnd_4264992 : Nat := 4983230072969 + 3 ^ 40 * 4264992 * 2
def baseEnd_4264992 : Nat := 2189990883580682432885665

theorem tailTrace_4264992 : CollatzResearch.WordTrace tailWord_4264992 prefixEnd_4264992 2189990883580682432885665 := by
  unfold tailWord_4264992
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778518882334930743806615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103704691843113240991742153 77778518882334930743806615)
  ·
    refine ⟨116667778323502396115709923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77778518882334930743806615 116667778323502396115709923)
    ·
      refine ⟨175001667485253594173564885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116667778323502396115709923 175001667485253594173564885)
      ·
        refine ⟨4101601581685631113442927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 175001667485253594173564885 4101601581685631113442927)
        ·
          refine ⟨6152402372528446670164391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101601581685631113442927 6152402372528446670164391)
          ·
            refine ⟨9228603558792670005246587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152402372528446670164391 9228603558792670005246587)
            ·
              refine ⟨13842905338189005007869881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9228603558792670005246587 13842905338189005007869881)
              ·
                refine ⟨10382179003641753755902411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13842905338189005007869881 10382179003641753755902411)
                ·
                  refine ⟨15573268505462630633853617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382179003641753755902411 15573268505462630633853617)
                  ·
                    refine ⟨11679951379096972975390213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15573268505462630633853617 11679951379096972975390213)
                    ·
                      refine ⟨2189990883580682432885665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11679951379096972975390213 2189990883580682432885665)
                      ·
                        rfl

theorem cell23_4264992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4264992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264992 prefixEnd_4264992 := by exact prefixLift 4264992
  have htrace : WordTrace (prefixWord ++ tailWord_4264992) baseStart_4264992 baseEnd_4264992 := by
    simpa [prefixWord, tailWord_4264992, baseEnd_4264992] using wordTrace_append hprefix tailTrace_4264992
  have hstable : (prefixWord ++ tailWord_4264992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264992).length < 2 ^ (prefixWord ++ tailWord_4264992).sum := by decide
  have hdescent : baseEnd_4264992 < baseStart_4264992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4264995 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3]
def baseStart_4264995 : Nat := 118140960795 + 4264995 * 2 ^ 59
def prefixEnd_4264995 : Nat := 4983230072969 + 3 ^ 40 * 4264995 * 2
def baseEnd_4264995 : Nat := 2189992424022645921148151

theorem tailTrace_4264995 : CollatzResearch.WordTrace tailWord_4264995 prefixEnd_4264995 2189992424022645921148151 := by
  unfold tailWord_4264995
  simp only [CollatzResearch.WordTrace]
  refine ⟨155557147183658992999972439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103704764789105995333314959 155557147183658992999972439)
  ·
    refine ⟨233335720775488489499958659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155557147183658992999972439 233335720775488489499958659)
    ·
      refine ⟨350003581163232734249937989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233335720775488489499958659 350003581163232734249937989)
      ·
        refine ⟨65625671468106137671863373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 350003581163232734249937989 65625671468106137671863373)
        ·
          refine ⟨24609626800539801626948765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65625671468106137671863373 24609626800539801626948765)
          ·
            refine ⟨9228610050202425610105787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24609626800539801626948765 9228610050202425610105787)
            ·
              refine ⟨13842915075303638415158681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9228610050202425610105787 13842915075303638415158681)
              ·
                refine ⟨10382186306477728811369011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13842915075303638415158681 10382186306477728811369011)
                ·
                  refine ⟨15573279459716593217053517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382186306477728811369011 15573279459716593217053517)
                  ·
                    refine ⟨5839979797393722456395069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15573279459716593217053517 5839979797393722456395069)
                    ·
                      refine ⟨2189992424022645921148151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5839979797393722456395069 2189992424022645921148151)
                      ·
                        rfl

theorem cell23_4264995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_4264995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4264995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4264995 prefixEnd_4264995 := by exact prefixLift 4264995
  have htrace : WordTrace (prefixWord ++ tailWord_4264995) baseStart_4264995 baseEnd_4264995 := by
    simpa [prefixWord, tailWord_4264995, baseEnd_4264995] using wordTrace_append hprefix tailTrace_4264995
  have hstable : (prefixWord ++ tailWord_4264995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4264995).length < 2 ^ (prefixWord ++ tailWord_4264995).sum := by decide
  have hdescent : baseEnd_4264995 < baseStart_4264995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4264995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265018 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_4265018 : Nat := 118140960795 + 4265018 * 2 ^ 59
def prefixEnd_4265018 : Nat := 4983230072969 + 3 ^ 40 * 4265018 * 2
def baseEnd_4265018 : Nat := 2190004234077699331160545

theorem tailTrace_4265018 : CollatzResearch.WordTrace tailWord_4265018 prefixEnd_4265018 2190004234077699331160545 := by
  unfold tailWord_4265018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889496515643916982014927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103705324041717111952039805 38889496515643916982014927)
  ·
    refine ⟨58334244773465875473022391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38889496515643916982014927 58334244773465875473022391)
    ·
      refine ⟨87501367160198813209533587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58334244773465875473022391 87501367160198813209533587)
      ·
        refine ⟨131252050740298219814300381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87501367160198813209533587 131252050740298219814300381)
        ·
          refine ⟨49219519027611832430362643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131252050740298219814300381 49219519027611832430362643)
          ·
            refine ⟨73829278541417748645543965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49219519027611832430362643 73829278541417748645543965)
            ·
              refine ⟨27685979453031655742078987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73829278541417748645543965 27685979453031655742078987)
              ·
                refine ⟨41528969179547483613118481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27685979453031655742078987 41528969179547483613118481)
                ·
                  refine ⟨31146726884660612709838861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41528969179547483613118481 31146726884660612709838861)
                  ·
                    refine ⟨11680022581747729766189573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31146726884660612709838861 11680022581747729766189573)
                    ·
                      refine ⟨2190004234077699331160545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11680022581747729766189573 2190004234077699331160545)
                      ·
                        rfl

theorem cell23_4265018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_4265018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265018 prefixEnd_4265018 := by exact prefixLift 4265018
  have htrace : WordTrace (prefixWord ++ tailWord_4265018) baseStart_4265018 baseEnd_4265018 := by
    simpa [prefixWord, tailWord_4265018, baseEnd_4265018] using wordTrace_append hprefix tailTrace_4265018
  have hstable : (prefixWord ++ tailWord_4265018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265018).length < 2 ^ (prefixWord ++ tailWord_4265018).sum := by decide
  have hdescent : baseEnd_4265018 < baseStart_4265018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265048 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4265048 : Nat := 118140960795 + 4265048 * 2 ^ 59
def prefixEnd_4265048 : Nat := 4983230072969 + 3 ^ 40 * 4265048 * 2
def baseEnd_4265048 : Nat := 2190019638497334213785407

theorem tailTrace_4265048 : CollatzResearch.WordTrace tailWord_4265048 prefixEnd_4265048 2190019638497334213785407 := by
  unfold tailWord_4265048
  simp only [CollatzResearch.WordTrace]
  refine ⟨77779540126233491525825899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103706053501644655367767865 77779540126233491525825899)
  ·
    refine ⟨116669310189350237288738849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77779540126233491525825899 116669310189350237288738849)
    ·
      refine ⟨87501982642012677966554137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116669310189350237288738849 87501982642012677966554137)
      ·
        refine ⟨65626486981509508474915603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87501982642012677966554137 65626486981509508474915603)
        ·
          refine ⟨98439730472264262712373405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65626486981509508474915603 98439730472264262712373405)
          ·
            refine ⟨36914898927099098517140027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98439730472264262712373405 36914898927099098517140027)
            ·
              refine ⟨55372348390648647775710041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36914898927099098517140027 55372348390648647775710041)
              ·
                refine ⟨41529261292986485831782531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55372348390648647775710041 41529261292986485831782531)
                ·
                  refine ⟨62293891939479728747673797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41529261292986485831782531 62293891939479728747673797)
                  ·
                    refine ⟨11680104738652449140188837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62293891939479728747673797 11680104738652449140188837)
                    ·
                      refine ⟨2190019638497334213785407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11680104738652449140188837 2190019638497334213785407)
                      ·
                        rfl

theorem cell23_4265048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4265048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265048 prefixEnd_4265048 := by exact prefixLift 4265048
  have htrace : WordTrace (prefixWord ++ tailWord_4265048) baseStart_4265048 baseEnd_4265048 := by
    simpa [prefixWord, tailWord_4265048, baseEnd_4265048] using wordTrace_append hprefix tailTrace_4265048
  have hstable : (prefixWord ++ tailWord_4265048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265048).length < 2 ^ (prefixWord ++ tailWord_4265048).sum := by decide
  have hdescent : baseEnd_4265048 < baseStart_4265048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265052 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4265052 : Nat := 118140960795 + 4265052 * 2 ^ 59
def prefixEnd_4265052 : Nat := 4983230072969 + 3 ^ 40 * 4265052 * 2
def baseEnd_4265052 : Nat := 2190021692419952198135389

theorem tailTrace_4265052 : CollatzResearch.WordTrace tailWord_4265052 prefixEnd_4265052 2190021692419952198135389 := by
  unfold tailWord_4265052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77779613072226245867398705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103706150762968327823198273 77779613072226245867398705)
  ·
    refine ⟨58334709804169684400549029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77779613072226245867398705 58334709804169684400549029)
    ·
      refine ⟨10937758088281815825102943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58334709804169684400549029 10937758088281815825102943)
      ·
        refine ⟨16406637132422723737654415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10937758088281815825102943 16406637132422723737654415)
        ·
          refine ⟨24609955698634085606481623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16406637132422723737654415 24609955698634085606481623)
          ·
            refine ⟨36914933547951128409722435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24609955698634085606481623 36914933547951128409722435)
            ·
              refine ⟨55372400321926692614583653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36914933547951128409722435 55372400321926692614583653)
              ·
                refine ⟨10382325060361254865234435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55372400321926692614583653 10382325060361254865234435)
                ·
                  refine ⟨15573487590541882297851653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382325060361254865234435 15573487590541882297851653)
                  ·
                    refine ⟨2920028923226602930847185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15573487590541882297851653 2920028923226602930847185)
                    ·
                      refine ⟨2190021692419952198135389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920028923226602930847185 2190021692419952198135389)
                      ·
                        rfl

theorem cell23_4265052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4265052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265052 prefixEnd_4265052 := by exact prefixLift 4265052
  have htrace : WordTrace (prefixWord ++ tailWord_4265052) baseStart_4265052 baseEnd_4265052 := by
    simpa [prefixWord, tailWord_4265052, baseEnd_4265052] using wordTrace_append hprefix tailTrace_4265052
  have hstable : (prefixWord ++ tailWord_4265052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265052).length < 2 ^ (prefixWord ++ tailWord_4265052).sum := by decide
  have hdescent : baseEnd_4265052 < baseStart_4265052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265069 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4265069 : Nat := 118140960795 + 4265069 * 2 ^ 59
def prefixEnd_4265069 : Nat := 4983230072969 + 3 ^ 40 * 4265069 * 2
def baseEnd_4265069 : Nat := 2190030421591078631622811

theorem tailTrace_4265069 : CollatzResearch.WordTrace tailWord_4265069 prefixEnd_4265069 2190030421591078631622811 := by
  unfold tailWord_4265069
  simp only [CollatzResearch.WordTrace]
  refine ⟨155559846185390903638166261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103706564123593935758777507 155559846185390903638166261)
  ·
    refine ⟨14583735579880397216078087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155559846185390903638166261 14583735579880397216078087)
    ·
      refine ⟨21875603369820595824117131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14583735579880397216078087 21875603369820595824117131)
      ·
        refine ⟨32813405054730893736175697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21875603369820595824117131 32813405054730893736175697)
        ·
          refine ⟨24610053791048170302131773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32813405054730893736175697 24610053791048170302131773)
          ·
            refine ⟨9228770171643063863299415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24610053791048170302131773 9228770171643063863299415)
            ·
              refine ⟨13843155257464595794949123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9228770171643063863299415 13843155257464595794949123)
              ·
                refine ⟨20764732886196893692423685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13843155257464595794949123 20764732886196893692423685)
                ·
                  refine ⟨3893387416161917567329441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20764732886196893692423685 3893387416161917567329441)
                  ·
                    refine ⟨2920040562121438175497081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893387416161917567329441 2920040562121438175497081)
                    ·
                      refine ⟨2190030421591078631622811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920040562121438175497081 2190030421591078631622811)
                      ·
                        rfl

theorem cell23_4265069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4265069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265069 prefixEnd_4265069 := by exact prefixLift 4265069
  have htrace : WordTrace (prefixWord ++ tailWord_4265069) baseStart_4265069 baseEnd_4265069 := by
    simpa [prefixWord, tailWord_4265069, baseEnd_4265069] using wordTrace_append hprefix tailTrace_4265069
  have hstable : (prefixWord ++ tailWord_4265069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265069).length < 2 ^ (prefixWord ++ tailWord_4265069).sum := by decide
  have hdescent : baseEnd_4265069 < baseStart_4265069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265085 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_4265085 : Nat := 118140960795 + 4265085 * 2 ^ 59
def prefixEnd_4265085 : Nat := 4983230072969 + 3 ^ 40 * 4265085 * 2
def baseEnd_4265085 : Nat := 2190038637281550569022737

theorem tailTrace_4265085 : CollatzResearch.WordTrace tailWord_4265085 prefixEnd_4265085 2190038637281550569022737 := by
  unfold tailWord_4265085
  simp only [CollatzResearch.WordTrace]
  refine ⟨155560429753332938370748709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103706953168888625580499139 155560429753332938370748709)
  ·
    refine ⟨29167580578749925944515383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155560429753332938370748709 29167580578749925944515383)
    ·
      refine ⟨43751370868124888916773075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29167580578749925944515383 43751370868124888916773075)
      ·
        refine ⟨65627056302187333375159613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43751370868124888916773075 65627056302187333375159613)
        ·
          refine ⟨24610146113320250015684855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65627056302187333375159613 24610146113320250015684855)
          ·
            refine ⟨36915219169980375023527283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24610146113320250015684855 36915219169980375023527283)
            ·
              refine ⟨55372828754970562535290925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36915219169980375023527283 55372828754970562535290925)
              ·
                refine ⟨20764810783113960950734097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55372828754970562535290925 20764810783113960950734097)
                ·
                  refine ⟨15573608087335470713050573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20764810783113960950734097 15573608087335470713050573)
                  ·
                    refine ⟨5840103032750801517393965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15573608087335470713050573 5840103032750801517393965)
                    ·
                      refine ⟨2190038637281550569022737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840103032750801517393965 2190038637281550569022737)
                      ·
                        rfl

theorem cell23_4265085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_4265085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265085 prefixEnd_4265085 := by exact prefixLift 4265085
  have htrace : WordTrace (prefixWord ++ tailWord_4265085) baseStart_4265085 baseEnd_4265085 := by
    simpa [prefixWord, tailWord_4265085, baseEnd_4265085] using wordTrace_append hprefix tailTrace_4265085
  have hstable : (prefixWord ++ tailWord_4265085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265085).length < 2 ^ (prefixWord ++ tailWord_4265085).sum := by decide
  have hdescent : baseEnd_4265085 < baseStart_4265085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265088 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_4265088 : Nat := 118140960795 + 4265088 * 2 ^ 59
def prefixEnd_4265088 : Nat := 4983230072969 + 3 ^ 40 * 4265088 * 2
def baseEnd_4265088 : Nat := 730013392574504685761741

theorem tailTrace_4265088 : CollatzResearch.WordTrace tailWord_4265088 prefixEnd_4265088 730013392574504685761741 := by
  unfold tailWord_4265088
  simp only [CollatzResearch.WordTrace]
  refine ⟨77780269586161034941553959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103707026114881379922071945 77780269586161034941553959)
  ·
    refine ⟨116670404379241552412330939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77780269586161034941553959 116670404379241552412330939)
    ·
      refine ⟨175005606568862328618496409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116670404379241552412330939 175005606568862328618496409)
      ·
        refine ⟨131254204926646746463872307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175005606568862328618496409 131254204926646746463872307)
        ·
          refine ⟨196881307389970119695808461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131254204926646746463872307 196881307389970119695808461)
          ·
            refine ⟨73830490271238794885928173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196881307389970119695808461 73830490271238794885928173)
            ·
              refine ⟨27686433851714548082223065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73830490271238794885928173 27686433851714548082223065)
              ·
                refine ⟨20764825388785911061667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27686433851714548082223065 20764825388785911061667299)
                ·
                  refine ⟨31147238083178866592500949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20764825388785911061667299 31147238083178866592500949)
                  ·
                    refine ⟨730013392574504685761741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31147238083178866592500949 730013392574504685761741)
                    ·
                      rfl

theorem cell23_4265088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_4265088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265088 prefixEnd_4265088 := by exact prefixLift 4265088
  have htrace : WordTrace (prefixWord ++ tailWord_4265088) baseStart_4265088 baseEnd_4265088 := by
    simpa [prefixWord, tailWord_4265088, baseEnd_4265088] using wordTrace_append hprefix tailTrace_4265088
  have hstable : (prefixWord ++ tailWord_4265088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265088).length < 2 ^ (prefixWord ++ tailWord_4265088).sum := by decide
  have hdescent : baseEnd_4265088 < baseStart_4265088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265125 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_4265125 : Nat := 118140960795 + 4265125 * 2 ^ 59
def prefixEnd_4265125 : Nat := 4983230072969 + 3 ^ 40 * 4265125 * 2
def baseEnd_4265125 : Nat := 2190059176507730412522553

theorem tailTrace_4265125 : CollatzResearch.WordTrace tailWord_4265125 prefixEnd_4265125 2190059176507730412522553 := by
  unfold tailWord_4265125
  simp only [CollatzResearch.WordTrace]
  refine ⟨155561888673188025202204829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103707925782125350134803219 155561888673188025202204829)
  ·
    refine ⟨58335708252445509450826811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155561888673188025202204829 58335708252445509450826811)
    ·
      refine ⟨87503562378668264176240217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58335708252445509450826811 87503562378668264176240217)
      ·
        refine ⟨65627671784001198132180163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87503562378668264176240217 65627671784001198132180163)
        ·
          refine ⟨98441507676001797198270245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65627671784001198132180163 98441507676001797198270245)
          ·
            refine ⟨18457782689250336974675671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98441507676001797198270245 18457782689250336974675671)
            ·
              refine ⟨27686674033875505462013507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18457782689250336974675671 27686674033875505462013507)
              ·
                refine ⟨41530011050813258193020261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27686674033875505462013507 41530011050813258193020261)
                ·
                  refine ⟨7786877072027485911191299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41530011050813258193020261 7786877072027485911191299)
                  ·
                    refine ⟨11680315608041228866786949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7786877072027485911191299 11680315608041228866786949)
                    ·
                      refine ⟨2190059176507730412522553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11680315608041228866786949 2190059176507730412522553)
                      ·
                        rfl

theorem cell23_4265125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_4265125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265125 prefixEnd_4265125 := by exact prefixLift 4265125
  have htrace : WordTrace (prefixWord ++ tailWord_4265125) baseStart_4265125 baseEnd_4265125 := by
    simpa [prefixWord, tailWord_4265125, baseEnd_4265125] using wordTrace_append hprefix tailTrace_4265125
  have hstable : (prefixWord ++ tailWord_4265125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265125).length < 2 ^ (prefixWord ++ tailWord_4265125).sum := by decide
  have hdescent : baseEnd_4265125 < baseStart_4265125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265162 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_4265162 : Nat := 118140960795 + 4265162 * 2 ^ 59
def prefixEnd_4265162 : Nat := 4983230072969 + 3 ^ 40 * 4265162 * 2
def baseEnd_4265162 : Nat := 2190078175291946767759883

theorem tailTrace_4265162 : CollatzResearch.WordTrace tailWord_4265162 prefixEnd_4265162 2190078175291946767759883 := by
  unfold tailWord_4265162
  simp only [CollatzResearch.WordTrace]
  refine ⟨38890809543513495130325435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103708825449369320347534493 38890809543513495130325435)
  ·
    refine ⟨58336214315270242695488153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38890809543513495130325435 58336214315270242695488153)
    ·
      refine ⟨43752160736452682021616115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58336214315270242695488153 43752160736452682021616115)
      ·
        refine ⟨65628241104679023032424173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43752160736452682021616115 65628241104679023032424173)
        ·
          refine ⟨24610590414254633637159065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65628241104679023032424173 24610590414254633637159065)
          ·
            refine ⟨18457942810690975227869299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24610590414254633637159065 18457942810690975227869299)
            ·
              refine ⟨27686914216036462841803949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18457942810690975227869299 27686914216036462841803949)
              ·
                refine ⟨10382592831013673565676481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27686914216036462841803949 10382592831013673565676481)
                ·
                  refine ⟨7786944623260255174257361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10382592831013673565676481 7786944623260255174257361)
                  ·
                    refine ⟨5840208467445191380693021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7786944623260255174257361 5840208467445191380693021)
                    ·
                      refine ⟨2190078175291946767759883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840208467445191380693021 2190078175291946767759883)
                      ·
                        rfl

theorem cell23_4265162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_4265162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265162 prefixEnd_4265162 := by exact prefixLift 4265162
  have htrace : WordTrace (prefixWord ++ tailWord_4265162) baseStart_4265162 baseEnd_4265162 := by
    simpa [prefixWord, tailWord_4265162, baseEnd_4265162] using wordTrace_append hprefix tailTrace_4265162
  have hstable : (prefixWord ++ tailWord_4265162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265162).length < 2 ^ (prefixWord ++ tailWord_4265162).sum := by decide
  have hdescent : baseEnd_4265162 < baseStart_4265162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265195 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 3, 5]
def baseStart_4265195 : Nat := 118140960795 + 4265195 * 2 ^ 59
def prefixEnd_4265195 : Nat := 4983230072969 + 3 ^ 40 * 4265195 * 2
def baseEnd_4265195 : Nat := 730031706717848379549077

theorem tailTrace_4265195 : CollatzResearch.WordTrace tailWord_4265195 prefixEnd_4265195 730031706717848379549077 := by
  unfold tailWord_4265195
  simp only [CollatzResearch.WordTrace]
  refine ⟨155564441782934427157253039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103709627855289618104835359 155564441782934427157253039)
  ·
    refine ⟨233346662674401640735879559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155564441782934427157253039 233346662674401640735879559)
    ·
      refine ⟨350019994011602461103819339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233346662674401640735879559 350019994011602461103819339)
      ·
        refine ⟨525029991017403691655729009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350019994011602461103819339 525029991017403691655729009)
        ·
          refine ⟨393772493263052768741796757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525029991017403691655729009 393772493263052768741796757)
          ·
            refine ⟨18458085621705598534771723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 393772493263052768741796757 18458085621705598534771723)
            ·
              refine ⟨27687128432558397802157585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18458085621705598534771723 27687128432558397802157585)
              ·
                refine ⟨20765346324418798351618189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27687128432558397802157585 20765346324418798351618189)
                ·
                  refine ⟨7787004871657049381856821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20765346324418798351618189 7787004871657049381856821)
                  ·
                    refine ⟨730031706717848379549077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7787004871657049381856821 730031706717848379549077)
                    ·
                      rfl

theorem cell23_4265195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].length) (baseStart_4265195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265195 prefixEnd_4265195 := by exact prefixLift 4265195
  have htrace : WordTrace (prefixWord ++ tailWord_4265195) baseStart_4265195 baseEnd_4265195 := by
    simpa [prefixWord, tailWord_4265195, baseEnd_4265195] using wordTrace_append hprefix tailTrace_4265195
  have hstable : (prefixWord ++ tailWord_4265195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265195).length < 2 ^ (prefixWord ++ tailWord_4265195).sum := by decide
  have hdescent : baseEnd_4265195 < baseStart_4265195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265219 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 2, 3, 2]
def baseStart_4265219 : Nat := 118140960795 + 4265219 * 2 ^ 59
def prefixEnd_4265219 : Nat := 4983230072969 + 3 ^ 40 * 4265219 * 2
def baseEnd_4265219 : Nat := 2190107443689253044747121

theorem tailTrace_4265219 : CollatzResearch.WordTrace tailWord_4265219 prefixEnd_4265219 2190107443689253044747121 := by
  unfold tailWord_4265219
  simp only [CollatzResearch.WordTrace]
  refine ⟨155565317134847479256126711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103710211423231652837417807 155565317134847479256126711)
  ·
    refine ⟨233347975702271218884190067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155565317134847479256126711 233347975702271218884190067)
    ·
      refine ⟨350021963553406828326285101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233347975702271218884190067 350021963553406828326285101)
      ·
        refine ⟨131258236332527560622356913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350021963553406828326285101 131258236332527560622356913)
        ·
          refine ⟨98443677249395670466767685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131258236332527560622356913 98443677249395670466767685)
          ·
            refine ⟨18458189484261688212518941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98443677249395670466767685 18458189484261688212518941)
            ·
              refine ⟨6921821056598133079694603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18458189484261688212518941 6921821056598133079694603)
              ·
                refine ⟨10382731584897199619541905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6921821056598133079694603 10382731584897199619541905)
                ·
                  refine ⟨7787048688672899714656429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10382731584897199619541905 7787048688672899714656429)
                  ·
                    refine ⟨2920143258252337392996161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7787048688672899714656429 2920143258252337392996161)
                    ·
                      refine ⟨2190107443689253044747121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920143258252337392996161 2190107443689253044747121)
                      ·
                        rfl

theorem cell23_4265219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_4265219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265219 prefixEnd_4265219 := by exact prefixLift 4265219
  have htrace : WordTrace (prefixWord ++ tailWord_4265219) baseStart_4265219 baseEnd_4265219 := by
    simpa [prefixWord, tailWord_4265219, baseEnd_4265219] using wordTrace_append hprefix tailTrace_4265219
  have hstable : (prefixWord ++ tailWord_4265219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265219).length < 2 ^ (prefixWord ++ tailWord_4265219).sum := by decide
  have hdescent : baseEnd_4265219 < baseStart_4265219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265225 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_4265225 : Nat := 118140960795 + 4265225 * 2 ^ 59
def prefixEnd_4265225 : Nat := 4983230072969 + 3 ^ 40 * 4265225 * 2
def baseEnd_4265225 : Nat := 730036841524393340424031

theorem tailTrace_4265225 : CollatzResearch.WordTrace tailWord_4265225 prefixEnd_4265225 730036841524393340424031 := by
  unfold tailWord_4265225
  simp only [CollatzResearch.WordTrace]
  refine ⟨155565535972825742280845129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103710357315217161520563419 155565535972825742280845129)
  ·
    refine ⟨116674151979619306710633847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155565535972825742280845129 116674151979619306710633847)
    ·
      refine ⟨175011227969428960065950771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116674151979619306710633847 175011227969428960065950771)
      ·
        refine ⟨262516841954143440098926157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175011227969428960065950771 262516841954143440098926157)
        ·
          refine ⟨98443815732803790037097309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262516841954143440098926157 98443815732803790037097309)
          ·
            refine ⟨36916430899801421263911491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98443815732803790037097309 36916430899801421263911491)
            ·
              refine ⟨55374646349702131895867237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36916430899801421263911491 55374646349702131895867237)
              ·
                refine ⟨10382746190569149730475107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55374646349702131895867237 10382746190569149730475107)
                ·
                  refine ⟨15574119285853724595712661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382746190569149730475107 15574119285853724595712661)
                  ·
                    refine ⟨730036841524393340424031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15574119285853724595712661 730036841524393340424031)
                    ·
                      rfl

theorem cell23_4265225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_4265225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265225 prefixEnd_4265225 := by exact prefixLift 4265225
  have htrace : WordTrace (prefixWord ++ tailWord_4265225) baseStart_4265225 baseEnd_4265225 := by
    simpa [prefixWord, tailWord_4265225, baseEnd_4265225] using wordTrace_append hprefix tailTrace_4265225
  have hstable : (prefixWord ++ tailWord_4265225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265225).length < 2 ^ (prefixWord ++ tailWord_4265225).sum := by decide
  have hdescent : baseEnd_4265225 < baseStart_4265225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265252 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4265252 : Nat := 118140960795 + 4265252 * 2 ^ 59
def prefixEnd_4265252 : Nat := 4983230072969 + 3 ^ 40 * 4265252 * 2
def baseEnd_4265252 : Nat := 2190124388550851415634469

theorem tailTrace_4265252 : CollatzResearch.WordTrace tailWord_4265252 prefixEnd_4265252 2190124388550851415634469 := by
  unfold tailWord_4265252
  simp only [CollatzResearch.WordTrace]
  refine ⟨77783260371863962946039005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103711013829151950594718673 77783260371863962946039005)
  ·
    refine ⟨29168722639448986104764627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77783260371863962946039005 29168722639448986104764627)
    ·
      refine ⟨43753083959173479157146941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29168722639448986104764627 43753083959173479157146941)
      ·
        refine ⟨16407406484690054683930103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43753083959173479157146941 16407406484690054683930103)
        ·
          refine ⟨24611109727035082025895155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16407406484690054683930103 24611109727035082025895155)
          ·
            refine ⟨36916664590552623038842733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24611109727035082025895155 36916664590552623038842733)
            ·
              refine ⟨13843749221457233639566025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36916664590552623038842733 13843749221457233639566025)
              ·
                refine ⟨10382811916092925229674519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13843749221457233639566025 10382811916092925229674519)
                ·
                  refine ⟨15574217874139387844511779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382811916092925229674519 15574217874139387844511779)
                  ·
                    refine ⟨23361326811209081766767669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15574217874139387844511779 23361326811209081766767669)
                    ·
                      refine ⟨2190124388550851415634469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23361326811209081766767669 2190124388550851415634469)
                      ·
                        rfl

theorem cell23_4265252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4265252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265252 prefixEnd_4265252 := by exact prefixLift 4265252
  have htrace : WordTrace (prefixWord ++ tailWord_4265252) baseStart_4265252 baseEnd_4265252 := by
    simpa [prefixWord, tailWord_4265252, baseEnd_4265252] using wordTrace_append hprefix tailTrace_4265252
  have hstable : (prefixWord ++ tailWord_4265252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265252).length < 2 ^ (prefixWord ++ tailWord_4265252).sum := by decide
  have hdescent : baseEnd_4265252 < baseStart_4265252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265266 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_4265266 : Nat := 118140960795 + 4265266 * 2 ^ 59
def prefixEnd_4265266 : Nat := 4983230072969 + 3 ^ 40 * 4265266 * 2
def baseEnd_4265266 : Nat := 2190131577280014360859405

theorem tailTrace_4265266 : CollatzResearch.WordTrace tailWord_4265266 prefixEnd_4265266 2190131577280014360859405 := by
  unfold tailWord_4265266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891757841419301570771913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103711354243784804188725101 38891757841419301570771913)
  ·
    refine ⟨29168818381064476178078935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38891757841419301570771913 29168818381064476178078935)
    ·
      refine ⟨43753227571596714267118403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29168818381064476178078935 43753227571596714267118403)
      ·
        refine ⟨65629841357395071400677605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43753227571596714267118403 65629841357395071400677605)
        ·
          refine ⟨12305595254511575887627051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65629841357395071400677605 12305595254511575887627051)
          ·
            refine ⟨18458392881767363831440577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12305595254511575887627051 18458392881767363831440577)
            ·
              refine ⟨13843794661325522873580433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18458392881767363831440577 13843794661325522873580433)
              ·
                refine ⟨10382845995994142155185325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13843794661325522873580433 10382845995994142155185325)
                ·
                  refine ⟨3893567248497803308194497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10382845995994142155185325 3893567248497803308194497)
                  ·
                    refine ⟨2920175436373352481145873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893567248497803308194497 2920175436373352481145873)
                    ·
                      refine ⟨2190131577280014360859405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920175436373352481145873 2190131577280014360859405)
                      ·
                        rfl

theorem cell23_4265266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_4265266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265266 prefixEnd_4265266 := by exact prefixLift 4265266
  have htrace : WordTrace (prefixWord ++ tailWord_4265266) baseStart_4265266 baseEnd_4265266 := by
    simpa [prefixWord, tailWord_4265266, baseEnd_4265266] using wordTrace_append hprefix tailTrace_4265266
  have hstable : (prefixWord ++ tailWord_4265266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265266).length < 2 ^ (prefixWord ++ tailWord_4265266).sum := by decide
  have hdescent : baseEnd_4265266 < baseStart_4265266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265269 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_4265269 : Nat := 118140960795 + 4265269 * 2 ^ 59
def prefixEnd_4265269 : Nat := 4983230072969 + 3 ^ 40 * 4265269 * 2
def baseEnd_4265269 : Nat := 2190133117721977849121891

theorem tailTrace_4265269 : CollatzResearch.WordTrace tailWord_4265269 prefixEnd_4265269 2190133117721977849121891 := by
  unfold tailWord_4265269
  simp only [CollatzResearch.WordTrace]
  refine ⟨155567140784666337795446861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103711427189777558530297907 155567140784666337795446861)
  ·
    refine ⟨58337677794249876673292573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155567140784666337795446861 58337677794249876673292573)
    ·
      refine ⟨21876629172843703752484715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58337677794249876673292573 21876629172843703752484715)
      ·
        refine ⟨32814943759265555628727073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21876629172843703752484715 32814943759265555628727073)
        ·
          refine ⟨24611207819449166721545305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32814943759265555628727073 24611207819449166721545305)
          ·
            refine ⟨18458405864586875041158979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24611207819449166721545305 18458405864586875041158979)
            ·
              refine ⟨27687608796880312561738469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18458405864586875041158979 27687608796880312561738469)
              ·
                refine ⟨5191426649415058605325963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27687608796880312561738469 5191426649415058605325963)
                ·
                  refine ⟨7787139974122587907988945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191426649415058605325963 7787139974122587907988945)
                  ·
                    refine ⟨5840354980591940930991709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7787139974122587907988945 5840354980591940930991709)
                    ·
                      refine ⟨2190133117721977849121891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840354980591940930991709 2190133117721977849121891)
                      ·
                        rfl

theorem cell23_4265269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_4265269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265269 prefixEnd_4265269 := by exact prefixLift 4265269
  have htrace : WordTrace (prefixWord ++ tailWord_4265269) baseStart_4265269 baseEnd_4265269 := by
    simpa [prefixWord, tailWord_4265269, baseEnd_4265269] using wordTrace_append hprefix tailTrace_4265269
  have hstable : (prefixWord ++ tailWord_4265269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265269).length < 2 ^ (prefixWord ++ tailWord_4265269).sum := by decide
  have hdescent : baseEnd_4265269 < baseStart_4265269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265277 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4265277 : Nat := 118140960795 + 4265277 * 2 ^ 59
def prefixEnd_4265277 : Nat := 4983230072969 + 3 ^ 40 * 4265277 * 2
def baseEnd_4265277 : Nat := 2190137225567213817821855

theorem tailTrace_4265277 : CollatzResearch.WordTrace tailWord_4265277 prefixEnd_4265277 2190137225567213817821855 := by
  unfold tailWord_4265277
  simp only [CollatzResearch.WordTrace]
  refine ⟨155567432568637355161738085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103711621712424903441158723 155567432568637355161738085)
  ·
    refine ⟨29168893606619504092825891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155567432568637355161738085 29168893606619504092825891)
    ·
      refine ⟨43753340409929256139238837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29168893606619504092825891 43753340409929256139238837)
      ·
        refine ⟨4101875663430867763053641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43753340409929256139238837 4101875663430867763053641)
        ·
          refine ⟨3076406747573150822290231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4101875663430867763053641 3076406747573150822290231)
          ·
            refine ⟨4614610121359726233435347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076406747573150822290231 4614610121359726233435347)
            ·
              refine ⟨6921915182039589350153021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614610121359726233435347 6921915182039589350153021)
              ·
                refine ⟨2595718193264846006307383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6921915182039589350153021 2595718193264846006307383)
                ·
                  refine ⟨3893577289897269009461075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595718193264846006307383 3893577289897269009461075)
                  ·
                    refine ⟨5840365934845903514191613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893577289897269009461075 5840365934845903514191613)
                    ·
                      refine ⟨2190137225567213817821855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840365934845903514191613 2190137225567213817821855)
                      ·
                        rfl

theorem cell23_4265277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4265277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265277 prefixEnd_4265277 := by exact prefixLift 4265277
  have htrace : WordTrace (prefixWord ++ tailWord_4265277) baseStart_4265277 baseEnd_4265277 := by
    simpa [prefixWord, tailWord_4265277, baseEnd_4265277] using wordTrace_append hprefix tailTrace_4265277
  have hstable : (prefixWord ++ tailWord_4265277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265277).length < 2 ^ (prefixWord ++ tailWord_4265277).sum := by decide
  have hdescent : baseEnd_4265277 < baseStart_4265277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265299 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 3]
def baseStart_4265299 : Nat := 118140960795 + 4265299 * 2 ^ 59
def prefixEnd_4265299 : Nat := 4983230072969 + 3 ^ 40 * 4265299 * 2
def baseEnd_4265299 : Nat := 2190148522141612731746753

theorem tailTrace_4265299 : CollatzResearch.WordTrace tailWord_4265299 prefixEnd_4265299 2190148522141612731746753 := by
  unfold tailWord_4265299
  simp only [CollatzResearch.WordTrace]
  refine ⟨155568234974557652919038951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103712156649705101946025967 155568234974557652919038951)
  ·
    refine ⟨233352352461836479378558427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155568234974557652919038951 233352352461836479378558427)
    ·
      refine ⟨350028528692754719067837641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233352352461836479378558427 350028528692754719067837641)
      ·
        refine ⟨262521396519566039300878231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350028528692754719067837641 262521396519566039300878231)
        ·
          refine ⟨393782094779349058951317347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262521396519566039300878231 393782094779349058951317347)
          ·
            refine ⟨590673142169023588426976021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393782094779349058951317347 590673142169023588426976021)
            ·
              refine ⟨27687803539172980707514501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 590673142169023588426976021 27687803539172980707514501)
              ·
                refine ⟨5191463163594933882658969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27687803539172980707514501 5191463163594933882658969)
                ·
                  refine ⟨3893597372696200411994227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191463163594933882658969 3893597372696200411994227)
                  ·
                    refine ⟨5840396059044300617991341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893597372696200411994227 5840396059044300617991341)
                    ·
                      refine ⟨2190148522141612731746753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840396059044300617991341 2190148522141612731746753)
                      ·
                        rfl

theorem cell23_4265299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_4265299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265299 prefixEnd_4265299 := by exact prefixLift 4265299
  have htrace : WordTrace (prefixWord ++ tailWord_4265299) baseStart_4265299 baseEnd_4265299 := by
    simpa [prefixWord, tailWord_4265299, baseEnd_4265299] using wordTrace_append hprefix tailTrace_4265299
  have hstable : (prefixWord ++ tailWord_4265299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265299).length < 2 ^ (prefixWord ++ tailWord_4265299).sum := by decide
  have hdescent : baseEnd_4265299 < baseStart_4265299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265300 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_4265300 : Nat := 118140960795 + 4265300 * 2 ^ 59
def prefixEnd_4265300 : Nat := 4983230072969 + 3 ^ 40 * 4265300 * 2
def baseEnd_4265300 : Nat := 2190149035622267227834249

theorem tailTrace_4265300 : CollatzResearch.WordTrace tailWord_4265300 prefixEnd_4265300 2190149035622267227834249 := by
  unfold tailWord_4265300
  simp only [CollatzResearch.WordTrace]
  refine ⟨77784135723777015044912677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103712180965036020059883569 77784135723777015044912677)
  ·
    refine ⟨14584525448208190320921127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77784135723777015044912677 14584525448208190320921127)
    ·
      refine ⟨21876788172312285481381691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14584525448208190320921127 21876788172312285481381691)
      ·
        refine ⟨32815182258468428222072537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21876788172312285481381691 32815182258468428222072537)
        ·
          refine ⟨24611386693851321166554403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32815182258468428222072537 24611386693851321166554403)
          ·
            refine ⟨36917080040776981749831605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24611386693851321166554403 36917080040776981749831605)
            ·
              refine ⟨3460976253822842039046713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36917080040776981749831605 3460976253822842039046713)
              ·
                refine ⟨2595732190367131529285035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460976253822842039046713 2595732190367131529285035)
                ·
                  refine ⟨3893598285550697293927553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595732190367131529285035 3893598285550697293927553)
                  ·
                    refine ⟨2920198714163022970445665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893598285550697293927553 2920198714163022970445665)
                    ·
                      refine ⟨2190149035622267227834249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920198714163022970445665 2190149035622267227834249)
                      ·
                        rfl

theorem cell23_4265300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_4265300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265300 prefixEnd_4265300 := by exact prefixLift 4265300
  have htrace : WordTrace (prefixWord ++ tailWord_4265300) baseStart_4265300 baseEnd_4265300 := by
    simpa [prefixWord, tailWord_4265300, baseEnd_4265300] using wordTrace_append hprefix tailTrace_4265300
  have hstable : (prefixWord ++ tailWord_4265300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265300).length < 2 ^ (prefixWord ++ tailWord_4265300).sum := by decide
  have hdescent : baseEnd_4265300 < baseStart_4265300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265316 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_4265316 : Nat := 118140960795 + 4265316 * 2 ^ 59
def prefixEnd_4265316 : Nat := 4983230072969 + 3 ^ 40 * 4265316 * 2
def baseEnd_4265316 : Nat := 2190157251312739165234175

theorem tailTrace_4265316 : CollatzResearch.WordTrace tailWord_4265316 prefixEnd_4265316 2190157251312739165234175 := by
  unfold tailWord_4265316
  simp only [CollatzResearch.WordTrace]
  refine ⟨77784427507748032411203901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103712570010330709881605201 77784427507748032411203901)
  ·
    refine ⟨29169160315405512154201463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77784427507748032411203901 29169160315405512154201463)
    ·
      refine ⟨43753740473108268231302195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29169160315405512154201463 43753740473108268231302195)
      ·
        refine ⟨65630610709662402346953293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43753740473108268231302195 65630610709662402346953293)
        ·
          refine ⟨24611479016123400880107485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65630610709662402346953293 24611479016123400880107485)
          ·
            refine ⟨9229304631046275330040307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24611479016123400880107485 9229304631046275330040307)
            ·
              refine ⟨13843956946569412995060461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9229304631046275330040307 13843956946569412995060461)
              ·
                refine ⟨5191483854963529873147673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13843956946569412995060461 5191483854963529873147673)
                ·
                  refine ⟨3893612891222647404860755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191483854963529873147673 3893612891222647404860755)
                  ·
                    refine ⟨5840419336833971107291133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893612891222647404860755 5840419336833971107291133)
                    ·
                      refine ⟨2190157251312739165234175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840419336833971107291133 2190157251312739165234175)
                      ·
                        rfl

theorem cell23_4265316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_4265316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265316 prefixEnd_4265316 := by exact prefixLift 4265316
  have htrace : WordTrace (prefixWord ++ tailWord_4265316) baseStart_4265316 baseEnd_4265316 := by
    simpa [prefixWord, tailWord_4265316, baseEnd_4265316] using wordTrace_append hprefix tailTrace_4265316
  have hstable : (prefixWord ++ tailWord_4265316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265316).length < 2 ^ (prefixWord ++ tailWord_4265316).sum := by decide
  have hdescent : baseEnd_4265316 < baseStart_4265316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265339 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 4, 2]
def baseStart_4265339 : Nat := 118140960795 + 4265339 * 2 ^ 59
def prefixEnd_4265339 : Nat := 4983230072969 + 3 ^ 40 * 4265339 * 2
def baseEnd_4265339 : Nat := 2190169061367792575246569

theorem tailTrace_4265339 : CollatzResearch.WordTrace tailWord_4265339 prefixEnd_4265339 2190169061367792575246569 := by
  unfold tailWord_4265339
  simp only [CollatzResearch.WordTrace]
  refine ⟨155569693894412739750495071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103713129262941826500330047 155569693894412739750495071)
  ·
    refine ⟨233354540841619109625742607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155569693894412739750495071 233354540841619109625742607)
    ·
      refine ⟨350031811262428664438613911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233354540841619109625742607 350031811262428664438613911)
      ·
        refine ⟨525047716893642996657920867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350031811262428664438613911 525047716893642996657920867)
        ·
          refine ⟨787571575340464494986881301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525047716893642996657920867 787571575340464494986881301)
          ·
            refine ⟨36917417594084273202510061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 787571575340464494986881301 36917417594084273202510061)
            ·
              refine ⟨13844031597781602450941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36917417594084273202510061 13844031597781602450941273)
              ·
                refine ⟨10383023698336201838205955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13844031597781602450941273 10383023698336201838205955)
                ·
                  refine ⟨15574535547504302757308933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10383023698336201838205955 15574535547504302757308933)
                  ·
                    refine ⟨2920225415157056766995425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15574535547504302757308933 2920225415157056766995425)
                    ·
                      refine ⟨2190169061367792575246569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920225415157056766995425 2190169061367792575246569)
                      ·
                        rfl

theorem cell23_4265339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4, 2].length) (baseStart_4265339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265339 prefixEnd_4265339 := by exact prefixLift 4265339
  have htrace : WordTrace (prefixWord ++ tailWord_4265339) baseStart_4265339 baseEnd_4265339 := by
    simpa [prefixWord, tailWord_4265339, baseEnd_4265339] using wordTrace_append hprefix tailTrace_4265339
  have hstable : (prefixWord ++ tailWord_4265339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265339).length < 2 ^ (prefixWord ++ tailWord_4265339).sum := by decide
  have hdescent : baseEnd_4265339 < baseStart_4265339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265373 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_4265373 : Nat := 118140960795 + 4265373 * 2 ^ 59
def prefixEnd_4265373 : Nat := 4983230072969 + 3 ^ 40 * 4265373 * 2
def baseEnd_4265373 : Nat := 2190186519710045442221413

theorem tailTrace_4265373 : CollatzResearch.WordTrace tailWord_4265373 prefixEnd_4265373 2190186519710045442221413 := by
  unfold tailWord_4265373
  simp only [CollatzResearch.WordTrace]
  refine ⟨155570933976289563557232773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103713955984193042371488515 155570933976289563557232773)
  ·
    refine ⟨29169550120554293166981145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155570933976289563557232773 29169550120554293166981145)
    ·
      refine ⟨21877162590415719875235859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29169550120554293166981145 21877162590415719875235859)
      ·
        refine ⟨32815743885623579812853789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21877162590415719875235859 32815743885623579812853789)
        ·
          refine ⟨12305903957108842429820171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32815743885623579812853789 12305903957108842429820171)
          ·
            refine ⟨18458855935663263644730257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12305903957108842429820171 18458855935663263644730257)
            ·
              refine ⟨13844141951747447733547693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18458855935663263644730257 13844141951747447733547693)
              ·
                refine ⟨5191553231905292900080385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13844141951747447733547693 5191553231905292900080385)
                ·
                  refine ⟨3893664923928969675060289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191553231905292900080385 3893664923928969675060289)
                  ·
                    refine ⟨2920248692946727256295217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893664923928969675060289 2920248692946727256295217)
                    ·
                      refine ⟨2190186519710045442221413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920248692946727256295217 2190186519710045442221413)
                      ·
                        rfl

theorem cell23_4265373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_4265373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265373 prefixEnd_4265373 := by exact prefixLift 4265373
  have htrace : WordTrace (prefixWord ++ tailWord_4265373) baseStart_4265373 baseEnd_4265373 := by
    simpa [prefixWord, tailWord_4265373, baseEnd_4265373] using wordTrace_append hprefix tailTrace_4265373
  have hstable : (prefixWord ++ tailWord_4265373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265373).length < 2 ^ (prefixWord ++ tailWord_4265373).sum := by decide
  have hdescent : baseEnd_4265373 < baseStart_4265373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265392 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_4265392 : Nat := 118140960795 + 4265392 * 2 ^ 59
def prefixEnd_4265392 : Nat := 4983230072969 + 3 ^ 40 * 4265392 * 2
def baseEnd_4265392 : Nat := 730065425280826955961275

theorem tailTrace_4265392 : CollatzResearch.WordTrace tailWord_4265392 prefixEnd_4265392 730065425280826955961275 := by
  unfold tailWord_4265392
  simp only [CollatzResearch.WordTrace]
  refine ⟨77785813481610364901087215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103714417975480486534782953 77785813481610364901087215)
  ·
    refine ⟨116678720222415547351630823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77785813481610364901087215 116678720222415547351630823)
    ·
      refine ⟨175018080333623321027446235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116678720222415547351630823 175018080333623321027446235)
      ·
        refine ⟨262527120500434981541169353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175018080333623321027446235 262527120500434981541169353)
        ·
          refine ⟨196895340375326236155877015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262527120500434981541169353 196895340375326236155877015)
          ·
            refine ⟨295343010562989354233815523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196895340375326236155877015 295343010562989354233815523)
            ·
              refine ⟨443014515844484031350723285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295343010562989354233815523 443014515844484031350723285)
              ·
                refine ⟨10383152715105094484782577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 443014515844484031350723285 10383152715105094484782577)
                ·
                  refine ⟨7787364536328820863586933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10383152715105094484782577 7787364536328820863586933)
                  ·
                    refine ⟨730065425280826955961275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7787364536328820863586933 730065425280826955961275)
                    ·
                      rfl

theorem cell23_4265392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_4265392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265392 prefixEnd_4265392 := by exact prefixLift 4265392
  have htrace : WordTrace (prefixWord ++ tailWord_4265392) baseStart_4265392 baseEnd_4265392 := by
    simpa [prefixWord, tailWord_4265392, baseEnd_4265392] using wordTrace_append hprefix tailTrace_4265392
  have hstable : (prefixWord ++ tailWord_4265392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265392).length < 2 ^ (prefixWord ++ tailWord_4265392).sum := by decide
  have hdescent : baseEnd_4265392 < baseStart_4265392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265439 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 3, 4]
def baseStart_4265439 : Nat := 118140960795 + 4265439 * 2 ^ 59
def prefixEnd_4265439 : Nat := 4983230072969 + 3 ^ 40 * 4265439 * 2
def baseEnd_4265439 : Nat := 730073469811080727998703

theorem tailTrace_4265439 : CollatzResearch.WordTrace tailWord_4265439 prefixEnd_4265439 730073469811080727998703 := by
  unfold tailWord_4265439
  simp only [CollatzResearch.WordTrace]
  refine ⟨155573341194050456829135371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103715560796033637886090247 155573341194050456829135371)
  ·
    refine ⟨233360011791075685243703057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155573341194050456829135371 233360011791075685243703057)
    ·
      refine ⟨175020008843306763932777293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233360011791075685243703057 175020008843306763932777293)
      ·
        refine ⟨65632503316240036474791485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175020008843306763932777293 65632503316240036474791485)
        ·
          refine ⟨24612188743590013678046807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65632503316240036474791485 24612188743590013678046807)
          ·
            refine ⟨36918283115385020517070211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24612188743590013678046807 36918283115385020517070211)
            ·
              refine ⟨55377424673077530775605317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36918283115385020517070211 55377424673077530775605317)
              ·
                refine ⟨10383267126202037020425997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55377424673077530775605317 10383267126202037020425997)
                ·
                  refine ⟨3893725172325763882659749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10383267126202037020425997 3893725172325763882659749)
                  ·
                    refine ⟨730073469811080727998703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893725172325763882659749 730073469811080727998703)
                    ·
                      rfl

theorem cell23_4265439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_4265439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265439 prefixEnd_4265439 := by exact prefixLift 4265439
  have htrace : WordTrace (prefixWord ++ tailWord_4265439) baseStart_4265439 baseEnd_4265439 := by
    simpa [prefixWord, tailWord_4265439, baseEnd_4265439] using wordTrace_append hprefix tailTrace_4265439
  have hstable : (prefixWord ++ tailWord_4265439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265439).length < 2 ^ (prefixWord ++ tailWord_4265439).sum := by decide
  have hdescent : baseEnd_4265439 < baseStart_4265439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265473 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4265473 : Nat := 118140960795 + 4265473 * 2 ^ 59
def prefixEnd_4265473 : Nat := 4983230072969 + 3 ^ 40 * 4265473 * 2
def baseEnd_4265473 : Nat := 730079289258498350323651

theorem tailTrace_4265473 : CollatzResearch.WordTrace tailWord_4265473 prefixEnd_4265473 730079289258498350323651 := by
  unfold tailWord_4265473
  simp only [CollatzResearch.WordTrace]
  refine ⟨155574581275927280635873073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103716387517284853757248715 155574581275927280635873073)
  ·
    refine ⟨116680935956945460476904805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155574581275927280635873073 116680935956945460476904805)
    ·
      refine ⟨21877675491927273839419651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116680935956945460476904805 21877675491927273839419651)
      ·
        refine ⟨32816513237890910759129477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21877675491927273839419651 32816513237890910759129477)
        ·
          refine ⟨6153096232104545767336777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32816513237890910759129477 6153096232104545767336777)
          ·
            refine ⟨4614822174078409325502583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153096232104545767336777 4614822174078409325502583)
            ·
              refine ⟨6922233261117613988253875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614822174078409325502583 6922233261117613988253875)
              ·
                refine ⟨10383349891676420982380813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6922233261117613988253875 10383349891676420982380813)
                ·
                  refine ⟨3893756209378657868392805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10383349891676420982380813 3893756209378657868392805)
                  ·
                    refine ⟨730079289258498350323651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893756209378657868392805 730079289258498350323651)
                    ·
                      rfl

theorem cell23_4265473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4265473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265473 prefixEnd_4265473 := by exact prefixLift 4265473
  have htrace : WordTrace (prefixWord ++ tailWord_4265473) baseStart_4265473 baseEnd_4265473 := by
    simpa [prefixWord, tailWord_4265473, baseEnd_4265473] using wordTrace_append hprefix tailTrace_4265473
  have hstable : (prefixWord ++ tailWord_4265473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265473).length < 2 ^ (prefixWord ++ tailWord_4265473).sum := by decide
  have hdescent : baseEnd_4265473 < baseStart_4265473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265486 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_4265486 : Nat := 118140960795 + 4265486 * 2 ^ 59
def prefixEnd_4265486 : Nat := 4983230072969 + 3 ^ 40 * 4265486 * 2
def baseEnd_4265486 : Nat := 243360504780444833345377

theorem tailTrace_4265486 : CollatzResearch.WordTrace tailWord_4265486 prefixEnd_4265486 243360504780444833345377 := by
  unfold tailWord_4265486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19446881928110022982012039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103716703616586789237397541 19446881928110022982012039)
  ·
    refine ⟨29170322892165034473018059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19446881928110022982012039 29170322892165034473018059)
    ·
      refine ⟨43755484338247551709527089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29170322892165034473018059 43755484338247551709527089)
      ·
        refine ⟨32816613253685663782145317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43755484338247551709527089 32816613253685663782145317)
        ·
          refine ⟨6153114985066061959152247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32816613253685663782145317 6153114985066061959152247)
          ·
            refine ⟨9229672477599092938728371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6153114985066061959152247 9229672477599092938728371)
            ·
              refine ⟨13844508716398639408092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9229672477599092938728371 13844508716398639408092557)
              ·
                refine ⟨5191690768649489778034709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13844508716398639408092557 5191690768649489778034709)
                ·
                  refine ⟨243360504780444833345377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5191690768649489778034709 243360504780444833345377)
                  ·
                    rfl

theorem cell23_4265486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_4265486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265486 prefixEnd_4265486 := by exact prefixLift 4265486
  have htrace : WordTrace (prefixWord ++ tailWord_4265486) baseStart_4265486 baseEnd_4265486 := by
    simpa [prefixWord, tailWord_4265486, baseEnd_4265486] using wordTrace_append hprefix tailTrace_4265486
  have hstable : (prefixWord ++ tailWord_4265486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265486).length < 2 ^ (prefixWord ++ tailWord_4265486).sum := by decide
  have hdescent : baseEnd_4265486 < baseStart_4265486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265506 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_4265506 : Nat := 118140960795 + 4265506 * 2 ^ 59
def prefixEnd_4265506 : Nat := 4983230072969 + 3 ^ 40 * 4265506 * 2
def baseEnd_4265506 : Nat := 2190254812637093421858301

theorem tailTrace_4265506 : CollatzResearch.WordTrace tailWord_4265506 prefixEnd_4265506 2190254812637093421858301 := by
  unfold tailWord_4265506
  simp only [CollatzResearch.WordTrace]
  refine ⟨38893946221201931817956093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103717189923205151514549581 38893946221201931817956093)
  ·
    refine ⟨14585229832950724431733535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38893946221201931817956093 14585229832950724431733535)
    ·
      refine ⟨21877844749426086647600303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14585229832950724431733535 21877844749426086647600303)
      ·
        refine ⟨32816767124139129971400455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21877844749426086647600303 32816767124139129971400455)
        ·
          refine ⟨49225150686208694957100683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32816767124139129971400455 49225150686208694957100683)
          ·
            refine ⟨73837726029313042435651025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49225150686208694957100683 73837726029313042435651025)
            ·
              refine ⟨55378294521984781826738269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73837726029313042435651025 55378294521984781826738269)
              ·
                refine ⟨20766860445744293185026851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55378294521984781826738269 20766860445744293185026851)
                ·
                  refine ⟨31150290668616439777540277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20766860445744293185026851 31150290668616439777540277)
                  ·
                    refine ⟨2920339750182791229144401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31150290668616439777540277 2920339750182791229144401)
                    ·
                      refine ⟨2190254812637093421858301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920339750182791229144401 2190254812637093421858301)
                      ·
                        rfl

theorem cell23_4265506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_4265506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265506 prefixEnd_4265506 := by exact prefixLift 4265506
  have htrace : WordTrace (prefixWord ++ tailWord_4265506) baseStart_4265506 baseEnd_4265506 := by
    simpa [prefixWord, tailWord_4265506, baseEnd_4265506] using wordTrace_append hprefix tailTrace_4265506
  have hstable : (prefixWord ++ tailWord_4265506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265506).length < 2 ^ (prefixWord ++ tailWord_4265506).sum := by decide
  have hdescent : baseEnd_4265506 < baseStart_4265506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265546 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_4265546 : Nat := 118140960795 + 4265546 * 2 ^ 59
def prefixEnd_4265546 : Nat := 4983230072969 + 3 ^ 40 * 4265546 * 2
def baseEnd_4265546 : Nat := 730091783954424421786039

theorem tailTrace_4265546 : CollatzResearch.WordTrace tailWord_4265546 prefixEnd_4265546 730091783954424421786039 := by
  unfold tailWord_4265546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38894310951165703525820123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103718162536441876068853661 38894310951165703525820123)
  ·
    refine ⟨58341466426748555288730185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38894310951165703525820123 58341466426748555288730185)
    ·
      refine ⟨43756099820061416466547639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58341466426748555288730185 43756099820061416466547639)
      ·
        refine ⟨65634149730092124699821459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43756099820061416466547639 65634149730092124699821459)
        ·
          refine ⟨98451224595138187049732189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65634149730092124699821459 98451224595138187049732189)
          ·
            refine ⟨36919209223176820143649571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98451224595138187049732189 36919209223176820143649571)
            ·
              refine ⟨55378813834765230215474357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36919209223176820143649571 55378813834765230215474357)
              ·
                refine ⟨5191763797009240332700721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55378813834765230215474357 5191763797009240332700721)
                ·
                  refine ⟨3893822847756930249525541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191763797009240332700721 3893822847756930249525541)
                  ·
                    refine ⟨730091783954424421786039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893822847756930249525541 730091783954424421786039)
                    ·
                      rfl

theorem cell23_4265546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_4265546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265546 prefixEnd_4265546 := by exact prefixLift 4265546
  have htrace : WordTrace (prefixWord ++ tailWord_4265546) baseStart_4265546 baseEnd_4265546 := by
    simpa [prefixWord, tailWord_4265546, baseEnd_4265546] using wordTrace_append hprefix tailTrace_4265546
  have hstable : (prefixWord ++ tailWord_4265546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265546).length < 2 ^ (prefixWord ++ tailWord_4265546).sum := by decide
  have hdescent : baseEnd_4265546 < baseStart_4265546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265553 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_4265553 : Nat := 118140960795 + 4265553 * 2 ^ 59
def prefixEnd_4265553 : Nat := 4983230072969 + 3 ^ 40 * 4265553 * 2
def baseEnd_4265553 : Nat := 2190278946227854737970585

theorem tailTrace_4265553 : CollatzResearch.WordTrace tailWord_4265553 prefixEnd_4265553 2190278946227854737970585 := by
  unfold tailWord_4265553
  simp only [CollatzResearch.WordTrace]
  refine ⟨155577499115637454298785313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103718332743758302865856875 155577499115637454298785313)
  ·
    refine ⟨116683124336728090724088985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155577499115637454298785313 116683124336728090724088985)
    ·
      refine ⟨87512343252546068043066739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116683124336728090724088985 87512343252546068043066739)
      ·
        refine ⟨131268514878819102064600109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87512343252546068043066739 131268514878819102064600109)
        ·
          refine ⟨49225693079557163274225041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131268514878819102064600109 49225693079557163274225041)
          ·
            refine ⟨36919269809667872455668781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49225693079557163274225041 36919269809667872455668781)
            ·
              refine ⟨13844726178625452170875793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36919269809667872455668781 13844726178625452170875793)
              ·
                refine ⟨10383544633969089128156845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13844726178625452170875793 10383544633969089128156845)
                ·
                  refine ⟨3893829237738408423058817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10383544633969089128156845 3893829237738408423058817)
                  ·
                    refine ⟨2920371928303806317294113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893829237738408423058817 2920371928303806317294113)
                    ·
                      refine ⟨2190278946227854737970585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920371928303806317294113 2190278946227854737970585)
                      ·
                        rfl

theorem cell23_4265553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_4265553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265553 prefixEnd_4265553 := by exact prefixLift 4265553
  have htrace : WordTrace (prefixWord ++ tailWord_4265553) baseStart_4265553 baseEnd_4265553 := by
    simpa [prefixWord, tailWord_4265553, baseEnd_4265553] using wordTrace_append hprefix tailTrace_4265553
  have hstable : (prefixWord ++ tailWord_4265553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265553).length < 2 ^ (prefixWord ++ tailWord_4265553).sum := by decide
  have hdescent : baseEnd_4265553 < baseStart_4265553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265556 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_4265556 : Nat := 118140960795 + 4265556 * 2 ^ 59
def prefixEnd_4265556 : Nat := 4983230072969 + 3 ^ 40 * 4265556 * 2
def baseEnd_4265556 : Nat := 2190280486669818226233071

theorem tailTrace_4265556 : CollatzResearch.WordTrace tailWord_4265556 prefixEnd_4265556 2190280486669818226233071 := by
  unfold tailWord_4265556
  simp only [CollatzResearch.WordTrace]
  refine ⟨77788804267313292905572261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103718405689751057207429681 77788804267313292905572261)
  ·
    refine ⟨14585400800121242419794799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77788804267313292905572261 14585400800121242419794799)
    ·
      refine ⟨21878101200181863629692199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14585400800121242419794799 21878101200181863629692199)
      ·
        refine ⟨32817151800272795444538299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21878101200181863629692199 32817151800272795444538299)
        ·
          refine ⟨49225727700409193166807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32817151800272795444538299 49225727700409193166807449)
          ·
            refine ⟨36919295775306894875105587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49225727700409193166807449 36919295775306894875105587)
            ·
              refine ⟨55378943662960342312658381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36919295775306894875105587 55378943662960342312658381)
              ·
                refine ⟨20767103873610128367246893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55378943662960342312658381 20767103873610128367246893)
                ·
                  refine ⟨7787663952603798137717585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20767103873610128367246893 7787663952603798137717585)
                  ·
                    refine ⟨5840747964452848603288189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7787663952603798137717585 5840747964452848603288189)
                    ·
                      refine ⟨2190280486669818226233071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840747964452848603288189 2190280486669818226233071)
                      ·
                        rfl

theorem cell23_4265556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_4265556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265556 prefixEnd_4265556 := by exact prefixLift 4265556
  have htrace : WordTrace (prefixWord ++ tailWord_4265556) baseStart_4265556 baseEnd_4265556 := by
    simpa [prefixWord, tailWord_4265556, baseEnd_4265556] using wordTrace_append hprefix tailTrace_4265556
  have hstable : (prefixWord ++ tailWord_4265556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265556).length < 2 ^ (prefixWord ++ tailWord_4265556).sum := by decide
  have hdescent : baseEnd_4265556 < baseStart_4265556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265573 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4265573 : Nat := 118140960795 + 4265573 * 2 ^ 59
def prefixEnd_4265573 : Nat := 4983230072969 + 3 ^ 40 * 4265573 * 2
def baseEnd_4265573 : Nat := 2190289215840944659720493

theorem tailTrace_4265573 : CollatzResearch.WordTrace tailWord_4265573 prefixEnd_4265573 2190289215840944659720493 := by
  unfold tailWord_4265573
  simp only [CollatzResearch.WordTrace]
  refine ⟨155578228575564997714513373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103718819050376665143008915 155578228575564997714513373)
  ·
    refine ⟨58341835715836874142942515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155578228575564997714513373 58341835715836874142942515)
    ·
      refine ⟨87512753573755311214413773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58341835715836874142942515 87512753573755311214413773)
      ·
        refine ⟨32817282590158241705405165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87512753573755311214413773 32817282590158241705405165)
        ·
          refine ⟨12306480971309340639526937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32817282590158241705405165 12306480971309340639526937)
          ·
            refine ⟨9229860728482005479645203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12306480971309340639526937 9229860728482005479645203)
            ·
              refine ⟨13844791092723008219467805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9229860728482005479645203 13844791092723008219467805)
              ·
                refine ⟨5191796659771128082300427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13844791092723008219467805 5191796659771128082300427)
                ·
                  refine ⟨7787694989656692123450641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191796659771128082300427 7787694989656692123450641)
                  ·
                    refine ⟨5840771242242519092587981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7787694989656692123450641 5840771242242519092587981)
                    ·
                      refine ⟨2190289215840944659720493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840771242242519092587981 2190289215840944659720493)
                      ·
                        rfl

theorem cell23_4265573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4265573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265573 prefixEnd_4265573 := by exact prefixLift 4265573
  have htrace : WordTrace (prefixWord ++ tailWord_4265573) baseStart_4265573 baseEnd_4265573 := by
    simpa [prefixWord, tailWord_4265573, baseEnd_4265573] using wordTrace_append hprefix tailTrace_4265573
  have hstable : (prefixWord ++ tailWord_4265573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265573).length < 2 ^ (prefixWord ++ tailWord_4265573).sum := by decide
  have hdescent : baseEnd_4265573 < baseStart_4265573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265609 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_4265609 : Nat := 118140960795 + 4265609 * 2 ^ 59
def prefixEnd_4265609 : Nat := 4983230072969 + 3 ^ 40 * 4265609 * 2
def baseEnd_4265609 : Nat := 2190307701144506518870327

theorem tailTrace_4265609 : CollatzResearch.WordTrace tailWord_4265609 prefixEnd_4265609 2190307701144506518870327 := by
  unfold tailWord_4265609
  simp only [CollatzResearch.WordTrace]
  refine ⟨155579541603434575862823881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103719694402289717241882587 155579541603434575862823881)
  ·
    refine ⟨116684656202575931897117911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155579541603434575862823881 116684656202575931897117911)
    ·
      refine ⟨175026984303863897845676867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116684656202575931897117911 175026984303863897845676867)
      ·
        refine ⟨262540476455795846768515301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175026984303863897845676867 262540476455795846768515301)
        ·
          refine ⟨49226339335461721269096619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262540476455795846768515301 49226339335461721269096619)
          ·
            refine ⟨73839509003192581903644929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49226339335461721269096619 73839509003192581903644929)
            ·
              refine ⟨55379631752394436427733697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73839509003192581903644929 55379631752394436427733697)
              ·
                refine ⟨41534723814295827320800273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55379631752394436427733697 41534723814295827320800273)
                ·
                  refine ⟨31151042860721870490600205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41534723814295827320800273 31151042860721870490600205)
                  ·
                    refine ⟨11681641072770701433975077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31151042860721870490600205 11681641072770701433975077)
                    ·
                      refine ⟨2190307701144506518870327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11681641072770701433975077 2190307701144506518870327)
                      ·
                        rfl

theorem cell23_4265609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_4265609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265609 prefixEnd_4265609 := by exact prefixLift 4265609
  have htrace : WordTrace (prefixWord ++ tailWord_4265609) baseStart_4265609 baseEnd_4265609 := by
    simpa [prefixWord, tailWord_4265609, baseEnd_4265609] using wordTrace_append hprefix tailTrace_4265609
  have hstable : (prefixWord ++ tailWord_4265609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265609).length < 2 ^ (prefixWord ++ tailWord_4265609).sum := by decide
  have hdescent : baseEnd_4265609 < baseStart_4265609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265654 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4265654 : Nat := 118140960795 + 4265654 * 2 ^ 59
def prefixEnd_4265654 : Nat := 4983230072969 + 3 ^ 40 * 4265654 * 2
def baseEnd_4265654 : Nat := 2190330807773958842807621

theorem tailTrace_4265654 : CollatzResearch.WordTrace tailWord_4265654 prefixEnd_4265654 2190330807773958842807621 := by
  unfold tailWord_4265654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723823930516971784263251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103720788592181032365474677 9723823930516971784263251)
  ·
    refine ⟨14585735895775457676394877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723823930516971784263251 14585735895775457676394877)
    ·
      refine ⟨5469650960915796628648079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14585735895775457676394877 5469650960915796628648079)
      ·
        refine ⟨8204476441373694942972119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469650960915796628648079 8204476441373694942972119)
        ·
          refine ⟨12306714662060542414458179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204476441373694942972119 12306714662060542414458179)
          ·
            refine ⟨18460071993090813621687269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12306714662060542414458179 18460071993090813621687269)
            ·
              refine ⟨3461263498704527554066363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18460071993090813621687269 3461263498704527554066363)
              ·
                refine ⟨5191895248056791331099545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461263498704527554066363 5191895248056791331099545)
                ·
                  refine ⟨3893921436042593498324659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191895248056791331099545 3893921436042593498324659)
                  ·
                    refine ⟨5840882154063890247486989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893921436042593498324659 5840882154063890247486989)
                    ·
                      refine ⟨2190330807773958842807621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5840882154063890247486989 2190330807773958842807621)
                      ·
                        rfl

theorem cell23_4265654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4265654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265654 prefixEnd_4265654 := by exact prefixLift 4265654
  have htrace : WordTrace (prefixWord ++ tailWord_4265654) baseStart_4265654 baseEnd_4265654 := by
    simpa [prefixWord, tailWord_4265654, baseEnd_4265654] using wordTrace_append hprefix tailTrace_4265654
  have hstable : (prefixWord ++ tailWord_4265654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265654).length < 2 ^ (prefixWord ++ tailWord_4265654).sum := by decide
  have hdescent : baseEnd_4265654 < baseStart_4265654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265677 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4265677 : Nat := 118140960795 + 4265677 * 2 ^ 59
def prefixEnd_4265677 : Nat := 4983230072969 + 3 ^ 40 * 4265677 * 2
def baseEnd_4265677 : Nat := 2190342617829012252820015

theorem tailTrace_4265677 : CollatzResearch.WordTrace tailWord_4265677 prefixEnd_4265677 2190342617829012252820015 := by
  unfold tailWord_4265677
  simp only [CollatzResearch.WordTrace]
  refine ⟨155582021767188223476299285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103721347844792148984199523 155582021767188223476299285)
  ·
    refine ⟨7292907270336947975451529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155582021767188223476299285 7292907270336947975451529)
    ·
      refine ⟨5469680452752710981588647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7292907270336947975451529 5469680452752710981588647)
      ·
        refine ⟨8204520679129066472382971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469680452752710981588647 8204520679129066472382971)
        ·
          refine ⟨12306781018693599708574457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204520679129066472382971 12306781018693599708574457)
          ·
            refine ⟨9230085764020199781430843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12306781018693599708574457 9230085764020199781430843)
            ·
              refine ⟨13845128646030299672146265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9230085764020199781430843 13845128646030299672146265)
              ·
                refine ⟨10383846484522724754109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13845128646030299672146265 10383846484522724754109699)
                ·
                  refine ⟨15575769726784087131164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10383846484522724754109699 15575769726784087131164549)
                  ·
                    refine ⟨2920456823772016337093353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15575769726784087131164549 2920456823772016337093353)
                    ·
                      refine ⟨2190342617829012252820015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920456823772016337093353 2190342617829012252820015)
                      ·
                        rfl

theorem cell23_4265677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4265677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265677 prefixEnd_4265677 := by exact prefixLift 4265677
  have htrace : WordTrace (prefixWord ++ tailWord_4265677) baseStart_4265677 baseEnd_4265677 := by
    simpa [prefixWord, tailWord_4265677, baseEnd_4265677] using wordTrace_append hprefix tailTrace_4265677
  have hstable : (prefixWord ++ tailWord_4265677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265677).length < 2 ^ (prefixWord ++ tailWord_4265677).sum := by decide
  have hdescent : baseEnd_4265677 < baseStart_4265677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265679 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 7]
def baseStart_4265679 : Nat := 118140960795 + 4265679 * 2 ^ 59
def prefixEnd_4265679 : Nat := 4983230072969 + 3 ^ 40 * 4265679 * 2
def baseEnd_4265679 : Nat := 730114548263440414998335

theorem tailTrace_4265679 : CollatzResearch.WordTrace tailWord_4265679 prefixEnd_4265679 730114548263440414998335 := by
  unfold tailWord_4265679
  simp only [CollatzResearch.WordTrace]
  refine ⟨155582094713180977817872091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103721396475453985211914727 155582094713180977817872091)
  ·
    refine ⟨233373142069771466726808137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155582094713180977817872091 233373142069771466726808137)
    ·
      refine ⟨175029856552328600045106103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233373142069771466726808137 175029856552328600045106103)
      ·
        refine ⟨262544784828492900067659155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175029856552328600045106103 262544784828492900067659155)
        ·
          refine ⟨393817177242739350101488733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262544784828492900067659155 393817177242739350101488733)
          ·
            refine ⟨147681441466027256288058275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393817177242739350101488733 147681441466027256288058275)
            ·
              refine ⟨221522162199040884432087413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147681441466027256288058275 221522162199040884432087413)
              ·
                refine ⟨20767702706160082915508195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221522162199040884432087413 20767702706160082915508195)
                ·
                  refine ⟨31151554059240124373262293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20767702706160082915508195 31151554059240124373262293)
                  ·
                    refine ⟨730114548263440414998335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31151554059240124373262293 730114548263440414998335)
                    ·
                      rfl

theorem cell23_4265679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_4265679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265679 prefixEnd_4265679 := by exact prefixLift 4265679
  have htrace : WordTrace (prefixWord ++ tailWord_4265679) baseStart_4265679 baseEnd_4265679 := by
    simpa [prefixWord, tailWord_4265679, baseEnd_4265679] using wordTrace_append hprefix tailTrace_4265679
  have hstable : (prefixWord ++ tailWord_4265679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265679).length < 2 ^ (prefixWord ++ tailWord_4265679).sum := by decide
  have hdescent : baseEnd_4265679 < baseStart_4265679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265696 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_4265696 : Nat := 118140960795 + 4265696 * 2 ^ 59
def prefixEnd_4265696 : Nat := 4983230072969 + 3 ^ 40 * 4265696 * 2
def baseEnd_4265696 : Nat := 730117457987149226160809

theorem tailTrace_4265696 : CollatzResearch.WordTrace tailWord_4265696 prefixEnd_4265696 730117457987149226160809 := by
  unfold tailWord_4265696
  simp only [CollatzResearch.WordTrace]
  refine ⟨77791357377059694860620471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103721809836079593147493961 77791357377059694860620471)
  ·
    refine ⟨116687036065589542290930707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77791357377059694860620471 116687036065589542290930707)
    ·
      refine ⟨175030554098384313436396061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116687036065589542290930707 175030554098384313436396061)
      ·
        refine ⟨65636457786894117538648523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175030554098384313436396061 65636457786894117538648523)
        ·
          refine ⟨98454686680341176307972785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65636457786894117538648523 98454686680341176307972785)
          ·
            refine ⟨73841015010255882230979589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98454686680341176307972785 73841015010255882230979589)
            ·
              refine ⟨13845190314422977918308673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73841015010255882230979589 13845190314422977918308673)
              ·
                refine ⟨10383892735817233438731505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13845190314422977918308673 10383892735817233438731505)
                ·
                  refine ⟨7787919551862925079048629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10383892735817233438731505 7787919551862925079048629)
                  ·
                    refine ⟨730117457987149226160809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7787919551862925079048629 730117457987149226160809)
                    ·
                      rfl

theorem cell23_4265696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_4265696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265696 prefixEnd_4265696 := by exact prefixLift 4265696
  have htrace : WordTrace (prefixWord ++ tailWord_4265696) baseStart_4265696 baseEnd_4265696 := by
    simpa [prefixWord, tailWord_4265696, baseEnd_4265696] using wordTrace_append hprefix tailTrace_4265696
  have hstable : (prefixWord ++ tailWord_4265696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265696).length < 2 ^ (prefixWord ++ tailWord_4265696).sum := by decide
  have hdescent : baseEnd_4265696 < baseStart_4265696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265706 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_4265706 : Nat := 118140960795 + 4265706 * 2 ^ 59
def prefixEnd_4265706 : Nat := 4983230072969 + 3 ^ 40 * 4265706 * 2
def baseEnd_4265706 : Nat := 2190357508767992639357381

theorem tailTrace_4265706 : CollatzResearch.WordTrace tailWord_4265706 prefixEnd_4265706 2190357508767992639357381 := by
  unfold tailWord_4265706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38895769871020790357276243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103722052989388774286069981 38895769871020790357276243)
  ·
    refine ⟨58343654806531185535914365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38895769871020790357276243 58343654806531185535914365)
    ·
      refine ⟨21878870552449194575967887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58343654806531185535914365 21878870552449194575967887)
      ·
        refine ⟨32818305828673791863951831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21878870552449194575967887 32818305828673791863951831)
        ·
          refine ⟨49227458743010687795927747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32818305828673791863951831 49227458743010687795927747)
          ·
            refine ⟨73841188114516031693891621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49227458743010687795927747 73841188114516031693891621)
            ·
              refine ⟨13845222771471755942604679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73841188114516031693891621 13845222771471755942604679)
              ·
                refine ⟨20767834157207633913907019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13845222771471755942604679 20767834157207633913907019)
                ·
                  refine ⟨31151751235811450870860529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20767834157207633913907019 31151751235811450870860529)
                  ·
                    refine ⟨23363813426858588153145397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31151751235811450870860529 23363813426858588153145397)
                    ·
                      refine ⟨2190357508767992639357381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23363813426858588153145397 2190357508767992639357381)
                      ·
                        rfl

theorem cell23_4265706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_4265706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265706 prefixEnd_4265706 := by exact prefixLift 4265706
  have htrace : WordTrace (prefixWord ++ tailWord_4265706) baseStart_4265706 baseEnd_4265706 := by
    simpa [prefixWord, tailWord_4265706, baseEnd_4265706] using wordTrace_append hprefix tailTrace_4265706
  have hstable : (prefixWord ++ tailWord_4265706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265706).length < 2 ^ (prefixWord ++ tailWord_4265706).sum := by decide
  have hdescent : baseEnd_4265706 < baseStart_4265706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265756 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 8]
def baseStart_4265756 : Nat := 118140960795 + 4265756 * 2 ^ 59
def prefixEnd_4265756 : Nat := 4983230072969 + 3 ^ 40 * 4265756 * 2
def baseEnd_4265756 : Nat := 243375909200079715970239

theorem tailTrace_4265756 : CollatzResearch.WordTrace tailWord_4265756 prefixEnd_4265756 243375909200079715970239 := by
  unfold tailWord_4265756
  simp only [CollatzResearch.WordTrace]
  refine ⟨77792451566951009984212561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103723268755934679978950081 77792451566951009984212561)
  ·
    refine ⟨58344338675213257488159421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77792451566951009984212561 58344338675213257488159421)
    ·
      refine ⟨21879127003204971558059783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58344338675213257488159421 21879127003204971558059783)
      ·
        refine ⟨32818690504807457337089675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21879127003204971558059783 32818690504807457337089675)
        ·
          refine ⟨49228035757211186005634513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32818690504807457337089675 49228035757211186005634513)
          ·
            refine ⟨36921026817908389504225885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49228035757211186005634513 36921026817908389504225885)
            ·
              refine ⟨13845385056715646064084707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36921026817908389504225885 13845385056715646064084707)
              ·
                refine ⟨20768077585073469096127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13845385056715646064084707 20768077585073469096127061)
                ·
                  refine ⟨243375909200079715970239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20768077585073469096127061 243375909200079715970239)
                  ·
                    rfl

theorem cell23_4265756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_4265756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265756 prefixEnd_4265756 := by exact prefixLift 4265756
  have htrace : WordTrace (prefixWord ++ tailWord_4265756) baseStart_4265756 baseEnd_4265756 := by
    simpa [prefixWord, tailWord_4265756, baseEnd_4265756] using wordTrace_append hprefix tailTrace_4265756
  have hstable : (prefixWord ++ tailWord_4265756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265756).length < 2 ^ (prefixWord ++ tailWord_4265756).sum := by decide
  have hdescent : baseEnd_4265756 < baseStart_4265756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265760 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 1, 4]
def baseStart_4265760 : Nat := 118140960795 + 4265760 * 2 ^ 59
def prefixEnd_4265760 : Nat := 4983230072969 + 3 ^ 40 * 4265760 * 2
def baseEnd_4265760 : Nat := 730128412241111809360711

theorem tailTrace_4265760 : CollatzResearch.WordTrace tailWord_4265760 prefixEnd_4265760 730128412241111809360711 := by
  unfold tailWord_4265760
  simp only [CollatzResearch.WordTrace]
  refine ⟨77792524512943764325785367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103723366017258352434380489 77792524512943764325785367)
  ·
    refine ⟨116688786769415646488678051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77792524512943764325785367 116688786769415646488678051)
    ·
      refine ⟨175033180154123469733017077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116688786769415646488678051 175033180154123469733017077)
      ·
        refine ⟨16409360639449075287470351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175033180154123469733017077 16409360639449075287470351)
        ·
          refine ⟨24614040959173612931205527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16409360639449075287470351 24614040959173612931205527)
          ·
            refine ⟨36921061438760419396808291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24614040959173612931205527 36921061438760419396808291)
            ·
              refine ⟨55381592158140629095212437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36921061438760419396808291 55381592158140629095212437)
              ·
                refine ⟨2596012132412841988838083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55381592158140629095212437 2596012132412841988838083)
                ·
                  refine ⟨3894018198619262983257125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596012132412841988838083 3894018198619262983257125)
                  ·
                    refine ⟨730128412241111809360711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894018198619262983257125 730128412241111809360711)
                    ·
                      rfl

theorem cell23_4265760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_4265760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265760 prefixEnd_4265760 := by exact prefixLift 4265760
  have htrace : WordTrace (prefixWord ++ tailWord_4265760) baseStart_4265760 baseEnd_4265760 := by
    simpa [prefixWord, tailWord_4265760, baseEnd_4265760] using wordTrace_append hprefix tailTrace_4265760
  have hstable : (prefixWord ++ tailWord_4265760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265760).length < 2 ^ (prefixWord ++ tailWord_4265760).sum := by decide
  have hdescent : baseEnd_4265760 < baseStart_4265760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265783 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_4265783 : Nat := 118140960795 + 4265783 * 2 ^ 59
def prefixEnd_4265783 : Nat := 4983230072969 + 3 ^ 40 * 4265783 * 2
def baseEnd_4265783 : Nat := 2190397046778388838094527

theorem tailTrace_4265783 : CollatzResearch.WordTrace tailWord_4265783 prefixEnd_4265783 2190397046778388838094527 := by
  unfold tailWord_4265783
  simp only [CollatzResearch.WordTrace]
  refine ⟨155585887904804203579658003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103723925269869469053105335 155585887904804203579658003)
  ·
    refine ⟨233378831857206305369487005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155585887904804203579658003 233378831857206305369487005)
    ·
      refine ⟨87517061946452364513557627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233378831857206305369487005 87517061946452364513557627)
      ·
        refine ⟨131275592919678546770336441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87517061946452364513557627 131275592919678546770336441)
        ·
          refine ⟨98456694689758910077752331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131275592919678546770336441 98456694689758910077752331)
          ·
            refine ⟨147685042034638365116628497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98456694689758910077752331 147685042034638365116628497)
            ·
              refine ⟨110763781525978773837471373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147685042034638365116628497 110763781525978773837471373)
              ·
                refine ⟨41536418072242040189051765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110763781525978773837471373 41536418072242040189051765)
                ·
                  refine ⟨3894039194272691267723603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41536418072242040189051765 3894039194272691267723603)
                  ·
                    refine ⟨5841058791409036901585405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894039194272691267723603 5841058791409036901585405)
                    ·
                      refine ⟨2190397046778388838094527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841058791409036901585405 2190397046778388838094527)
                      ·
                        rfl

theorem cell23_4265783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_4265783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265783 prefixEnd_4265783 := by exact prefixLift 4265783
  have htrace : WordTrace (prefixWord ++ tailWord_4265783) baseStart_4265783 baseEnd_4265783 := by
    simpa [prefixWord, tailWord_4265783, baseEnd_4265783] using wordTrace_append hprefix tailTrace_4265783
  have hstable : (prefixWord ++ tailWord_4265783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265783).length < 2 ^ (prefixWord ++ tailWord_4265783).sum := by decide
  have hdescent : baseEnd_4265783 < baseStart_4265783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265810 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_4265810 : Nat := 118140960795 + 4265810 * 2 ^ 59
def prefixEnd_4265810 : Nat := 4983230072969 + 3 ^ 40 * 4265810 * 2
def baseEnd_4265810 : Nat := 2190410910756060232456903

theorem tailTrace_4265810 : CollatzResearch.WordTrace tailWord_4265810 prefixEnd_4265810 2190410910756060232456903 := by
  unfold tailWord_4265810
  simp only [CollatzResearch.WordTrace]
  refine ⟨38896718168926596797722721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103724581783804258127260589 38896718168926596797722721)
  ·
    refine ⟨29172538626694947598292041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38896718168926596797722721 29172538626694947598292041)
    ·
      refine ⟨21879403970021210698719031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29172538626694947598292041 21879403970021210698719031)
      ·
        refine ⟨32819105955031816048078547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21879403970021210698719031 32819105955031816048078547)
        ·
          refine ⟨49228658932547724072117821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32819105955031816048078547 49228658932547724072117821)
          ·
            refine ⟨18460747099705396527044183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49228658932547724072117821 18460747099705396527044183)
            ·
              refine ⟨27691120649558094790566275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18460747099705396527044183 27691120649558094790566275)
              ·
                refine ⟨41536680974337142185849413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27691120649558094790566275 41536680974337142185849413)
                ·
                  refine ⟨7788127682688214159846765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41536680974337142185849413 7788127682688214159846765)
                  ·
                    refine ⟨2920547881008080309942537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7788127682688214159846765 2920547881008080309942537)
                    ·
                      refine ⟨2190410910756060232456903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920547881008080309942537 2190410910756060232456903)
                      ·
                        rfl

theorem cell23_4265810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_4265810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265810 prefixEnd_4265810 := by exact prefixLift 4265810
  have htrace : WordTrace (prefixWord ++ tailWord_4265810) baseStart_4265810 baseEnd_4265810 := by
    simpa [prefixWord, tailWord_4265810, baseEnd_4265810] using wordTrace_append hprefix tailTrace_4265810
  have hstable : (prefixWord ++ tailWord_4265810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265810).length < 2 ^ (prefixWord ++ tailWord_4265810).sum := by decide
  have hdescent : baseEnd_4265810 < baseStart_4265810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265840 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2]
def baseStart_4265840 : Nat := 118140960795 + 4265840 * 2 ^ 59
def prefixEnd_4265840 : Nat := 4983230072969 + 3 ^ 40 * 4265840 * 2
def baseEnd_4265840 : Nat := 2190426315175695115081765

theorem tailTrace_4265840 : CollatzResearch.WordTrace tailWord_4265840 prefixEnd_4265840 2190426315175695115081765 := by
  unfold tailWord_4265840
  simp only [CollatzResearch.WordTrace]
  refine ⟨77793983432798851157241487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103725311243731801542988649 77793983432798851157241487)
  ·
    refine ⟨116690975149198276735862231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77793983432798851157241487 116690975149198276735862231)
    ·
      refine ⟨175036462723797415103793347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116690975149198276735862231 175036462723797415103793347)
      ·
        refine ⟨262554694085696122655690021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175036462723797415103793347 262554694085696122655690021)
        ·
          refine ⟨49229005141068022997941879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262554694085696122655690021 49229005141068022997941879)
          ·
            refine ⟨73843507711602034496912819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49229005141068022997941879 73843507711602034496912819)
            ·
              refine ⟨110765261567403051745369229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73843507711602034496912819 110765261567403051745369229)
              ·
                refine ⟨41536973087776144404513461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110765261567403051745369229 41536973087776144404513461)
                ·
                  refine ⟨3894091226979013537923137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41536973087776144404513461 3894091226979013537923137)
                  ·
                    refine ⟨2920568420234260153442353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3894091226979013537923137 2920568420234260153442353)
                    ·
                      refine ⟨2190426315175695115081765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920568420234260153442353 2190426315175695115081765)
                      ·
                        rfl

theorem cell23_4265840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2].length) (baseStart_4265840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265840 prefixEnd_4265840 := by exact prefixLift 4265840
  have htrace : WordTrace (prefixWord ++ tailWord_4265840) baseStart_4265840 baseEnd_4265840 := by
    simpa [prefixWord, tailWord_4265840, baseEnd_4265840] using wordTrace_append hprefix tailTrace_4265840
  have hstable : (prefixWord ++ tailWord_4265840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265840).length < 2 ^ (prefixWord ++ tailWord_4265840).sum := by decide
  have hdescent : baseEnd_4265840 < baseStart_4265840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265854 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4265854 : Nat := 118140960795 + 4265854 * 2 ^ 59
def prefixEnd_4265854 : Nat := 4983230072969 + 3 ^ 40 * 4265854 * 2
def baseEnd_4265854 : Nat := 730144501301619353435567

theorem tailTrace_4265854 : CollatzResearch.WordTrace tailWord_4265854 prefixEnd_4265854 730144501301619353435567 := by
  unfold tailWord_4265854
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448559685943372838186577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103725651658364655136995077 19448559685943372838186577)
  ·
    refine ⟨14586419764457529628639933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19448559685943372838186577 14586419764457529628639933)
    ·
      refine ⟨5469907411671573610739975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14586419764457529628639933 5469907411671573610739975)
      ·
        refine ⟨8204861117507360416109963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469907411671573610739975 8204861117507360416109963)
        ·
          refine ⟨12307291676261040624164945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204861117507360416109963 12307291676261040624164945)
          ·
            refine ⟨9230468757195780468123709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12307291676261040624164945 9230468757195780468123709)
            ·
              refine ⟨3461425783948417675546391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9230468757195780468123709 3461425783948417675546391)
              ·
                refine ⟨5192138675922626513319587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461425783948417675546391 5192138675922626513319587)
                ·
                  refine ⟨7788208013883939769979381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192138675922626513319587 7788208013883939769979381)
                  ·
                    refine ⟨730144501301619353435567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7788208013883939769979381 730144501301619353435567)
                    ·
                      rfl

theorem cell23_4265854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4265854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265854 prefixEnd_4265854 := by exact prefixLift 4265854
  have htrace : WordTrace (prefixWord ++ tailWord_4265854) baseStart_4265854 baseEnd_4265854 := by
    simpa [prefixWord, tailWord_4265854, baseEnd_4265854] using wordTrace_append hprefix tailTrace_4265854
  have hstable : (prefixWord ++ tailWord_4265854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265854).length < 2 ^ (prefixWord ++ tailWord_4265854).sum := by decide
  have hdescent : baseEnd_4265854 < baseStart_4265854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265860 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_4265860 : Nat := 118140960795 + 4265860 * 2 ^ 59
def prefixEnd_4265860 : Nat := 4983230072969 + 3 ^ 40 * 4265860 * 2
def baseEnd_4265860 : Nat := 2190436584788785036831673

theorem tailTrace_4265860 : CollatzResearch.WordTrace tailWord_4265860 prefixEnd_4265860 2190436584788785036831673 := by
  unfold tailWord_4265860
  simp only [CollatzResearch.WordTrace]
  refine ⟨77794348162762622865105517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103725797550350163820140689 77794348162762622865105517)
  ·
    refine ⟨29172880561035983574414569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77794348162762622865105517 29172880561035983574414569)
    ·
      refine ⟨21879660420776987680810927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29172880561035983574414569 21879660420776987680810927)
      ·
        refine ⟨32819490631165481521216391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21879660420776987680810927 32819490631165481521216391)
        ·
          refine ⟨49229235946748222281824587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32819490631165481521216391 49229235946748222281824587)
          ·
            refine ⟨73843853920122333422736881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49229235946748222281824587 73843853920122333422736881)
            ·
              refine ⟨55382890440091750067052661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73843853920122333422736881 55382890440091750067052661)
              ·
                refine ⟨5192145978758601568786187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55382890440091750067052661 5192145978758601568786187)
                ·
                  refine ⟨7788218968137902353179281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192145978758601568786187 7788218968137902353179281)
                  ·
                    refine ⟨5841164226103426764884461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7788218968137902353179281 5841164226103426764884461)
                    ·
                      refine ⟨2190436584788785036831673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841164226103426764884461 2190436584788785036831673)
                      ·
                        rfl

theorem cell23_4265860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_4265860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265860 prefixEnd_4265860 := by exact prefixLift 4265860
  have htrace : WordTrace (prefixWord ++ tailWord_4265860) baseStart_4265860 baseEnd_4265860 := by
    simpa [prefixWord, tailWord_4265860, baseEnd_4265860] using wordTrace_append hprefix tailTrace_4265860
  have hstable : (prefixWord ++ tailWord_4265860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265860).length < 2 ^ (prefixWord ++ tailWord_4265860).sum := by decide
  have hdescent : baseEnd_4265860 < baseStart_4265860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265863 : List Nat := [1, 1, 4, 2, 5, 10]
def baseStart_4265863 : Nat := 118140960795 + 4265863 * 2 ^ 59
def prefixEnd_4265863 : Nat := 4983230072969 + 3 ^ 40 * 4265863 * 2
def baseEnd_4265863 : Nat := 9014148663501022737013

theorem tailTrace_4265863 : CollatzResearch.WordTrace tailWord_4265863 prefixEnd_4265863 9014148663501022737013 := by
  unfold tailWord_4265863
  simp only [CollatzResearch.WordTrace]
  refine ⟨155588805744514377242570243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103725870496342918161713495 155588805744514377242570243)
  ·
    refine ⟨233383208616771565863855365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155588805744514377242570243 233383208616771565863855365)
    ·
      refine ⟨43759351615644668599472881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233383208616771565863855365 43759351615644668599472881)
      ·
        refine ⟨32819513711733501449604661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43759351615644668599472881 32819513711733501449604661)
        ·
          refine ⟨3076829410475015760900437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32819513711733501449604661 3076829410475015760900437)
          ·
            refine ⟨9014148663501022737013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3076829410475015760900437 9014148663501022737013)
            ·
              rfl

theorem cell23_4265863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 10].length) (baseStart_4265863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265863 prefixEnd_4265863 := by exact prefixLift 4265863
  have htrace : WordTrace (prefixWord ++ tailWord_4265863) baseStart_4265863 baseEnd_4265863 := by
    simpa [prefixWord, tailWord_4265863, baseEnd_4265863] using wordTrace_append hprefix tailTrace_4265863
  have hstable : (prefixWord ++ tailWord_4265863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265863).length < 2 ^ (prefixWord ++ tailWord_4265863).sum := by decide
  have hdescent : baseEnd_4265863 < baseStart_4265863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265908 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4265908 : Nat := 118140960795 + 4265908 * 2 ^ 59
def prefixEnd_4265908 : Nat := 4983230072969 + 3 ^ 40 * 4265908 * 2
def baseEnd_4265908 : Nat := 2190461231860200849031453

theorem tailTrace_4265908 : CollatzResearch.WordTrace tailWord_4265908 prefixEnd_4265908 2190461231860200849031453 := by
  unfold tailWord_4265908
  simp only [CollatzResearch.WordTrace]
  refine ⟨77795223514675674963979189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103726964686234233285305585 77795223514675674963979189)
  ·
    refine ⟨7293302204500844527873049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77795223514675674963979189 7293302204500844527873049)
    ·
      refine ⟨5469976653375633395904787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7293302204500844527873049 5469976653375633395904787)
      ·
        refine ⟨8204964980063450093857181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469976653375633395904787 8204964980063450093857181)
        ·
          refine ⟨3076861867523793785196443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8204964980063450093857181 3076861867523793785196443)
          ·
            refine ⟨4615292801285690677794665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076861867523793785196443 4615292801285690677794665)
            ·
              refine ⟨3461469600964268008345999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615292801285690677794665 3461469600964268008345999)
              ·
                refine ⟨5192204401446402012518999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461469600964268008345999 5192204401446402012518999)
                ·
                  refine ⟨7788306602169603018778499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192204401446402012518999 7788306602169603018778499)
                  ·
                    refine ⟨11682459903254404528167749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7788306602169603018778499 11682459903254404528167749)
                    ·
                      refine ⟨2190461231860200849031453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11682459903254404528167749 2190461231860200849031453)
                      ·
                        rfl

theorem cell23_4265908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4265908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265908 prefixEnd_4265908 := by exact prefixLift 4265908
  have htrace : WordTrace (prefixWord ++ tailWord_4265908) baseStart_4265908 baseEnd_4265908 := by
    simpa [prefixWord, tailWord_4265908, baseEnd_4265908] using wordTrace_append hprefix tailTrace_4265908
  have hstable : (prefixWord ++ tailWord_4265908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265908).length < 2 ^ (prefixWord ++ tailWord_4265908).sum := by decide
  have hdescent : baseEnd_4265908 < baseStart_4265908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265930 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_4265930 : Nat := 118140960795 + 4265930 * 2 ^ 59
def prefixEnd_4265930 : Nat := 4983230072969 + 3 ^ 40 * 4265930 * 2
def baseEnd_4265930 : Nat := 2190472528434599762956351

theorem tailTrace_4265930 : CollatzResearch.WordTrace tailWord_4265930 prefixEnd_4265930 2190472528434599762956351 := by
  unfold tailWord_4265930
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897812358817911921314811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103727499623514431790172829 38897812358817911921314811)
  ·
    refine ⟨58346718538226867881972217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38897812358817911921314811 58346718538226867881972217)
    ·
      refine ⟨43760038903670150911479163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58346718538226867881972217 43760038903670150911479163)
      ·
        refine ⟨65640058355505226367218745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43760038903670150911479163 65640058355505226367218745)
        ·
          refine ⟨49230043766628919775414059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65640058355505226367218745 49230043766628919775414059)
          ·
            refine ⟨73845065649943379663121089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49230043766628919775414059 73845065649943379663121089)
            ·
              refine ⟨55383799237457534747340817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73845065649943379663121089 55383799237457534747340817)
              ·
                refine ⟨41537849428093151060505613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55383799237457534747340817 41537849428093151060505613)
                ·
                  refine ⟨15576693535534931647689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41537849428093151060505613 15576693535534931647689605)
                  ·
                    refine ⟨2920630037912799683941801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15576693535534931647689605 2920630037912799683941801)
                    ·
                      refine ⟨2190472528434599762956351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920630037912799683941801 2190472528434599762956351)
                      ·
                        rfl

theorem cell23_4265930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_4265930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265930 prefixEnd_4265930 := by exact prefixLift 4265930
  have htrace : WordTrace (prefixWord ++ tailWord_4265930) baseStart_4265930 baseEnd_4265930 := by
    simpa [prefixWord, tailWord_4265930, baseEnd_4265930] using wordTrace_append hprefix tailTrace_4265930
  have hstable : (prefixWord ++ tailWord_4265930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265930).length < 2 ^ (prefixWord ++ tailWord_4265930).sum := by decide
  have hdescent : baseEnd_4265930 < baseStart_4265930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265943 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4265943 : Nat := 118140960795 + 4265943 * 2 ^ 59
def prefixEnd_4265943 : Nat := 4983230072969 + 3 ^ 40 * 4265943 * 2
def baseEnd_4265943 : Nat := 2190479203683108212093791

theorem tailTrace_4265943 : CollatzResearch.WordTrace tailWord_4265943 prefixEnd_4265943 2190479203683108212093791 := by
  unfold tailWord_4265943
  simp only [CollatzResearch.WordTrace]
  refine ⟨155591723584224550905482483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103727815722816367270321655 155591723584224550905482483)
  ·
    refine ⟨233387585376336826358223725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155591723584224550905482483 233387585376336826358223725)
    ·
      refine ⟨87520344516126309884333897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233387585376336826358223725 87520344516126309884333897)
      ·
        refine ⟨65640258387094732413250423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87520344516126309884333897 65640258387094732413250423)
        ·
          refine ⟨98460387580642098619875635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65640258387094732413250423 98460387580642098619875635)
          ·
            refine ⟨147690581370963147929813453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98460387580642098619875635 147690581370963147929813453)
            ·
              refine ⟨55383968014111180473680045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147690581370963147929813453 55383968014111180473680045)
              ·
                refine ⟨20768988005291692677630017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55383968014111180473680045 20768988005291692677630017)
                ·
                  refine ⟨15576741003968769508222513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20768988005291692677630017 15576741003968769508222513)
                  ·
                    refine ⟨11682555752976577131166885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15576741003968769508222513 11682555752976577131166885)
                    ·
                      refine ⟨2190479203683108212093791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11682555752976577131166885 2190479203683108212093791)
                      ·
                        rfl

theorem cell23_4265943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4265943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265943 prefixEnd_4265943 := by exact prefixLift 4265943
  have htrace : WordTrace (prefixWord ++ tailWord_4265943) baseStart_4265943 baseEnd_4265943 := by
    simpa [prefixWord, tailWord_4265943, baseEnd_4265943] using wordTrace_append hprefix tailTrace_4265943
  have hstable : (prefixWord ++ tailWord_4265943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265943).length < 2 ^ (prefixWord ++ tailWord_4265943).sum := by decide
  have hdescent : baseEnd_4265943 < baseStart_4265943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265953 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 7]
def baseStart_4265953 : Nat := 118140960795 + 4265953 * 2 ^ 59
def prefixEnd_4265953 : Nat := 4983230072969 + 3 ^ 40 * 4265953 * 2
def baseEnd_4265953 : Nat := 243387148721072574774305

theorem tailTrace_4265953 : CollatzResearch.WordTrace tailWord_4265953 prefixEnd_4265953 243387148721072574774305 := by
  unfold tailWord_4265953
  simp only [CollatzResearch.WordTrace]
  refine ⟨155592088314188322613346513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103728058876125548408897675 155592088314188322613346513)
  ·
    refine ⟨116694066235641241960009885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155592088314188322613346513 116694066235641241960009885)
    ·
      refine ⟨43760274838365465735003707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116694066235641241960009885 43760274838365465735003707)
      ·
        refine ⟨65640412257548198602505561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43760274838365465735003707 65640412257548198602505561)
        ·
          refine ⟨49230309193161148951879171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65640412257548198602505561 49230309193161148951879171)
          ·
            refine ⟨73845463789741723427818757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49230309193161148951879171 73845463789741723427818757)
            ·
              refine ⟨13846024460576573142716017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73845463789741723427818757 13846024460576573142716017)
              ·
                refine ⟨10384518345432429857037013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13846024460576573142716017 10384518345432429857037013)
                ·
                  refine ⟨243387148721072574774305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10384518345432429857037013 243387148721072574774305)
                  ·
                    rfl

theorem cell23_4265953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_4265953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265953 prefixEnd_4265953 := by exact prefixLift 4265953
  have htrace : WordTrace (prefixWord ++ tailWord_4265953) baseStart_4265953 baseEnd_4265953 := by
    simpa [prefixWord, tailWord_4265953, baseEnd_4265953] using wordTrace_append hprefix tailTrace_4265953
  have hstable : (prefixWord ++ tailWord_4265953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265953).length < 2 ^ (prefixWord ++ tailWord_4265953).sum := by decide
  have hdescent : baseEnd_4265953 < baseStart_4265953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4265963 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3]
def baseStart_4265963 : Nat := 118140960795 + 4265963 * 2 ^ 59
def prefixEnd_4265963 : Nat := 4983230072969 + 3 ^ 40 * 4265963 * 2
def baseEnd_4265963 : Nat := 2190489473296198133843699

theorem tailTrace_4265963 : CollatzResearch.WordTrace tailWord_4265963 prefixEnd_4265963 2190489473296198133843699 := by
  unfold tailWord_4265963
  simp only [CollatzResearch.WordTrace]
  refine ⟨155592453044152094321210543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103728302029434729547473695 155592453044152094321210543)
  ·
    refine ⟨233388679566228141481815815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155592453044152094321210543 233388679566228141481815815)
    ·
      refine ⟨350083019349342212222723723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233388679566228141481815815 350083019349342212222723723)
      ·
        refine ⟨525124529024013318334085585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350083019349342212222723723 525124529024013318334085585)
        ·
          refine ⟨393843396768009988750564189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525124529024013318334085585 393843396768009988750564189)
          ·
            refine ⟨147691273788003745781461571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393843396768009988750564189 147691273788003745781461571)
            ·
              refine ⟨221536910682005618672192357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147691273788003745781461571 221536910682005618672192357)
              ·
                refine ⟨41538170752876053501036067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221536910682005618672192357 41538170752876053501036067)
                ·
                  refine ⟨62307256129314080251554101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41538170752876053501036067 62307256129314080251554101)
                  ·
                    refine ⟨5841305262123195023583197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62307256129314080251554101 5841305262123195023583197)
                    ·
                      refine ⟨2190489473296198133843699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841305262123195023583197 2190489473296198133843699)
                      ·
                        rfl

theorem cell23_4265963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].length) (baseStart_4265963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4265963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4265963 prefixEnd_4265963 := by exact prefixLift 4265963
  have htrace : WordTrace (prefixWord ++ tailWord_4265963) baseStart_4265963 baseEnd_4265963 := by
    simpa [prefixWord, tailWord_4265963, baseEnd_4265963] using wordTrace_append hprefix tailTrace_4265963
  have hstable : (prefixWord ++ tailWord_4265963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4265963).length < 2 ^ (prefixWord ++ tailWord_4265963).sum := by decide
  have hdescent : baseEnd_4265963 < baseStart_4265963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4265963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266003 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_4266003 : Nat := 118140960795 + 4266003 * 2 ^ 59
def prefixEnd_4266003 : Nat := 4983230072969 + 3 ^ 40 * 4266003 * 2
def baseEnd_4266003 : Nat := 2190510012522377977343515

theorem tailTrace_4266003 : CollatzResearch.WordTrace tailWord_4266003 prefixEnd_4266003 2190510012522377977343515 := by
  unfold tailWord_4266003
  simp only [CollatzResearch.WordTrace]
  refine ⟨155593911964007181152666663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103729274642671454101777775 155593911964007181152666663)
  ·
    refine ⟨233390867946010771728999995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155593911964007181152666663 233390867946010771728999995)
    ·
      refine ⟨350086301919016157593499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233390867946010771728999995 350086301919016157593499993)
      ·
        refine ⟨262564726439262118195124995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350086301919016157593499993 262564726439262118195124995)
        ·
          refine ⟨393847089658893177292687493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262564726439262118195124995 393847089658893177292687493)
          ·
            refine ⟨73846329311042470742378905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393847089658893177292687493 73846329311042470742378905)
            ·
              refine ⟨55384746983281853056784179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73846329311042470742378905 55384746983281853056784179)
              ·
                refine ⟨83077120474922779585176269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55384746983281853056784179 83077120474922779585176269)
                ·
                  refine ⟨31153920178096042344441101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83077120474922779585176269 31153920178096042344441101)
                  ·
                    refine ⟨11682720066786015879165413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31153920178096042344441101 11682720066786015879165413)
                    ·
                      refine ⟨2190510012522377977343515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11682720066786015879165413 2190510012522377977343515)
                      ·
                        rfl

theorem cell23_4266003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_4266003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266003 prefixEnd_4266003 := by exact prefixLift 4266003
  have htrace : WordTrace (prefixWord ++ tailWord_4266003) baseStart_4266003 baseEnd_4266003 := by
    simpa [prefixWord, tailWord_4266003, baseEnd_4266003] using wordTrace_append hprefix tailTrace_4266003
  have hstable : (prefixWord ++ tailWord_4266003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266003).length < 2 ^ (prefixWord ++ tailWord_4266003).sum := by decide
  have hdescent : baseEnd_4266003 < baseStart_4266003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266017 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_4266017 : Nat := 118140960795 + 4266017 * 2 ^ 59
def prefixEnd_4266017 : Nat := 4983230072969 + 3 ^ 40 * 4266017 * 2
def baseEnd_4266017 : Nat := 730172400417180307522817

theorem tailTrace_4266017 : CollatzResearch.WordTrace tailWord_4266017 prefixEnd_4266017 730172400417180307522817 := by
  unfold tailWord_4266017
  simp only [CollatzResearch.WordTrace]
  refine ⟨155594422585956461543676305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103729615057304307695784203 155594422585956461543676305)
  ·
    refine ⟨116695816939467346157757229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155594422585956461543676305 116695816939467346157757229)
    ·
      refine ⟨43760931352300254809158961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116695816939467346157757229 43760931352300254809158961)
      ·
        refine ⟨32820698514225191106869221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43760931352300254809158961 32820698514225191106869221)
        ·
          refine ⟨6153880971417223332537979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32820698514225191106869221 6153880971417223332537979)
          ·
            refine ⟨9230821457125834998806969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6153880971417223332537979 9230821457125834998806969)
            ·
              refine ⟨6923116092844376249105227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9230821457125834998806969 6923116092844376249105227)
              ·
                refine ⟨10384674139266564373657841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923116092844376249105227 10384674139266564373657841)
                ·
                  refine ⟨7788505604449923280243381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10384674139266564373657841 7788505604449923280243381)
                  ·
                    refine ⟨730172400417180307522817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7788505604449923280243381 730172400417180307522817)
                    ·
                      rfl

theorem cell23_4266017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_4266017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266017 prefixEnd_4266017 := by exact prefixLift 4266017
  have htrace : WordTrace (prefixWord ++ tailWord_4266017) baseStart_4266017 baseEnd_4266017 := by
    simpa [prefixWord, tailWord_4266017, baseEnd_4266017] using wordTrace_append hprefix tailTrace_4266017
  have hstable : (prefixWord ++ tailWord_4266017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266017).length < 2 ^ (prefixWord ++ tailWord_4266017).sum := by decide
  have hdescent : baseEnd_4266017 < baseStart_4266017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266060 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 6]
def baseStart_4266060 : Nat := 118140960795 + 4266060 * 2 ^ 59
def prefixEnd_4266060 : Nat := 4983230072969 + 3 ^ 40 * 4266060 * 2
def baseEnd_4266060 : Nat := 243393253435520472703417

theorem tailTrace_4266060 : CollatzResearch.WordTrace tailWord_4266060 prefixEnd_4266060 243393253435520472703417 := by
  unfold tailWord_4266060
  simp only [CollatzResearch.WordTrace]
  refine ⟨77797995462400339943745817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103730660616533786591661089 77797995462400339943745817)
  ·
    refine ⟨58348496596800254957809363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77797995462400339943745817 58348496596800254957809363)
    ·
      refine ⟨87522744895200382436714045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58348496596800254957809363 87522744895200382436714045)
      ·
        refine ⟨32821029335700143413767767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87522744895200382436714045 32821029335700143413767767)
        ·
          refine ⟨49231544003550215120651651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32821029335700143413767767 49231544003550215120651651)
          ·
            refine ⟨73847316005325322680977477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49231544003550215120651651 73847316005325322680977477)
            ·
              refine ⟨13846371750998498002683277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73847316005325322680977477 13846371750998498002683277)
              ·
                refine ⟨5192389406624436751006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13846371750998498002683277 5192389406624436751006229)
                ·
                  refine ⟨243393253435520472703417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5192389406624436751006229 243393253435520472703417)
                  ·
                    rfl

theorem cell23_4266060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_4266060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266060 prefixEnd_4266060 := by exact prefixLift 4266060
  have htrace : WordTrace (prefixWord ++ tailWord_4266060) baseStart_4266060 baseEnd_4266060 := by
    simpa [prefixWord, tailWord_4266060, baseEnd_4266060] using wordTrace_append hprefix tailTrace_4266060
  have hstable : (prefixWord ++ tailWord_4266060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266060).length < 2 ^ (prefixWord ++ tailWord_4266060).sum := by decide
  have hdescent : baseEnd_4266060 < baseStart_4266060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266063 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_4266063 : Nat := 118140960795 + 4266063 * 2 ^ 59
def prefixEnd_4266063 : Nat := 4983230072969 + 3 ^ 40 * 4266063 * 2
def baseEnd_4266063 : Nat := 2190540821361647742593239

theorem tailTrace_4266063 : CollatzResearch.WordTrace tailWord_4266063 prefixEnd_4266063 2190540821361647742593239 := by
  unfold tailWord_4266063
  simp only [CollatzResearch.WordTrace]
  refine ⟨155596100343789811399850843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103730733562526540933233895 155596100343789811399850843)
  ·
    refine ⟨233394150515684717099776265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155596100343789811399850843 233394150515684717099776265)
    ·
      refine ⟨175045612886763537824832199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233394150515684717099776265 175045612886763537824832199)
      ·
        refine ⟨262568419330145306737248299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175045612886763537824832199 262568419330145306737248299)
        ·
          refine ⟨393852628995217960105872449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262568419330145306737248299 393852628995217960105872449)
          ·
            refine ⟨295389471746413470079404337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393852628995217960105872449 295389471746413470079404337)
            ·
              refine ⟨221542103809810102559553253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295389471746413470079404337 221542103809810102559553253)
              ·
                refine ⟨41539144464339394229916235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221542103809810102559553253 41539144464339394229916235)
                ·
                  refine ⟨62308716696509091344874353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41539144464339394229916235 62308716696509091344874353)
                  ·
                    refine ⟨46731537522381818508655765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62308716696509091344874353 46731537522381818508655765)
                    ·
                      refine ⟨2190540821361647742593239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46731537522381818508655765 2190540821361647742593239)
                      ·
                        rfl

theorem cell23_4266063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_4266063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266063 prefixEnd_4266063 := by exact prefixLift 4266063
  have htrace : WordTrace (prefixWord ++ tailWord_4266063) baseStart_4266063 baseEnd_4266063 := by
    simpa [prefixWord, tailWord_4266063, baseEnd_4266063] using wordTrace_append hprefix tailTrace_4266063
  have hstable : (prefixWord ++ tailWord_4266063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266063).length < 2 ^ (prefixWord ++ tailWord_4266063).sum := by decide
  have hdescent : baseEnd_4266063 < baseStart_4266063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266087 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_4266087 : Nat := 118140960795 + 4266087 * 2 ^ 59
def prefixEnd_4266087 : Nat := 4983230072969 + 3 ^ 40 * 4266087 * 2
def baseEnd_4266087 : Nat := 2190553144897355648693129

theorem tailTrace_4266087 : CollatzResearch.WordTrace tailWord_4266087 prefixEnd_4266087 2190553144897355648693129 := by
  unfold tailWord_4266087
  simp only [CollatzResearch.WordTrace]
  refine ⟨155596975695702863498724515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103731317130468575665816343 155596975695702863498724515)
  ·
    refine ⟨233395463543554295248086773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155596975695702863498724515 233395463543554295248086773)
    ·
      refine ⟨21880824707208215179508135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233395463543554295248086773 21880824707208215179508135)
      ·
        refine ⟨32821237060812322769262203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21880824707208215179508135 32821237060812322769262203)
        ·
          refine ⟨49231855591218484153893305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32821237060812322769262203 49231855591218484153893305)
          ·
            refine ⟨36923891693413863115419979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49231855591218484153893305 36923891693413863115419979)
            ·
              refine ⟨55385837540120794673129969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36923891693413863115419979 55385837540120794673129969)
              ·
                refine ⟨41539378155090596004847477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55385837540120794673129969 41539378155090596004847477)
                ·
                  refine ⟨3894316702039743375454451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41539378155090596004847477 3894316702039743375454451)
                  ·
                    refine ⟨5841475053059615063181677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894316702039743375454451 5841475053059615063181677)
                    ·
                      refine ⟨2190553144897355648693129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841475053059615063181677 2190553144897355648693129)
                      ·
                        rfl

theorem cell23_4266087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_4266087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266087 prefixEnd_4266087 := by exact prefixLift 4266087
  have htrace : WordTrace (prefixWord ++ tailWord_4266087) baseStart_4266087 baseEnd_4266087 := by
    simpa [prefixWord, tailWord_4266087, baseEnd_4266087] using wordTrace_append hprefix tailTrace_4266087
  have hstable : (prefixWord ++ tailWord_4266087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266087).length < 2 ^ (prefixWord ++ tailWord_4266087).sum := by decide
  have hdescent : baseEnd_4266087 < baseStart_4266087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266097 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_4266097 : Nat := 118140960795 + 4266097 * 2 ^ 59
def prefixEnd_4266097 : Nat := 4983230072969 + 3 ^ 40 * 4266097 * 2
def baseEnd_4266097 : Nat := 2190558279703900609568083

theorem tailTrace_4266097 : CollatzResearch.WordTrace tailWord_4266097 prefixEnd_4266097 2190558279703900609568083 := by
  unfold tailWord_4266097
  simp only [CollatzResearch.WordTrace]
  refine ⟨155597340425666635206588545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103731560283777756804392363 155597340425666635206588545)
  ·
    refine ⟨116698005319249976404941409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155597340425666635206588545 116698005319249976404941409)
    ·
      refine ⟨87523503989437482303706057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116698005319249976404941409 87523503989437482303706057)
      ·
        refine ⟨65642627992078111727779543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87523503989437482303706057 65642627992078111727779543)
        ·
          refine ⟨98463941988117167591669315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65642627992078111727779543 98463941988117167591669315)
          ·
            refine ⟨147695912982175751387503973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98463941988117167591669315 147695912982175751387503973)
            ·
              refine ⟨27692983684157953385156995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147695912982175751387503973 27692983684157953385156995)
              ·
                refine ⟨41539475526236930077735493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27692983684157953385156995 41539475526236930077735493)
                ·
                  refine ⟨7788651661169424389575405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41539475526236930077735493 7788651661169424389575405)
                  ·
                    refine ⟨2920744372938534146090777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7788651661169424389575405 2920744372938534146090777)
                    ·
                      refine ⟨2190558279703900609568083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920744372938534146090777 2190558279703900609568083)
                      ·
                        rfl

theorem cell23_4266097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_4266097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266097 prefixEnd_4266097 := by exact prefixLift 4266097
  have htrace : WordTrace (prefixWord ++ tailWord_4266097) baseStart_4266097 baseEnd_4266097 := by
    simpa [prefixWord, tailWord_4266097, baseEnd_4266097] using wordTrace_append hprefix tailTrace_4266097
  have hstable : (prefixWord ++ tailWord_4266097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266097).length < 2 ^ (prefixWord ++ tailWord_4266097).sum := by decide
  have hdescent : baseEnd_4266097 < baseStart_4266097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266157 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4266157 : Nat := 118140960795 + 4266157 * 2 ^ 59
def prefixEnd_4266157 : Nat := 4983230072969 + 3 ^ 40 * 4266157 * 2
def baseEnd_4266157 : Nat := 2190589088543170374817807

theorem tailTrace_4266157 : CollatzResearch.WordTrace tailWord_4266157 prefixEnd_4266157 2190589088543170374817807 := by
  unfold tailWord_4266157
  simp only [CollatzResearch.WordTrace]
  refine ⟨155599528805449265453772725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103733019203632843635848483 155599528805449265453772725)
  ·
    refine ⟨14587455825510868636291193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155599528805449265453772725 14587455825510868636291193)
    ·
      refine ⟨10940591869133151477218395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14587455825510868636291193 10940591869133151477218395)
      ·
        refine ⟨16410887803699727215827593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10940591869133151477218395 16410887803699727215827593)
        ·
          refine ⟨12308165852774795411870695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16410887803699727215827593 12308165852774795411870695)
          ·
            refine ⟨18462248779162193117806043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12308165852774795411870695 18462248779162193117806043)
            ·
              refine ⟨27693373168743289676709065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18462248779162193117806043 27693373168743289676709065)
              ·
                refine ⟨20770029876557467257531799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27693373168743289676709065 20770029876557467257531799)
                ·
                  refine ⟨31155044814836200886297699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20770029876557467257531799 31155044814836200886297699)
                  ·
                    refine ⟨46732567222254301329446549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31155044814836200886297699 46732567222254301329446549)
                    ·
                      refine ⟨2190589088543170374817807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46732567222254301329446549 2190589088543170374817807)
                      ·
                        rfl

theorem cell23_4266157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4266157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266157 prefixEnd_4266157 := by exact prefixLift 4266157
  have htrace : WordTrace (prefixWord ++ tailWord_4266157) baseStart_4266157 baseEnd_4266157 := by
    simpa [prefixWord, tailWord_4266157, baseEnd_4266157] using wordTrace_append hprefix tailTrace_4266157
  have hstable : (prefixWord ++ tailWord_4266157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266157).length < 2 ^ (prefixWord ++ tailWord_4266157).sum := by decide
  have hdescent : baseEnd_4266157 < baseStart_4266157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266160 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_4266160 : Nat := 118140960795 + 4266160 * 2 ^ 59
def prefixEnd_4266160 : Nat := 4983230072969 + 3 ^ 40 * 4266160 * 2
def baseEnd_4266160 : Nat := 2190590628985133863080293

theorem tailTrace_4266160 : CollatzResearch.WordTrace tailWord_4266160 prefixEnd_4266160 2190590628985133863080293 := by
  unfold tailWord_4266160
  simp only [CollatzResearch.WordTrace]
  refine ⟨77799819112219198483065967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103733092149625597977421289 77799819112219198483065967)
  ·
    refine ⟨116699728668328797724598951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77799819112219198483065967 116699728668328797724598951)
    ·
      refine ⟨175049593002493196586898427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116699728668328797724598951 175049593002493196586898427)
      ·
        refine ⟨262574389503739794880347641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175049593002493196586898427 262574389503739794880347641)
        ·
          refine ⟨196930792127804846160260731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262574389503739794880347641 196930792127804846160260731)
          ·
            refine ⟨295396188191707269240391097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196930792127804846160260731 295396188191707269240391097)
            ·
              refine ⟨221547141143780451930293323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295396188191707269240391097 221547141143780451930293323)
              ·
                refine ⟨332320711715670677895439985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221547141143780451930293323 332320711715670677895439985)
                ·
                  refine ⟨249240533786753008421579989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332320711715670677895439985 249240533786753008421579989)
                  ·
                    refine ⟨5841575010627023634880781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 249240533786753008421579989 5841575010627023634880781)
                    ·
                      refine ⟨2190590628985133863080293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841575010627023634880781 2190590628985133863080293)
                      ·
                        rfl

theorem cell23_4266160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_4266160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266160 prefixEnd_4266160 := by exact prefixLift 4266160
  have htrace : WordTrace (prefixWord ++ tailWord_4266160) baseStart_4266160 baseEnd_4266160 := by
    simpa [prefixWord, tailWord_4266160, baseEnd_4266160] using wordTrace_append hprefix tailTrace_4266160
  have hstable : (prefixWord ++ tailWord_4266160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266160).length < 2 ^ (prefixWord ++ tailWord_4266160).sum := by decide
  have hdescent : baseEnd_4266160 < baseStart_4266160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266178 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4266178 : Nat := 118140960795 + 4266178 * 2 ^ 59
def prefixEnd_4266178 : Nat := 4983230072969 + 3 ^ 40 * 4266178 * 2
def baseEnd_4266178 : Nat := 2190599871636914792655211

theorem tailTrace_4266178 : CollatzResearch.WordTrace tailWord_4266178 prefixEnd_4266178 2190599871636914792655211 := by
  unfold tailWord_4266178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900073684593296510071797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103733529825582124026858125 38900073684593296510071797)
  ·
    refine ⟨3646881907930621547819231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38900073684593296510071797 3646881907930621547819231)
    ·
      refine ⟨5470322861895932321728847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646881907930621547819231 5470322861895932321728847)
      ·
        refine ⟨8205484292843898482593271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470322861895932321728847 8205484292843898482593271)
        ·
          refine ⟨12308226439265847723889907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205484292843898482593271 12308226439265847723889907)
          ·
            refine ⟨18462339658898771585834861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12308226439265847723889907 18462339658898771585834861)
            ·
              refine ⟨6923377372087039344688073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18462339658898771585834861 6923377372087039344688073)
              ·
                refine ⟨5192533029065279508516055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923377372087039344688073 5192533029065279508516055)
                ·
                  refine ⟨7788799543597919262774083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192533029065279508516055 7788799543597919262774083)
                  ·
                    refine ⟨11683199315396878894161125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7788799543597919262774083 11683199315396878894161125)
                    ·
                      refine ⟨2190599871636914792655211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11683199315396878894161125 2190599871636914792655211)
                      ·
                        rfl

theorem cell23_4266178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4266178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266178 prefixEnd_4266178 := by exact prefixLift 4266178
  have htrace : WordTrace (prefixWord ++ tailWord_4266178) baseStart_4266178 baseEnd_4266178 := by
    simpa [prefixWord, tailWord_4266178, baseEnd_4266178] using wordTrace_append hprefix tailTrace_4266178
  have hstable : (prefixWord ++ tailWord_4266178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266178).length < 2 ^ (prefixWord ++ tailWord_4266178).sum := by decide
  have hdescent : baseEnd_4266178 < baseStart_4266178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266194 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4266194 : Nat := 118140960795 + 4266194 * 2 ^ 59
def prefixEnd_4266194 : Nat := 4983230072969 + 3 ^ 40 * 4266194 * 2
def baseEnd_4266194 : Nat := 2190608087327386730055137

theorem tailTrace_4266194 : CollatzResearch.WordTrace tailWord_4266194 prefixEnd_4266194 2190608087327386730055137 := by
  unfold tailWord_4266194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900219576578805193217409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103733918870876813848579757 38900219576578805193217409)
  ·
    refine ⟨29175164682434103894913057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38900219576578805193217409 29175164682434103894913057)
    ·
      refine ⟨21881373511825577921184793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29175164682434103894913057 21881373511825577921184793)
      ·
        refine ⟨16411030133869183440888595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21881373511825577921184793 16411030133869183440888595)
        ·
          refine ⟨24616545200803775161332893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16411030133869183440888595 24616545200803775161332893)
          ·
            refine ⟨9231204450301415685499835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24616545200803775161332893 9231204450301415685499835)
            ·
              refine ⟨13846806675452123528249753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9231204450301415685499835 13846806675452123528249753)
              ·
                refine ⟨10385105006589092646187315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13846806675452123528249753 10385105006589092646187315)
                ·
                  refine ⟨15577657509883638969280973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10385105006589092646187315 15577657509883638969280973)
                  ·
                    refine ⟨5841621566206364613480365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15577657509883638969280973 5841621566206364613480365)
                    ·
                      refine ⟨2190608087327386730055137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841621566206364613480365 2190608087327386730055137)
                      ·
                        rfl

theorem cell23_4266194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4266194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266194 prefixEnd_4266194 := by exact prefixLift 4266194
  have htrace : WordTrace (prefixWord ++ tailWord_4266194) baseStart_4266194 baseEnd_4266194 := by
    simpa [prefixWord, tailWord_4266194, baseEnd_4266194] using wordTrace_append hprefix tailTrace_4266194
  have hstable : (prefixWord ++ tailWord_4266194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266194).length < 2 ^ (prefixWord ++ tailWord_4266194).sum := by decide
  have hdescent : baseEnd_4266194 < baseStart_4266194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266234 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_4266234 : Nat := 118140960795 + 4266234 * 2 ^ 59
def prefixEnd_4266234 : Nat := 4983230072969 + 3 ^ 40 * 4266234 * 2
def baseEnd_4266234 : Nat := 2190628626553566573554953

theorem tailTrace_4266234 : CollatzResearch.WordTrace tailWord_4266234 prefixEnd_4266234 2190628626553566573554953 := by
  unfold tailWord_4266234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900584306542576901081439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103734891484113538402883837 38900584306542576901081439)
  ·
    refine ⟨58350876459813865351622159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38900584306542576901081439 58350876459813865351622159)
    ·
      refine ⟨87526314689720798027433239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58350876459813865351622159 87526314689720798027433239)
      ·
        refine ⟨131289472034581197041149859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87526314689720798027433239 131289472034581197041149859)
        ·
          refine ⟨196934208051871795561724789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131289472034581197041149859 196934208051871795561724789)
          ·
            refine ⟨18462582004862980833911699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196934208051871795561724789 18462582004862980833911699)
            ·
              refine ⟨27693873007294471250867549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18462582004862980833911699 27693873007294471250867549)
              ·
                refine ⟨10385202377735426719075331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27693873007294471250867549 10385202377735426719075331)
                ·
                  refine ⟨15577803566603140078612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10385202377735426719075331 15577803566603140078612997)
                  ·
                    refine ⟨2920838168738088764739937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15577803566603140078612997 2920838168738088764739937)
                    ·
                      refine ⟨2190628626553566573554953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920838168738088764739937 2190628626553566573554953)
                      ·
                        rfl

theorem cell23_4266234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_4266234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266234 prefixEnd_4266234 := by exact prefixLift 4266234
  have htrace : WordTrace (prefixWord ++ tailWord_4266234) baseStart_4266234 baseEnd_4266234 := by
    simpa [prefixWord, tailWord_4266234, baseEnd_4266234] using wordTrace_append hprefix tailTrace_4266234
  have hstable : (prefixWord ++ tailWord_4266234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266234).length < 2 ^ (prefixWord ++ tailWord_4266234).sum := by decide
  have hdescent : baseEnd_4266234 < baseStart_4266234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266240 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 9]
def baseStart_4266240 : Nat := 118140960795 + 4266240 * 2 ^ 59
def prefixEnd_4266240 : Nat := 4983230072969 + 3 ^ 40 * 4266240 * 2
def baseEnd_4266240 : Nat := 243403523048610394453325

theorem tailTrace_4266240 : CollatzResearch.WordTrace tailWord_4266240 prefixEnd_4266240 243403523048610394453325 := by
  unfold tailWord_4266240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77801278032074285314522087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103735037376099047086029449 77801278032074285314522087)
  ·
    refine ⟨116701917048111427971783131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77801278032074285314522087 116701917048111427971783131)
    ·
      refine ⟨175052875572167141957674697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116701917048111427971783131 175052875572167141957674697)
      ·
        refine ⟨131289656679125356468256023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175052875572167141957674697 131289656679125356468256023)
        ·
          refine ⟨196934485018688034702384035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131289656679125356468256023 196934485018688034702384035)
          ·
            refine ⟨295401727528032052053576053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196934485018688034702384035 295401727528032052053576053)
            ·
              refine ⟨27693911955753004880022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 295401727528032052053576053 27693911955753004880022755)
              ·
                refine ⟨41540867933629507320034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27693911955753004880022755 41540867933629507320034133)
                ·
                  refine ⟨243403523048610394453325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41540867933629507320034133 243403523048610394453325)
                  ·
                    rfl

theorem cell23_4266240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_4266240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266240 prefixEnd_4266240 := by exact prefixLift 4266240
  have htrace : WordTrace (prefixWord ++ tailWord_4266240) baseStart_4266240 baseEnd_4266240 := by
    simpa [prefixWord, tailWord_4266240, baseEnd_4266240] using wordTrace_append hprefix tailTrace_4266240
  have hstable : (prefixWord ++ tailWord_4266240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266240).length < 2 ^ (prefixWord ++ tailWord_4266240).sum := by decide
  have hdescent : baseEnd_4266240 < baseStart_4266240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266267 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3]
def baseStart_4266267 : Nat := 118140960795 + 4266267 * 2 ^ 59
def prefixEnd_4266267 : Nat := 4983230072969 + 3 ^ 40 * 4266267 * 2
def baseEnd_4266267 : Nat := 2190645571415164944442301

theorem tailTrace_4266267 : CollatzResearch.WordTrace tailWord_4266267 prefixEnd_4266267 2190645571415164944442301 := by
  unfold tailWord_4266267
  simp only [CollatzResearch.WordTrace]
  refine ⟨155603540835050754240277055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103735693890033836160184703 155603540835050754240277055)
  ·
    refine ⟨233405311252576131360415583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155603540835050754240277055 233405311252576131360415583)
    ·
      refine ⟨350107966878864197040623375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233405311252576131360415583 350107966878864197040623375)
      ·
        refine ⟨525161950318296295560935063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350107966878864197040623375 525161950318296295560935063)
        ·
          refine ⟨787742925477444443341402595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525161950318296295560935063 787742925477444443341402595)
          ·
            refine ⟨1181614388216166665012103893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787742925477444443341402595 1181614388216166665012103893)
            ·
              refine ⟨27694087223816406211221185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1181614388216166665012103893 27694087223816406211221185)
              ·
                refine ⟨20770565417862304658415889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27694087223816406211221185 20770565417862304658415889)
                ·
                  refine ⟨15577924063396728493811917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20770565417862304658415889 15577924063396728493811917)
                  ·
                    refine ⟨5841721523773773185179469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15577924063396728493811917 5841721523773773185179469)
                    ·
                      refine ⟨2190645571415164944442301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841721523773773185179469 2190645571415164944442301)
                      ·
                        rfl

theorem cell23_4266267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].length) (baseStart_4266267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266267 prefixEnd_4266267 := by exact prefixLift 4266267
  have htrace : WordTrace (prefixWord ++ tailWord_4266267) baseStart_4266267 baseEnd_4266267 := by
    simpa [prefixWord, tailWord_4266267, baseEnd_4266267] using wordTrace_append hprefix tailTrace_4266267
  have hstable : (prefixWord ++ tailWord_4266267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266267).length < 2 ^ (prefixWord ++ tailWord_4266267).sum := by decide
  have hdescent : baseEnd_4266267 < baseStart_4266267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266274 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4266274 : Nat := 118140960795 + 4266274 * 2 ^ 59
def prefixEnd_4266274 : Nat := 4983230072969 + 3 ^ 40 * 4266274 * 2
def baseEnd_4266274 : Nat := 243405462864416268561641

theorem tailTrace_4266274 : CollatzResearch.WordTrace tailWord_4266274 prefixEnd_4266274 243405462864416268561641 := by
  unfold tailWord_4266274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900949036506348608945469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103735864097350262957187917 38900949036506348608945469)
  ·
    refine ⟨14587855888689880728354551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38900949036506348608945469 14587855888689880728354551)
    ·
      refine ⟨21881783833034821092531827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14587855888689880728354551 21881783833034821092531827)
      ·
        refine ⟨32822675749552231638797741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21881783833034821092531827 32822675749552231638797741)
        ·
          refine ⟨12308503406082086864549153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32822675749552231638797741 12308503406082086864549153)
          ·
            refine ⟨9231377554561565148411865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12308503406082086864549153 9231377554561565148411865)
            ·
              refine ⟨6923533165921173861308899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9231377554561565148411865 6923533165921173861308899)
              ·
                refine ⟨10385299748881760791963349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923533165921173861308899 10385299748881760791963349)
                ·
                  refine ⟨243405462864416268561641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10385299748881760791963349 243405462864416268561641)
                  ·
                    rfl

theorem cell23_4266274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4266274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266274 prefixEnd_4266274 := by exact prefixLift 4266274
  have htrace : WordTrace (prefixWord ++ tailWord_4266274) baseStart_4266274 baseEnd_4266274 := by
    simpa [prefixWord, tailWord_4266274, baseEnd_4266274] using wordTrace_append hprefix tailTrace_4266274
  have hstable : (prefixWord ++ tailWord_4266274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266274).length < 2 ^ (prefixWord ++ tailWord_4266274).sum := by decide
  have hdescent : baseEnd_4266274 < baseStart_4266274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266285 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4266285 : Nat := 118140960795 + 4266285 * 2 ^ 59
def prefixEnd_4266285 : Nat := 4983230072969 + 3 ^ 40 * 4266285 * 2
def baseEnd_4266285 : Nat := 2190654814066945874017219

theorem tailTrace_4266285 : CollatzResearch.WordTrace tailWord_4266285 prefixEnd_4266285 2190654814066945874017219 := by
  unfold tailWord_4266285
  simp only [CollatzResearch.WordTrace]
  refine ⟨155604197348985543314432309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103736131565990362209621539 155604197348985543314432309)
  ·
    refine ⟨14587893501467394685728029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155604197348985543314432309 14587893501467394685728029)
    ·
      refine ⟨5470460063050273007148011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14587893501467394685728029 5470460063050273007148011)
      ·
        refine ⟨8205690094575409510722017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470460063050273007148011 8205690094575409510722017)
        ·
          refine ⟨6154267570931557133041513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8205690094575409510722017 6154267570931557133041513)
          ·
            refine ⟨4615700678198667849781135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154267570931557133041513 4615700678198667849781135)
            ·
              refine ⟨6923551017298001774671703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615700678198667849781135 6923551017298001774671703)
              ·
                refine ⟨10385326525947002662007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923551017298001774671703 10385326525947002662007555)
                ·
                  refine ⟨15577989788920503993011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10385326525947002662007555 15577989788920503993011333)
                  ·
                    refine ⟨2920873085422594498689625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15577989788920503993011333 2920873085422594498689625)
                    ·
                      refine ⟨2190654814066945874017219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2920873085422594498689625 2190654814066945874017219)
                      ·
                        rfl

theorem cell23_4266285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4266285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266285 prefixEnd_4266285 := by exact prefixLift 4266285
  have htrace : WordTrace (prefixWord ++ tailWord_4266285) baseStart_4266285 baseEnd_4266285 := by
    simpa [prefixWord, tailWord_4266285, baseEnd_4266285] using wordTrace_append hprefix tailTrace_4266285
  have hstable : (prefixWord ++ tailWord_4266285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266285).length < 2 ^ (prefixWord ++ tailWord_4266285).sum := by decide
  have hdescent : baseEnd_4266285 < baseStart_4266285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266307 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_4266307 : Nat := 118140960795 + 4266307 * 2 ^ 59
def prefixEnd_4266307 : Nat := 4983230072969 + 3 ^ 40 * 4266307 * 2
def baseEnd_4266307 : Nat := 2190666110641344787942117

theorem tailTrace_4266307 : CollatzResearch.WordTrace tailWord_4266307 prefixEnd_4266307 2190666110641344787942117 := by
  unfold tailWord_4266307
  simp only [CollatzResearch.WordTrace]
  refine ⟨155604999754905841071733175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103736666503270560714488783 155604999754905841071733175)
  ·
    refine ⟨233407499632358761607599763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155604999754905841071733175 233407499632358761607599763)
    ·
      refine ⟨350111249448538142411399645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233407499632358761607599763 350111249448538142411399645)
      ·
        refine ⟨131291718543201803404274867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350111249448538142411399645 131291718543201803404274867)
        ·
          refine ⟨196937577814802705106412301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131291718543201803404274867 196937577814802705106412301)
          ·
            refine ⟨73851591680551014414904613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196937577814802705106412301 73851591680551014414904613)
            ·
              refine ⟨13847173440103315202794615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73851591680551014414904613 13847173440103315202794615)
              ·
                refine ⟨20770760160154972804191923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13847173440103315202794615 20770760160154972804191923)
                ·
                  refine ⟨31156140240232459206287885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20770760160154972804191923 31156140240232459206287885)
                  ·
                    refine ⟨11683552590087172202357957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31156140240232459206287885 11683552590087172202357957)
                    ·
                      refine ⟨2190666110641344787942117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11683552590087172202357957 2190666110641344787942117)
                      ·
                        rfl

theorem cell23_4266307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_4266307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266307 prefixEnd_4266307 := by exact prefixLift 4266307
  have htrace : WordTrace (prefixWord ++ tailWord_4266307) baseStart_4266307 baseEnd_4266307 := by
    simpa [prefixWord, tailWord_4266307, baseEnd_4266307] using wordTrace_append hprefix tailTrace_4266307
  have hstable : (prefixWord ++ tailWord_4266307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266307).length < 2 ^ (prefixWord ++ tailWord_4266307).sum := by decide
  have hdescent : baseEnd_4266307 < baseStart_4266307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266324 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4266324 : Nat := 118140960795 + 4266324 * 2 ^ 59
def prefixEnd_4266324 : Nat := 4983230072969 + 3 ^ 40 * 4266324 * 2
def baseEnd_4266324 : Nat := 2190674839812471221429539

theorem tailTrace_4266324 : CollatzResearch.WordTrace tailWord_4266324 prefixEnd_4266324 2190674839812471221429539 := by
  unfold tailWord_4266324
  simp only [CollatzResearch.WordTrace]
  refine ⟨77802809897922126487551013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103737079863896168650068017 77802809897922126487551013)
  ·
    refine ⟨14588026855860398716415815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77802809897922126487551013 14588026855860398716415815)
    ·
      refine ⟨21882040283790598074623723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14588026855860398716415815 21882040283790598074623723)
      ·
        refine ⟨32823060425685897111935585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21882040283790598074623723 32823060425685897111935585)
        ·
          refine ⟨24617295319264422833951689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32823060425685897111935585 24617295319264422833951689)
          ·
            refine ⟨18462971489448317125463767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24617295319264422833951689 18462971489448317125463767)
            ·
              refine ⟨27694457234172475688195651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18462971489448317125463767 27694457234172475688195651)
              ·
                refine ⟨41541685851258713532293477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27694457234172475688195651 41541685851258713532293477)
                ·
                  refine ⟨7789066097111008787305027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41541685851258713532293477 7789066097111008787305027)
                  ·
                    refine ⟨11683599145666513180957541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7789066097111008787305027 11683599145666513180957541)
                    ·
                      refine ⟨2190674839812471221429539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11683599145666513180957541 2190674839812471221429539)
                      ·
                        rfl

theorem cell23_4266324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4266324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266324 prefixEnd_4266324 := by exact prefixLift 4266324
  have htrace : WordTrace (prefixWord ++ tailWord_4266324) baseStart_4266324 baseEnd_4266324 := by
    simpa [prefixWord, tailWord_4266324, baseEnd_4266324] using wordTrace_append hprefix tailTrace_4266324
  have hstable : (prefixWord ++ tailWord_4266324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266324).length < 2 ^ (prefixWord ++ tailWord_4266324).sum := by decide
  have hdescent : baseEnd_4266324 < baseStart_4266324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266347 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 6]
def baseStart_4266347 : Nat := 118140960795 + 4266347 * 2 ^ 59
def prefixEnd_4266347 : Nat := 4983230072969 + 3 ^ 40 * 4266347 * 2
def baseEnd_4266347 : Nat := 243409627763058292382437

theorem tailTrace_4266347 : CollatzResearch.WordTrace tailWord_4266347 prefixEnd_4266347 243409627763058292382437 := by
  unfold tailWord_4266347
  simp only [CollatzResearch.WordTrace]
  refine ⟨155606458674760927903189295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103737639116507285268792863 155606458674760927903189295)
  ·
    refine ⟨233409688012141391854783943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155606458674760927903189295 233409688012141391854783943)
    ·
      refine ⟨350114532018212087782175915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233409688012141391854783943 350114532018212087782175915)
      ·
        refine ⟨525171798027318131673263873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350114532018212087782175915 525171798027318131673263873)
        ·
          refine ⟨393878848520488598754947905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525171798027318131673263873 393878848520488598754947905)
          ·
            refine ⟨295409136390366449066210929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393878848520488598754947905 295409136390366449066210929)
            ·
              refine ⟨221556852292774836799658197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295409136390366449066210929 221556852292774836799658197)
              ·
                refine ⟨5192738725611910237491989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 221556852292774836799658197 5192738725611910237491989)
                ·
                  refine ⟨243409627763058292382437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5192738725611910237491989 243409627763058292382437)
                  ·
                    rfl

theorem cell23_4266347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 6].length) (baseStart_4266347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266347 prefixEnd_4266347 := by exact prefixLift 4266347
  have htrace : WordTrace (prefixWord ++ tailWord_4266347) baseStart_4266347 baseEnd_4266347 := by
    simpa [prefixWord, tailWord_4266347, baseEnd_4266347] using wordTrace_append hprefix tailTrace_4266347
  have hstable : (prefixWord ++ tailWord_4266347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266347).length < 2 ^ (prefixWord ++ tailWord_4266347).sum := by decide
  have hdescent : baseEnd_4266347 < baseStart_4266347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266394 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_4266394 : Nat := 118140960795 + 4266394 * 2 ^ 59
def prefixEnd_4266394 : Nat := 4983230072969 + 3 ^ 40 * 4266394 * 2
def baseEnd_4266394 : Nat := 730236927819428649184739

theorem tailTrace_4266394 : CollatzResearch.WordTrace tailWord_4266394 prefixEnd_4266394 730236927819428649184739 := by
  unfold tailWord_4266394
  simp only [CollatzResearch.WordTrace]
  refine ⟨38902043226397663732537559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103738781937060436620100157 38902043226397663732537559)
  ·
    refine ⟨58353064839596495598806339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38902043226397663732537559 58353064839596495598806339)
    ·
      refine ⟨87529597259394743398209509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58353064839596495598806339 87529597259394743398209509)
      ·
        refine ⟨16411799486136514387164283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87529597259394743398209509 16411799486136514387164283)
        ·
          refine ⟨24617699229204771580746425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16411799486136514387164283 24617699229204771580746425)
          ·
            refine ⟨18463274421903578685559819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24617699229204771580746425 18463274421903578685559819)
            ·
              refine ⟨27694911632855368028339729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18463274421903578685559819 27694911632855368028339729)
              ·
                refine ⟨20771183724641526021254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27694911632855368028339729 20771183724641526021254797)
                ·
                  refine ⟨7789193896740572257970549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20771183724641526021254797 7789193896740572257970549)
                  ·
                    refine ⟨730236927819428649184739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7789193896740572257970549 730236927819428649184739)
                    ·
                      rfl

theorem cell23_4266394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_4266394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266394 prefixEnd_4266394 := by exact prefixLift 4266394
  have htrace : WordTrace (prefixWord ++ tailWord_4266394) baseStart_4266394 baseEnd_4266394 := by
    simpa [prefixWord, tailWord_4266394, baseEnd_4266394] using wordTrace_append hprefix tailTrace_4266394
  have hstable : (prefixWord ++ tailWord_4266394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266394).length < 2 ^ (prefixWord ++ tailWord_4266394).sum := by decide
  have hdescent : baseEnd_4266394 < baseStart_4266394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266408 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4266408 : Nat := 118140960795 + 4266408 * 2 ^ 59
def prefixEnd_4266408 : Nat := 4983230072969 + 3 ^ 40 * 4266408 * 2
def baseEnd_4266408 : Nat := 2190717972187448892779153

theorem tailTrace_4266408 : CollatzResearch.WordTrace tailWord_4266408 prefixEnd_4266408 2190717972187448892779153 := by
  unfold tailWord_4266408
  simp only [CollatzResearch.WordTrace]
  refine ⟨77804341763769967660579939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103739122351693290214106585 77804341763769967660579939)
  ·
    refine ⟨116706512645654951490869909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77804341763769967660579939 116706512645654951490869909)
    ·
      refine ⟨5470617780265075851134527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 116706512645654951490869909 5470617780265075851134527)
      ·
        refine ⟨8205926670397613776701791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470617780265075851134527 8205926670397613776701791)
        ·
          refine ⟨12308890005596420665052687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205926670397613776701791 12308890005596420665052687)
          ·
            refine ⟨18463335008394630997579031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12308890005596420665052687 18463335008394630997579031)
            ·
              refine ⟨27695002512591946496368547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18463335008394630997579031 27695002512591946496368547)
              ·
                refine ⟨41542503768887919744552821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27695002512591946496368547 41542503768887919744552821)
                ·
                  refine ⟨3894609728333242476051827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41542503768887919744552821 3894609728333242476051827)
                  ·
                    refine ⟨5841914592499863714077741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894609728333242476051827 5841914592499863714077741)
                    ·
                      refine ⟨2190717972187448892779153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841914592499863714077741 2190717972187448892779153)
                      ·
                        rfl

theorem cell23_4266408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4266408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266408 prefixEnd_4266408 := by exact prefixLift 4266408
  have htrace : WordTrace (prefixWord ++ tailWord_4266408) baseStart_4266408 baseEnd_4266408 := by
    simpa [prefixWord, tailWord_4266408, baseEnd_4266408] using wordTrace_append hprefix tailTrace_4266408
  have hstable : (prefixWord ++ tailWord_4266408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266408).length < 2 ^ (prefixWord ++ tailWord_4266408).sum := by decide
  have hdescent : baseEnd_4266408 < baseStart_4266408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266424 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_4266424 : Nat := 118140960795 + 4266424 * 2 ^ 59
def prefixEnd_4266424 : Nat := 4983230072969 + 3 ^ 40 * 4266424 * 2
def baseEnd_4266424 : Nat := 730242062625973610059693

theorem tailTrace_4266424 : CollatzResearch.WordTrace tailWord_4266424 prefixEnd_4266424 730242062625973610059693 := by
  unfold tailWord_4266424
  simp only [CollatzResearch.WordTrace]
  refine ⟨77804633547740985026871163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103739511396987980035828217 77804633547740985026871163)
  ·
    refine ⟨116706950321611477540306745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77804633547740985026871163 116706950321611477540306745)
    ·
      refine ⟨87530212741208608155230059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116706950321611477540306745 87530212741208608155230059)
      ·
        refine ⟨131295319111812912232845089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87530212741208608155230059 131295319111812912232845089)
        ·
          refine ⟨98471489333859684174633817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131295319111812912232845089 98471489333859684174633817)
          ·
            refine ⟨73853617000394763130975363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98471489333859684174633817 73853617000394763130975363)
            ·
              refine ⟨110780425500592144696463045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73853617000394763130975363 110780425500592144696463045)
              ·
                refine ⟨20771329781361027130586821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110780425500592144696463045 20771329781361027130586821)
                ·
                  refine ⟨3894624334005192586985029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20771329781361027130586821 3894624334005192586985029)
                  ·
                    refine ⟨730242062625973610059693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894624334005192586985029 730242062625973610059693)
                    ·
                      rfl

theorem cell23_4266424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_4266424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266424 prefixEnd_4266424 := by exact prefixLift 4266424
  have htrace : WordTrace (prefixWord ++ tailWord_4266424) baseStart_4266424 baseEnd_4266424 := by
    simpa [prefixWord, tailWord_4266424, baseEnd_4266424] using wordTrace_append hprefix tailTrace_4266424
  have hstable : (prefixWord ++ tailWord_4266424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266424).length < 2 ^ (prefixWord ++ tailWord_4266424).sum := by decide
  have hdescent : baseEnd_4266424 < baseStart_4266424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266425 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4266425 : Nat := 118140960795 + 4266425 * 2 ^ 59
def prefixEnd_4266425 : Nat := 4983230072969 + 3 ^ 40 * 4266425 * 2
def baseEnd_4266425 : Nat := 2190726701358575326266575

theorem tailTrace_4266425 : CollatzResearch.WordTrace tailWord_4266425 prefixEnd_4266425 2190726701358575326266575 := by
  unfold tailWord_4266425
  simp only [CollatzResearch.WordTrace]
  refine ⟨155609303568478347224528729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103739535712318898149685819 155609303568478347224528729)
  ·
    refine ⟨116706977676358760418396547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155609303568478347224528729 116706977676358760418396547)
    ·
      refine ⟨175060466514538140627594821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116706977676358760418396547 175060466514538140627594821)
      ·
        refine ⟨32823837471475901367674029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175060466514538140627594821 32823837471475901367674029)
        ·
          refine ⟨12308939051803463012877761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32823837471475901367674029 12308939051803463012877761)
          ·
            refine ⟨9231704288852597259658321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12308939051803463012877761 9231704288852597259658321)
            ·
              refine ⟨6923778216639447944743741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9231704288852597259658321 6923778216639447944743741)
              ·
                refine ⟨2596416831239792979278903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6923778216639447944743741 2596416831239792979278903)
                ·
                  refine ⟨3894625246859689468918355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596416831239792979278903 3894625246859689468918355)
                  ·
                    refine ⟨5841937870289534203377533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894625246859689468918355 5841937870289534203377533)
                    ·
                      refine ⟨2190726701358575326266575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5841937870289534203377533 2190726701358575326266575)
                      ·
                        rfl

theorem cell23_4266425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4266425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266425 prefixEnd_4266425 := by exact prefixLift 4266425
  have htrace : WordTrace (prefixWord ++ tailWord_4266425) baseStart_4266425 baseEnd_4266425 := by
    simpa [prefixWord, tailWord_4266425, baseEnd_4266425] using wordTrace_append hprefix tailTrace_4266425
  have hstable : (prefixWord ++ tailWord_4266425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266425).length < 2 ^ (prefixWord ++ tailWord_4266425).sum := by decide
  have hdescent : baseEnd_4266425 < baseStart_4266425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266428 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_4266428 : Nat := 118140960795 + 4266428 * 2 ^ 59
def prefixEnd_4266428 : Nat := 4983230072969 + 3 ^ 40 * 4266428 * 2
def baseEnd_4266428 : Nat := 730242747266846271509687

theorem tailTrace_4266428 : CollatzResearch.WordTrace tailWord_4266428 prefixEnd_4266428 730242747266846271509687 := by
  unfold tailWord_4266428
  simp only [CollatzResearch.WordTrace]
  refine ⟨77804706493733739368443969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103739608658311652491258625 77804706493733739368443969)
  ·
    refine ⟨58353529870300304526332977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77804706493733739368443969 58353529870300304526332977)
    ·
      refine ⟨43765147402725228394749733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58353529870300304526332977 43765147402725228394749733)
      ·
        refine ⟨8205965138010980324015575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43765147402725228394749733 8205965138010980324015575)
        ·
          refine ⟨12308947707016470486023363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205965138010980324015575 12308947707016470486023363)
          ·
            refine ⟨18463421560524705729035045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12308947707016470486023363 18463421560524705729035045)
            ·
              refine ⟨3461891542598382324194071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18463421560524705729035045 3461891542598382324194071)
              ·
                refine ⟨5192837313897573486291107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461891542598382324194071 5192837313897573486291107)
                ·
                  refine ⟨7789255970846360229436661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192837313897573486291107 7789255970846360229436661)
                  ·
                    refine ⟨730242747266846271509687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7789255970846360229436661 730242747266846271509687)
                    ·
                      rfl

theorem cell23_4266428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_4266428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266428 prefixEnd_4266428 := by exact prefixLift 4266428
  have htrace : WordTrace (prefixWord ++ tailWord_4266428) baseStart_4266428 baseEnd_4266428 := by
    simpa [prefixWord, tailWord_4266428, baseEnd_4266428] using wordTrace_append hprefix tailTrace_4266428
  have hstable : (prefixWord ++ tailWord_4266428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266428).length < 2 ^ (prefixWord ++ tailWord_4266428).sum := by decide
  have hdescent : baseEnd_4266428 < baseStart_4266428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266441 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_4266441 : Nat := 118140960795 + 4266441 * 2 ^ 59
def prefixEnd_4266441 : Nat := 4983230072969 + 3 ^ 40 * 4266441 * 2
def baseEnd_4266441 : Nat := 730244972349682421222167

theorem tailTrace_4266441 : CollatzResearch.WordTrace tailWord_4266441 prefixEnd_4266441 730244972349682421222167 := by
  unfold tailWord_4266441
  simp only [CollatzResearch.WordTrace]
  refine ⟨155609887136420381957111177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103739924757613587971407451 155609887136420381957111177)
  ·
    refine ⟨116707415352315286467833383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155609887136420381957111177 116707415352315286467833383)
    ·
      refine ⟨175061123028472929701750075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116707415352315286467833383 175061123028472929701750075)
      ·
        refine ⟨262591684542709394552625113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175061123028472929701750075 262591684542709394552625113)
        ·
          refine ⟨196943763407032045914468835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262591684542709394552625113 196943763407032045914468835)
          ·
            refine ⟨295415645110548068871703253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196943763407032045914468835 295415645110548068871703253)
            ·
              refine ⟨6923804182278470364180545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 295415645110548068871703253 6923804182278470364180545)
              ·
                refine ⟨5192853136708852773135409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923804182278470364180545 5192853136708852773135409)
                ·
                  refine ⟨3894639852531639579851557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192853136708852773135409 3894639852531639579851557)
                  ·
                    refine ⟨730244972349682421222167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894639852531639579851557 730244972349682421222167)
                    ·
                      rfl

theorem cell23_4266441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_4266441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266441 prefixEnd_4266441 := by exact prefixLift 4266441
  have htrace : WordTrace (prefixWord ++ tailWord_4266441) baseStart_4266441 baseEnd_4266441 := by
    simpa [prefixWord, tailWord_4266441, baseEnd_4266441] using wordTrace_append hprefix tailTrace_4266441
  have hstable : (prefixWord ++ tailWord_4266441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266441).length < 2 ^ (prefixWord ++ tailWord_4266441).sum := by decide
  have hdescent : baseEnd_4266441 < baseStart_4266441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_4266447 : Nat := 118140960795 + 4266447 * 2 ^ 59
def prefixEnd_4266447 : Nat := 4983230072969 + 3 ^ 40 * 4266447 * 2
def baseEnd_4266447 : Nat := 2190737997932974240191473

theorem tailTrace_4266447 : CollatzResearch.WordTrace tailWord_4266447 prefixEnd_4266447 2190737997932974240191473 := by
  unfold tailWord_4266447
  simp only [CollatzResearch.WordTrace]
  refine ⟨155610105974398644981829595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103740070649599096654553063 155610105974398644981829595)
  ·
    refine ⟨233415158961597967472744393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155610105974398644981829595 233415158961597967472744393)
    ·
      refine ⟨175061369221198475604558295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233415158961597967472744393 175061369221198475604558295)
      ·
        refine ⟨262592053831797713406837443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175061369221198475604558295 262592053831797713406837443)
        ·
          refine ⟨393888080747696570110256165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262592053831797713406837443 393888080747696570110256165)
          ·
            refine ⟨73854015140193106895673031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393888080747696570110256165 73854015140193106895673031)
            ·
              refine ⟨110781022710289660343509547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73854015140193106895673031 110781022710289660343509547)
              ·
                refine ⟨166171534065434490515264321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110781022710289660343509547 166171534065434490515264321)
                ·
                  refine ⟨124628650549075867886448241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166171534065434490515264321 124628650549075867886448241)
                  ·
                    refine ⟨93471487911806900914836181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124628650549075867886448241 93471487911806900914836181)
                    ·
                      refine ⟨2190737997932974240191473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93471487911806900914836181 2190737997932974240191473)
                      ·
                        rfl

theorem cell23_4266447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_4266447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266447 prefixEnd_4266447 := by exact prefixLift 4266447
  have htrace : WordTrace (prefixWord ++ tailWord_4266447) baseStart_4266447 baseEnd_4266447 := by
    simpa [prefixWord, tailWord_4266447, baseEnd_4266447] using wordTrace_append hprefix tailTrace_4266447
  have hstable : (prefixWord ++ tailWord_4266447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266447).length < 2 ^ (prefixWord ++ tailWord_4266447).sum := by decide
  have hdescent : baseEnd_4266447 < baseStart_4266447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266458 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_4266458 : Nat := 118140960795 + 4266458 * 2 ^ 59
def prefixEnd_4266458 : Nat := 4983230072969 + 3 ^ 40 * 4266458 * 2
def baseEnd_4266458 : Nat := 730247882073391232384641

theorem tailTrace_4266458 : CollatzResearch.WordTrace tailWord_4266458 prefixEnd_4266458 730247882073391232384641 := by
  unfold tailWord_4266458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38902626794339698465120007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103740338118239195906986685 38902626794339698465120007)
  ·
    refine ⟨58353940191509547697680011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38902626794339698465120007 58353940191509547697680011)
    ·
      refine ⟨87530910287264321546520017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58353940191509547697680011 87530910287264321546520017)
      ·
        refine ⟨65648182715448241159890013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87530910287264321546520017 65648182715448241159890013)
        ·
          refine ⟨24618068518293090434958755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65648182715448241159890013 24618068518293090434958755)
          ·
            refine ⟨36927102777439635652438133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24618068518293090434958755 36927102777439635652438133)
            ·
              refine ⟨3461915885384965842416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36927102777439635652438133 3461915885384965842416075)
              ·
                refine ⟨5192873828077448763624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461915885384965842416075 5192873828077448763624113)
                ·
                  refine ⟨3894655371058086572718085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192873828077448763624113 3894655371058086572718085)
                  ·
                    refine ⟨730247882073391232384641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894655371058086572718085 730247882073391232384641)
                    ·
                      rfl

theorem cell23_4266458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_4266458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266458 prefixEnd_4266458 := by exact prefixLift 4266458
  have htrace : WordTrace (prefixWord ++ tailWord_4266458) baseStart_4266458 baseEnd_4266458 := by
    simpa [prefixWord, tailWord_4266458, baseEnd_4266458] using wordTrace_append hprefix tailTrace_4266458
  have hstable : (prefixWord ++ tailWord_4266458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266458).length < 2 ^ (prefixWord ++ tailWord_4266458).sum := by decide
  have hdescent : baseEnd_4266458 < baseStart_4266458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266481 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_4266481 : Nat := 118140960795 + 4266481 * 2 ^ 59
def prefixEnd_4266481 : Nat := 4983230072969 + 3 ^ 40 * 4266481 * 2
def baseEnd_4266481 : Nat := 2190755456275227107166317

theorem tailTrace_4266481 : CollatzResearch.WordTrace tailWord_4266481 prefixEnd_4266481 2190755456275227107166317 := by
  unfold tailWord_4266481
  simp only [CollatzResearch.WordTrace]
  refine ⟨155611346056275468788567297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103740897370850312525711531 155611346056275468788567297)
  ·
    refine ⟨116708509542206601591425473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155611346056275468788567297 116708509542206601591425473)
    ·
      refine ⟨87531382156654951193569105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116708509542206601591425473 87531382156654951193569105)
      ·
        refine ⟨65648536617491213395176829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87531382156654951193569105 65648536617491213395176829)
        ·
          refine ⟨24618201231559205023191311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65648536617491213395176829 24618201231559205023191311)
          ·
            refine ⟨36927301847338807534786967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24618201231559205023191311 36927301847338807534786967)
            ·
              refine ⟨55390952771008211302180451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36927301847338807534786967 55390952771008211302180451)
              ·
                refine ⟨83086429156512316953270677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55390952771008211302180451 83086429156512316953270677)
                ·
                  refine ⟨3894676366711514857184563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83086429156512316953270677 3894676366711514857184563)
                  ·
                    refine ⟨5842014550067272285776845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894676366711514857184563 5842014550067272285776845)
                    ·
                      refine ⟨2190755456275227107166317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5842014550067272285776845 2190755456275227107166317)
                      ·
                        rfl

theorem cell23_4266481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_4266481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266481 prefixEnd_4266481 := by exact prefixLift 4266481
  have htrace : WordTrace (prefixWord ++ tailWord_4266481) baseStart_4266481 baseEnd_4266481 := by
    simpa [prefixWord, tailWord_4266481, baseEnd_4266481] using wordTrace_append hprefix tailTrace_4266481
  have hstable : (prefixWord ++ tailWord_4266481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266481).length < 2 ^ (prefixWord ++ tailWord_4266481).sum := by decide
  have hdescent : baseEnd_4266481 < baseStart_4266481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266504 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_4266504 : Nat := 118140960795 + 4266504 * 2 ^ 59
def prefixEnd_4266504 : Nat := 4983230072969 + 3 ^ 40 * 4266504 * 2
def baseEnd_4266504 : Nat := 2190767266330280517178711

theorem tailTrace_4266504 : CollatzResearch.WordTrace tailWord_4266504 prefixEnd_4266504 2190767266330280517178711 := by
  unfold tailWord_4266504
  simp only [CollatzResearch.WordTrace]
  refine ⟨77806092467596071858327283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103741456623461429144436377 77806092467596071858327283)
  ·
    refine ⟨116709138701394107787490925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77806092467596071858327283 116709138701394107787490925)
    ·
      refine ⟨43765927013022790420309097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116709138701394107787490925 43765927013022790420309097)
      ·
        refine ⟨32824445259767092815231823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43765927013022790420309097 32824445259767092815231823)
        ·
          refine ⟨49236667889650639222847735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32824445259767092815231823 49236667889650639222847735)
          ·
            refine ⟨73855001834475958834271603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49236667889650639222847735 73855001834475958834271603)
            ·
              refine ⟨110782502751713938251407405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73855001834475958834271603 110782502751713938251407405)
              ·
                refine ⟨41543438531892726844277777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110782502751713938251407405 41543438531892726844277777)
                ·
                  refine ⟨31157578898919545133208333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41543438531892726844277777 31157578898919545133208333)
                  ·
                    refine ⟨11684092087094829424953125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31157578898919545133208333 11684092087094829424953125)
                    ·
                      refine ⟨2190767266330280517178711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11684092087094829424953125 2190767266330280517178711)
                      ·
                        rfl

theorem cell23_4266504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_4266504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266504 prefixEnd_4266504 := by exact prefixLift 4266504
  have htrace : WordTrace (prefixWord ++ tailWord_4266504) baseStart_4266504 baseEnd_4266504 := by
    simpa [prefixWord, tailWord_4266504, baseEnd_4266504] using wordTrace_append hprefix tailTrace_4266504
  have hstable : (prefixWord ++ tailWord_4266504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266504).length < 2 ^ (prefixWord ++ tailWord_4266504).sum := by decide
  have hdescent : baseEnd_4266504 < baseStart_4266504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266509 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4266509 : Nat := 118140960795 + 4266509 * 2 ^ 59
def prefixEnd_4266509 : Nat := 4983230072969 + 3 ^ 40 * 4266509 * 2
def baseEnd_4266509 : Nat := 730256611244517665872063

theorem tailTrace_4266509 : CollatzResearch.WordTrace tailWord_4266509 prefixEnd_4266509 730256611244517665872063 := by
  unfold tailWord_4266509
  simp only [CollatzResearch.WordTrace]
  refine ⟨155612367300174029570586581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103741578200116019713724387 155612367300174029570586581)
  ·
    refine ⟨3647164858597828818060623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 155612367300174029570586581 3647164858597828818060623)
    ·
      refine ⟨5470747287896743227090935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647164858597828818060623 5470747287896743227090935)
      ·
        refine ⟨8206120931845114840636403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470747287896743227090935 8206120931845114840636403)
        ·
          refine ⟨12309181397767672260954605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8206120931845114840636403 12309181397767672260954605)
          ·
            refine ⟨4615943024162877097857977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12309181397767672260954605 4615943024162877097857977)
            ·
              refine ⟨3461957268122157823393483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615943024162877097857977 3461957268122157823393483)
              ·
                refine ⟨5192935902183236735090225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461957268122157823393483 5192935902183236735090225)
                ·
                  refine ⟨3894701926637427551317669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192935902183236735090225 3894701926637427551317669)
                  ·
                    refine ⟨730256611244517665872063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894701926637427551317669 730256611244517665872063)
                    ·
                      rfl

theorem cell23_4266509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4266509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266509 prefixEnd_4266509 := by exact prefixLift 4266509
  have htrace : WordTrace (prefixWord ++ tailWord_4266509) baseStart_4266509 baseEnd_4266509 := by
    simpa [prefixWord, tailWord_4266509, baseEnd_4266509] using wordTrace_append hprefix tailTrace_4266509
  have hstable : (prefixWord ++ tailWord_4266509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266509).length < 2 ^ (prefixWord ++ tailWord_4266509).sum := by decide
  have hdescent : baseEnd_4266509 < baseStart_4266509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266525 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_4266525 : Nat := 118140960795 + 4266525 * 2 ^ 59
def prefixEnd_4266525 : Nat := 4983230072969 + 3 ^ 40 * 4266525 * 2
def baseEnd_4266525 : Nat := 2190778049424024935016115

theorem tailTrace_4266525 : CollatzResearch.WordTrace tailWord_4266525 prefixEnd_4266525 2190778049424024935016115 := by
  unfold tailWord_4266525
  simp only [CollatzResearch.WordTrace]
  refine ⟨155612950868116064303169029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103741967245410709535446019 155612950868116064303169029)
  ·
    refine ⟨29177428287771762056844193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155612950868116064303169029 29177428287771762056844193)
    ·
      refine ⟨21883071215828821542633145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29177428287771762056844193 21883071215828821542633145)
      ·
        refine ⟨16412303411871616156974859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21883071215828821542633145 16412303411871616156974859)
        ·
          refine ⟨24618455117807424235462289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412303411871616156974859 24618455117807424235462289)
          ·
            refine ⟨18463841338355568176596717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24618455117807424235462289 18463841338355568176596717)
            ·
              refine ⟨6923940501883338066223769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18463841338355568176596717 6923940501883338066223769)
              ·
                refine ⟨5192955376412503549667827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923940501883338066223769 5192955376412503549667827)
                ·
                  refine ⟨7789433064618755324501741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192955376412503549667827 7789433064618755324501741)
                  ·
                    refine ⟨2921037399232033246688153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7789433064618755324501741 2921037399232033246688153)
                    ·
                      refine ⟨2190778049424024935016115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921037399232033246688153 2190778049424024935016115)
                      ·
                        rfl

theorem cell23_4266525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_4266525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266525 prefixEnd_4266525 := by exact prefixLift 4266525
  have htrace : WordTrace (prefixWord ++ tailWord_4266525) baseStart_4266525 baseEnd_4266525 := by
    simpa [prefixWord, tailWord_4266525, baseEnd_4266525] using wordTrace_append hprefix tailTrace_4266525
  have hstable : (prefixWord ++ tailWord_4266525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266525).length < 2 ^ (prefixWord ++ tailWord_4266525).sum := by decide
  have hdescent : baseEnd_4266525 < baseStart_4266525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266538 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4266538 : Nat := 118140960795 + 4266538 * 2 ^ 59
def prefixEnd_4266538 : Nat := 4983230072969 + 3 ^ 40 * 4266538 * 2
def baseEnd_4266538 : Nat := 2190784724672533384153555

theorem tailTrace_4266538 : CollatzResearch.WordTrace tailWord_4266538 prefixEnd_4266538 2190784724672533384153555 := by
  unfold tailWord_4266538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38903356254267241880848067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103742283344712645015594845 38903356254267241880848067)
  ·
    refine ⟨58355034381400862821272101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38903356254267241880848067 58355034381400862821272101)
    ·
      refine ⟨10941568946512661778988519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58355034381400862821272101 10941568946512661778988519)
      ·
        refine ⟨16412353419768992668482779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10941568946512661778988519 16412353419768992668482779)
        ·
          refine ⟨24618530129653489002724169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412353419768992668482779 24618530129653489002724169)
          ·
            refine ⟨18463897597240116752043127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24618530129653489002724169 18463897597240116752043127)
            ·
              refine ⟨27695846395860175128064691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18463897597240116752043127 27695846395860175128064691)
              ·
                refine ⟨41543769593790262692097037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27695846395860175128064691 41543769593790262692097037)
                ·
                  refine ⟨15578913597671348509536389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41543769593790262692097037 15578913597671348509536389)
                  ·
                    refine ⟨2921046299563377845538073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15578913597671348509536389 2921046299563377845538073)
                    ·
                      refine ⟨2190784724672533384153555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921046299563377845538073 2190784724672533384153555)
                      ·
                        rfl

theorem cell23_4266538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4266538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266538 prefixEnd_4266538 := by exact prefixLift 4266538
  have htrace : WordTrace (prefixWord ++ tailWord_4266538) baseStart_4266538 baseEnd_4266538 := by
    simpa [prefixWord, tailWord_4266538, baseEnd_4266538] using wordTrace_append hprefix tailTrace_4266538
  have hstable : (prefixWord ++ tailWord_4266538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266538).length < 2 ^ (prefixWord ++ tailWord_4266538).sum := by decide
  have hdescent : baseEnd_4266538 < baseStart_4266538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266584 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4266584 : Nat := 118140960795 + 4266584 * 2 ^ 59
def prefixEnd_4266584 : Nat := 4983230072969 + 3 ^ 40 * 4266584 * 2
def baseEnd_4266584 : Nat := 2190808344782640204178343

theorem tailTrace_4266584 : CollatzResearch.WordTrace tailWord_4266584 prefixEnd_4266584 2190808344782640204178343 := by
  unfold tailWord_4266584
  simp only [CollatzResearch.WordTrace]
  refine ⟨77807551387451158689783403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103743401849934878253044537 77807551387451158689783403)
  ·
    refine ⟨116711327081176738034675105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77807551387451158689783403 116711327081176738034675105)
    ·
      refine ⟨87533495310882553526006329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116711327081176738034675105 87533495310882553526006329)
      ·
        refine ⟨65650121483161915144504747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87533495310882553526006329 65650121483161915144504747)
        ·
          refine ⟨98475182224742872716757121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65650121483161915144504747 98475182224742872716757121)
          ·
            refine ⟨73856386668557154537567841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98475182224742872716757121 73856386668557154537567841)
            ·
              refine ⟨55392290001417865903175881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73856386668557154537567841 55392290001417865903175881)
              ·
                refine ⟨41544217501063399427381911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55392290001417865903175881 41544217501063399427381911)
                ·
                  refine ⟨62316326251595099141072867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41544217501063399427381911 62316326251595099141072867)
                  ·
                    refine ⟨93474489377392648711609301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62316326251595099141072867 93474489377392648711609301)
                    ·
                      refine ⟨2190808344782640204178343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93474489377392648711609301 2190808344782640204178343)
                      ·
                        rfl

theorem cell23_4266584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4266584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266584 prefixEnd_4266584 := by exact prefixLift 4266584
  have htrace : WordTrace (prefixWord ++ tailWord_4266584) baseStart_4266584 baseEnd_4266584 := by
    simpa [prefixWord, tailWord_4266584, baseEnd_4266584] using wordTrace_append hprefix tailTrace_4266584
  have hstable : (prefixWord ++ tailWord_4266584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266584).length < 2 ^ (prefixWord ++ tailWord_4266584).sum := by decide
  have hdescent : baseEnd_4266584 < baseStart_4266584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266631 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_4266631 : Nat := 118140960795 + 4266631 * 2 ^ 59
def prefixEnd_4266631 : Nat := 4983230072969 + 3 ^ 40 * 4266631 * 2
def baseEnd_4266631 : Nat := 2190832478373401520290627

theorem tailTrace_4266631 : CollatzResearch.WordTrace tailWord_4266631 prefixEnd_4266631 2190832478373401520290627 := by
  unfold tailWord_4266631
  simp only [CollatzResearch.WordTrace]
  refine ⟨155616817005732044406527747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103744544670488029604351831 155616817005732044406527747)
  ·
    refine ⟨233425225508598066609791621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155616817005732044406527747 233425225508598066609791621)
    ·
      refine ⟨43767229782862137489335929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233425225508598066609791621 43767229782862137489335929)
      ·
        refine ⟨32825422337146603117001947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43767229782862137489335929 32825422337146603117001947)
        ·
          refine ⟨49238133505719904675502921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32825422337146603117001947 49238133505719904675502921)
          ·
            refine ⟨36928600129289928506627191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49238133505719904675502921 36928600129289928506627191)
            ·
              refine ⟨55392900193934892759940787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36928600129289928506627191 55392900193934892759940787)
              ·
                refine ⟨83089350290902339139911181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55392900193934892759940787 83089350290902339139911181)
                ·
                  refine ⟨31158506359088377177466693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83089350290902339139911181 31158506359088377177466693)
                  ·
                    refine ⟨5842219942329070720775005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31158506359088377177466693 5842219942329070720775005)
                    ·
                      refine ⟨2190832478373401520290627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5842219942329070720775005 2190832478373401520290627)
                      ·
                        rfl

theorem cell23_4266631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_4266631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266631 prefixEnd_4266631 := by exact prefixLift 4266631
  have htrace : WordTrace (prefixWord ++ tailWord_4266631) baseStart_4266631 baseEnd_4266631 := by
    simpa [prefixWord, tailWord_4266631, baseEnd_4266631] using wordTrace_append hprefix tailTrace_4266631
  have hstable : (prefixWord ++ tailWord_4266631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266631).length < 2 ^ (prefixWord ++ tailWord_4266631).sum := by decide
  have hdescent : baseEnd_4266631 < baseStart_4266631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266638 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_4266638 : Nat := 118140960795 + 4266638 * 2 ^ 59
def prefixEnd_4266638 : Nat := 4983230072969 + 3 ^ 40 * 4266638 * 2
def baseEnd_4266638 : Nat := 730278690912660997634365

theorem tailTrace_4266638 : CollatzResearch.WordTrace tailWord_4266638 prefixEnd_4266638 730278690912660997634365 := by
  unfold tailWord_4266638
  simp only [CollatzResearch.WordTrace]
  refine ⟨19452134039588335575254071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103744714877804456401355045 19452134039588335575254071)
  ·
    refine ⟨29178201059382503362881107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19452134039588335575254071 29178201059382503362881107)
    ·
      refine ⟨43767301589073755044321661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29178201059382503362881107 43767301589073755044321661)
      ·
        refine ⟨16412738095902658141620623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43767301589073755044321661 16412738095902658141620623)
        ·
          refine ⟨24619107143853987212430935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412738095902658141620623 24619107143853987212430935)
          ·
            refine ⟨36928660715780980818646403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24619107143853987212430935 36928660715780980818646403)
            ·
              refine ⟨55392991073671471227969605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36928660715780980818646403 55392991073671471227969605)
              ·
                refine ⟨10386185826313400855244301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55392991073671471227969605 10386185826313400855244301)
                ·
                  refine ⟨3894819684867525320716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10386185826313400855244301 3894819684867525320716613)
                  ·
                    refine ⟨730278690912660997634365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894819684867525320716613 730278690912660997634365)
                    ·
                      rfl

theorem cell23_4266638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_4266638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266638 prefixEnd_4266638 := by exact prefixLift 4266638
  have htrace : WordTrace (prefixWord ++ tailWord_4266638) baseStart_4266638 baseEnd_4266638 := by
    simpa [prefixWord, tailWord_4266638, baseEnd_4266638] using wordTrace_append hprefix tailTrace_4266638
  have hstable : (prefixWord ++ tailWord_4266638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266638).length < 2 ^ (prefixWord ++ tailWord_4266638).sum := by decide
  have hdescent : baseEnd_4266638 < baseStart_4266638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266648 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4266648 : Nat := 118140960795 + 4266648 * 2 ^ 59
def prefixEnd_4266648 : Nat := 4983230072969 + 3 ^ 40 * 4266648 * 2
def baseEnd_4266648 : Nat := 2190841207544527953778049

theorem tailTrace_4266648 : CollatzResearch.WordTrace tailWord_4266648 prefixEnd_4266648 2190841207544527953778049 := by
  unfold tailWord_4266648
  simp only [CollatzResearch.WordTrace]
  refine ⟨77808718523335228154948299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103744958031113637539931065 77808718523335228154948299)
  ·
    refine ⟨116713077785002842232422449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77808718523335228154948299 116713077785002842232422449)
    ·
      refine ⟨87534808338752131674316837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116713077785002842232422449 87534808338752131674316837)
      ·
        refine ⟨16412776563516024688934407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87534808338752131674316837 16412776563516024688934407)
        ·
          refine ⟨24619164845274037033401611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412776563516024688934407 24619164845274037033401611)
          ·
            refine ⟨36928747267911055550102417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24619164845274037033401611 36928747267911055550102417)
            ·
              refine ⟨27696560450933291662576813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36928747267911055550102417 27696560450933291662576813)
              ·
                refine ⟨10386210169099984373466305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27696560450933291662576813 10386210169099984373466305)
                ·
                  refine ⟨7789657626824988280099729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10386210169099984373466305 7789657626824988280099729)
                  ·
                    refine ⟨5842243220118741210074797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7789657626824988280099729 5842243220118741210074797)
                    ·
                      refine ⟨2190841207544527953778049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5842243220118741210074797 2190841207544527953778049)
                      ·
                        rfl

theorem cell23_4266648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4266648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266648 prefixEnd_4266648 := by exact prefixLift 4266648
  have htrace : WordTrace (prefixWord ++ tailWord_4266648) baseStart_4266648 baseEnd_4266648 := by
    simpa [prefixWord, tailWord_4266648, baseEnd_4266648] using wordTrace_append hprefix tailTrace_4266648
  have hstable : (prefixWord ++ tailWord_4266648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266648).length < 2 ^ (prefixWord ++ tailWord_4266648).sum := by decide
  have hdescent : baseEnd_4266648 < baseStart_4266648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266681 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_4266681 : Nat := 118140960795 + 4266681 * 2 ^ 59
def prefixEnd_4266681 : Nat := 4983230072969 + 3 ^ 40 * 4266681 * 2
def baseEnd_4266681 : Nat := 730286050802042108221799

theorem tailTrace_4266681 : CollatzResearch.WordTrace tailWord_4266681 prefixEnd_4266681 730286050802042108221799 := by
  unfold tailWord_4266681
  simp only [CollatzResearch.WordTrace]
  refine ⟨155618640655550902945847897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103745760437033935297231931 155618640655550902945847897)
  ·
    refine ⟨116713980491663177209385923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155618640655550902945847897 116713980491663177209385923)
    ·
      refine ⟨175070970737494765814078885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116713980491663177209385923 175070970737494765814078885)
      ·
        refine ⟨32825807013280268590139791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175070970737494765814078885 32825807013280268590139791)
        ·
          refine ⟨49238710519920402885209687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32825807013280268590139791 49238710519920402885209687)
          ·
            refine ⟨73858065779880604327814531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49238710519920402885209687 73858065779880604327814531)
            ·
              refine ⟨110787098669820906491721797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73858065779880604327814531 110787098669820906491721797)
              ·
                refine ⟨20772581000591419967197837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110787098669820906491721797 20772581000591419967197837)
                ·
                  refine ⟨7789717875221782487699189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20772581000591419967197837 7789717875221782487699189)
                  ·
                    refine ⟨730286050802042108221799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7789717875221782487699189 730286050802042108221799)
                    ·
                      rfl

theorem cell23_4266681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_4266681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266681 prefixEnd_4266681 := by exact prefixLift 4266681
  have htrace : WordTrace (prefixWord ++ tailWord_4266681) baseStart_4266681 baseEnd_4266681 := by
    simpa [prefixWord, tailWord_4266681, baseEnd_4266681] using wordTrace_append hprefix tailTrace_4266681
  have hstable : (prefixWord ++ tailWord_4266681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266681).length < 2 ^ (prefixWord ++ tailWord_4266681).sum := by decide
  have hdescent : baseEnd_4266681 < baseStart_4266681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266685 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 6]
def baseStart_4266685 : Nat := 118140960795 + 4266685 * 2 ^ 59
def prefixEnd_4266685 : Nat := 4983230072969 + 3 ^ 40 * 4266685 * 2
def baseEnd_4266685 : Nat := 243428911814304923223931

theorem tailTrace_4266685 : CollatzResearch.WordTrace tailWord_4266685 prefixEnd_4266685 243428911814304923223931 := by
  unfold tailWord_4266685
  simp only [CollatzResearch.WordTrace]
  refine ⟨155618786547536411628993509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103745857698357607752662339 155618786547536411628993509)
  ·
    refine ⟨29178522477663077180436283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155618786547536411628993509 29178522477663077180436283)
    ·
      refine ⟨43767783716494615770654425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29178522477663077180436283 43767783716494615770654425)
      ·
        refine ⟨32825837787370961827990819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43767783716494615770654425 32825837787370961827990819)
        ·
          refine ⟨49238756681056442741986229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32825837787370961827990819 49238756681056442741986229)
          ·
            refine ⟨4616133438849041507061209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49238756681056442741986229 4616133438849041507061209)
            ·
              refine ⟨3462100079136781130295907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4616133438849041507061209 3462100079136781130295907)
              ·
                refine ⟨5193150118705171695443861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462100079136781130295907 5193150118705171695443861)
                ·
                  refine ⟨243428911814304923223931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5193150118705171695443861 243428911814304923223931)
                  ·
                    rfl

theorem cell23_4266685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_4266685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266685 prefixEnd_4266685 := by exact prefixLift 4266685
  have htrace : WordTrace (prefixWord ++ tailWord_4266685) baseStart_4266685 baseEnd_4266685 := by
    simpa [prefixWord, tailWord_4266685, baseEnd_4266685] using wordTrace_append hprefix tailTrace_4266685
  have hstable : (prefixWord ++ tailWord_4266685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266685).length < 2 ^ (prefixWord ++ tailWord_4266685).sum := by decide
  have hdescent : baseEnd_4266685 < baseStart_4266685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266698 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4266698 : Nat := 118140960795 + 4266698 * 2 ^ 59
def prefixEnd_4266698 : Nat := 4983230072969 + 3 ^ 40 * 4266698 * 2
def baseEnd_4266698 : Nat := 730288960525750919384273

theorem tailTrace_4266698 : CollatzResearch.WordTrace tailWord_4266698 prefixEnd_4266698 730288960525750919384273 := by
  unfold tailWord_4266698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38904815174122328712304187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103746173797659543232811165 38904815174122328712304187)
  ·
    refine ⟨58357222761183493068456281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38904815174122328712304187 58357222761183493068456281)
    ·
      refine ⟨43767917070887619801342211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58357222761183493068456281 43767917070887619801342211)
      ·
        refine ⟨65651875606331429702013317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43767917070887619801342211 65651875606331429702013317)
        ·
          refine ⟨12309726676187143069127497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65651875606331429702013317 12309726676187143069127497)
          ·
            refine ⟨9232295007140357301845623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12309726676187143069127497 9232295007140357301845623)
            ·
              refine ⟨13848442510710535952768435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9232295007140357301845623 13848442510710535952768435)
              ·
                refine ⟨20772663766065803929152653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13848442510710535952768435 20772663766065803929152653)
                ·
                  refine ⟨7789748912274676473432245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20772663766065803929152653 7789748912274676473432245)
                  ·
                    refine ⟨730288960525750919384273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7789748912274676473432245 730288960525750919384273)
                    ·
                      rfl

theorem cell23_4266698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4266698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266698 prefixEnd_4266698 := by exact prefixLift 4266698
  have htrace : WordTrace (prefixWord ++ tailWord_4266698) baseStart_4266698 baseEnd_4266698 := by
    simpa [prefixWord, tailWord_4266698, baseEnd_4266698] using wordTrace_append hprefix tailTrace_4266698
  have hstable : (prefixWord ++ tailWord_4266698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266698).length < 2 ^ (prefixWord ++ tailWord_4266698).sum := by decide
  have hdescent : baseEnd_4266698 < baseStart_4266698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266705 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_4266705 : Nat := 118140960795 + 4266705 * 2 ^ 59
def prefixEnd_4266705 : Nat := 4983230072969 + 3 ^ 40 * 4266705 * 2
def baseEnd_4266705 : Nat := 2190870475941834230765287

theorem tailTrace_4266705 : CollatzResearch.WordTrace tailWord_4266705 prefixEnd_4266705 2190870475941834230765287 := by
  unfold tailWord_4266705
  simp only [CollatzResearch.WordTrace]
  refine ⟨155619516007463955044721569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103746344004975970029814379 155619516007463955044721569)
  ·
    refine ⟨116714637005597966283541177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155619516007463955044721569 116714637005597966283541177)
    ·
      refine ⟨87535977754198474712655883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116714637005597966283541177 87535977754198474712655883)
      ·
        refine ⟨131303966631297712068983825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87535977754198474712655883 131303966631297712068983825)
        ·
          refine ⟨98477974973473284051737869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131303966631297712068983825 98477974973473284051737869)
          ·
            refine ⟨36929240615052481519401701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98477974973473284051737869 36929240615052481519401701)
            ·
              refine ⟨6924232615322340284887819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36929240615052481519401701 6924232615322340284887819)
              ·
                refine ⟨10386348922983510427331729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924232615322340284887819 10386348922983510427331729)
                ·
                  refine ⟨7789761692237632820498797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10386348922983510427331729 7789761692237632820498797)
                  ·
                    refine ⟨2921160634589112307687049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7789761692237632820498797 2921160634589112307687049)
                    ·
                      refine ⟨2190870475941834230765287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921160634589112307687049 2190870475941834230765287)
                      ·
                        rfl

theorem cell23_4266705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_4266705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266705 prefixEnd_4266705 := by exact prefixLift 4266705
  have htrace : WordTrace (prefixWord ++ tailWord_4266705) baseStart_4266705 baseEnd_4266705 := by
    simpa [prefixWord, tailWord_4266705, baseEnd_4266705] using wordTrace_append hprefix tailTrace_4266705
  have hstable : (prefixWord ++ tailWord_4266705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266705).length < 2 ^ (prefixWord ++ tailWord_4266705).sum := by decide
  have hdescent : baseEnd_4266705 < baseStart_4266705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266711 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 6]
def baseStart_4266711 : Nat := 118140960795 + 4266711 * 2 ^ 59
def prefixEnd_4266711 : Nat := 4983230072969 + 3 ^ 40 * 4266711 * 2
def baseEnd_4266711 : Nat := 730291185608587069096753

theorem tailTrace_4266711 : CollatzResearch.WordTrace tailWord_4266711 prefixEnd_4266711 730291185608587069096753 := by
  unfold tailWord_4266711
  simp only [CollatzResearch.WordTrace]
  refine ⟨155619734845442218069439987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103746489896961478712959991 155619734845442218069439987)
  ·
    refine ⟨233429602268163327104159981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155619734845442218069439987 233429602268163327104159981)
    ·
      refine ⟨87536100850561247664059993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233429602268163327104159981 87536100850561247664059993)
      ·
        refine ⟨65652075637920935748044995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87536100850561247664059993 65652075637920935748044995)
        ·
          refine ⟨98478113456881403622067493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65652075637920935748044995 98478113456881403622067493)
          ·
            refine ⟨18464646273165263179137655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98478113456881403622067493 18464646273165263179137655)
            ·
              refine ⟨27696969409747894768706483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18464646273165263179137655 27696969409747894768706483)
              ·
                refine ⟨41545454114621842153059725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27696969409747894768706483 41545454114621842153059725)
                ·
                  refine ⟨15579545292983190807397397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41545454114621842153059725 15579545292983190807397397)
                  ·
                    refine ⟨730291185608587069096753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15579545292983190807397397 730291185608587069096753)
                    ·
                      rfl

theorem cell23_4266711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_4266711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266711 prefixEnd_4266711 := by exact prefixLift 4266711
  have htrace : WordTrace (prefixWord ++ tailWord_4266711) baseStart_4266711 baseEnd_4266711 := by
    simpa [prefixWord, tailWord_4266711, baseEnd_4266711] using wordTrace_append hprefix tailTrace_4266711
  have hstable : (prefixWord ++ tailWord_4266711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266711).length < 2 ^ (prefixWord ++ tailWord_4266711).sum := by decide
  have hdescent : baseEnd_4266711 < baseStart_4266711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266731 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_4266731 : Nat := 118140960795 + 4266731 * 2 ^ 59
def prefixEnd_4266731 : Nat := 4983230072969 + 3 ^ 40 * 4266731 * 2
def baseEnd_4266731 : Nat := 2190883826438851129040167

theorem tailTrace_4266731 : CollatzResearch.WordTrace tailWord_4266731 prefixEnd_4266731 2190883826438851129040167 := by
  unfold tailWord_4266731
  simp only [CollatzResearch.WordTrace]
  refine ⟨155620464305369761485168047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103746976203579840990112031 155620464305369761485168047)
  ·
    refine ⟨233430696458054642227752071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155620464305369761485168047 233430696458054642227752071)
    ·
      refine ⟨350146044687081963341628107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233430696458054642227752071 350146044687081963341628107)
      ·
        refine ⟨525219067030622945012442161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350146044687081963341628107 525219067030622945012442161)
        ·
          refine ⟨393914300272967208759331621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525219067030622945012442161 393914300272967208759331621)
          ·
            refine ⟨73858931301181351642374679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393914300272967208759331621 73858931301181351642374679)
            ·
              refine ⟨110788396951772027463562019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73858931301181351642374679 110788396951772027463562019)
              ·
                refine ⟨166182595427658041195343029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110788396951772027463562019 166182595427658041195343029)
                ·
                  refine ⟨15579618321342941362063409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166182595427658041195343029 15579618321342941362063409)
                  ·
                    refine ⟨11684713741007206021547557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15579618321342941362063409 11684713741007206021547557)
                    ·
                      refine ⟨2190883826438851129040167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11684713741007206021547557 2190883826438851129040167)
                      ·
                        rfl

theorem cell23_4266731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_4266731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266731 prefixEnd_4266731 := by exact prefixLift 4266731
  have htrace : WordTrace (prefixWord ++ tailWord_4266731) baseStart_4266731 baseEnd_4266731 := by
    simpa [prefixWord, tailWord_4266731, baseEnd_4266731] using wordTrace_append hprefix tailTrace_4266731
  have hstable : (prefixWord ++ tailWord_4266731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266731).length < 2 ^ (prefixWord ++ tailWord_4266731).sum := by decide
  have hdescent : baseEnd_4266731 < baseStart_4266731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266748 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_4266748 : Nat := 118140960795 + 4266748 * 2 ^ 59
def prefixEnd_4266748 : Nat := 4983230072969 + 3 ^ 40 * 4266748 * 2
def baseEnd_4266748 : Nat := 2190892555609977562527589

theorem tailTrace_4266748 : CollatzResearch.WordTrace tailWord_4266748 prefixEnd_4266748 2190892555609977562527589 := by
  unfold tailWord_4266748
  simp only [CollatzResearch.WordTrace]
  refine ⟨77810542173154086694268449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103747389564205448925691265 77810542173154086694268449)
  ·
    refine ⟨58357906629865565020701337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77810542173154086694268449 58357906629865565020701337)
    ·
      refine ⟨43768429972399173765526003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58357906629865565020701337 43768429972399173765526003)
      ·
        refine ⟨65652644958598760648289005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43768429972399173765526003 65652644958598760648289005)
        ·
          refine ⟨24619741859474535243108377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65652644958598760648289005 24619741859474535243108377)
          ·
            refine ⟨18464806394605901432331283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24619741859474535243108377 18464806394605901432331283)
            ·
              refine ⟨27697209591908852148496925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18464806394605901432331283 27697209591908852148496925)
              ·
                refine ⟨10386453596965819555686347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27697209591908852148496925 10386453596965819555686347)
                ·
                  refine ⟨15579680395448729333529521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10386453596965819555686347 15579680395448729333529521)
                  ·
                    refine ⟨11684760296586547000147141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15579680395448729333529521 11684760296586547000147141)
                    ·
                      refine ⟨2190892555609977562527589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11684760296586547000147141 2190892555609977562527589)
                      ·
                        rfl

theorem cell23_4266748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_4266748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266748 prefixEnd_4266748 := by exact prefixLift 4266748
  have htrace : WordTrace (prefixWord ++ tailWord_4266748) baseStart_4266748 baseEnd_4266748 := by
    simpa [prefixWord, tailWord_4266748, baseEnd_4266748] using wordTrace_append hprefix tailTrace_4266748
  have hstable : (prefixWord ++ tailWord_4266748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266748).length < 2 ^ (prefixWord ++ tailWord_4266748).sum := by decide
  have hdescent : baseEnd_4266748 < baseStart_4266748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266785 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4266785 : Nat := 118140960795 + 4266785 * 2 ^ 59
def prefixEnd_4266785 : Nat := 4983230072969 + 3 ^ 40 * 4266785 * 2
def baseEnd_4266785 : Nat := 2190911554394193917764919

theorem tailTrace_4266785 : CollatzResearch.WordTrace tailWord_4266785 prefixEnd_4266785 2190911554394193917764919 := by
  unfold tailWord_4266785
  simp only [CollatzResearch.WordTrace]
  refine ⟨155622433847174128707633809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103748289231449419138422539 155622433847174128707633809)
  ·
    refine ⟨116716825385380596530725357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155622433847174128707633809 116716825385380596530725357)
    ·
      refine ⟨43768809519517723699022009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116716825385380596530725357 43768809519517723699022009)
      ·
        refine ⟨32826607139638292774266507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43768809519517723699022009 32826607139638292774266507)
        ·
          refine ⟨49239910709457439161399761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32826607139638292774266507 49239910709457439161399761)
          ·
            refine ⟨36929933032093079371049821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49239910709457439161399761 36929933032093079371049821)
            ·
              refine ⟨13848724887034904764143683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36929933032093079371049821 13848724887034904764143683)
              ·
                refine ⟨20773087330552357146215525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13848724887034904764143683 20773087330552357146215525)
                ·
                  refine ⟨3894953874478566964915411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20773087330552357146215525 3894953874478566964915411)
                  ·
                    refine ⟨5842430811717850447373117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894953874478566964915411 5842430811717850447373117)
                    ·
                      refine ⟨2190911554394193917764919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5842430811717850447373117 2190911554394193917764919)
                      ·
                        rfl

theorem cell23_4266785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4266785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266785 prefixEnd_4266785 := by exact prefixLift 4266785
  have htrace : WordTrace (prefixWord ++ tailWord_4266785) baseStart_4266785 baseEnd_4266785 := by
    simpa [prefixWord, tailWord_4266785, baseEnd_4266785] using wordTrace_append hprefix tailTrace_4266785
  have hstable : (prefixWord ++ tailWord_4266785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266785).length < 2 ^ (prefixWord ++ tailWord_4266785).sum := by decide
  have hdescent : baseEnd_4266785 < baseStart_4266785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266820 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4266820 : Nat := 118140960795 + 4266820 * 2 ^ 59
def prefixEnd_4266820 : Nat := 4983230072969 + 3 ^ 40 * 4266820 * 2
def baseEnd_4266820 : Nat := 2190929526217101280827259

theorem tailTrace_4266820 : CollatzResearch.WordTrace tailWord_4266820 prefixEnd_4266820 2190929526217101280827259 := by
  unfold tailWord_4266820
  simp only [CollatzResearch.WordTrace]
  refine ⟨77811855201023664842578957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103749140268031553123438609 77811855201023664842578957)
  ·
    refine ⟨29179445700383874315967109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77811855201023664842578957 29179445700383874315967109)
    ·
      refine ⟨5471146068821976434243833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29179445700383874315967109 5471146068821976434243833)
      ·
        refine ⟨4103359551616482325682875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5471146068821976434243833 4103359551616482325682875)
        ·
          refine ⟨6155039327424723488524313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103359551616482325682875 6155039327424723488524313)
          ·
            refine ⟨4616279495568542616393235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6155039327424723488524313 4616279495568542616393235)
            ·
              refine ⟨6924419243352813924589853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616279495568542616393235 6924419243352813924589853)
              ·
                refine ⟨2596657216257305221721195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6924419243352813924589853 2596657216257305221721195)
                ·
                  refine ⟨3894985824385957832581793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596657216257305221721195 3894985824385957832581793)
                  ·
                    refine ⟨2921239368289468374436345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3894985824385957832581793 2921239368289468374436345)
                    ·
                      refine ⟨2190929526217101280827259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921239368289468374436345 2190929526217101280827259)
                      ·
                        rfl

theorem cell23_4266820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4266820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266820 prefixEnd_4266820 := by exact prefixLift 4266820
  have htrace : WordTrace (prefixWord ++ tailWord_4266820) baseStart_4266820 baseEnd_4266820 := by
    simpa [prefixWord, tailWord_4266820, baseEnd_4266820] using wordTrace_append hprefix tailTrace_4266820
  have hstable : (prefixWord ++ tailWord_4266820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266820).length < 2 ^ (prefixWord ++ tailWord_4266820).sum := by decide
  have hdescent : baseEnd_4266820 < baseStart_4266820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266828 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4266828 : Nat := 118140960795 + 4266828 * 2 ^ 59
def prefixEnd_4266828 : Nat := 4983230072969 + 3 ^ 40 * 4266828 * 2
def baseEnd_4266828 : Nat := 2190933634062337249527221

theorem tailTrace_4266828 : CollatzResearch.WordTrace tailWord_4266828 prefixEnd_4266828 2190933634062337249527221 := by
  unfold tailWord_4266828
  simp only [CollatzResearch.WordTrace]
  refine ⟨77812001093009173525724569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103749334790678898034299425 77812001093009173525724569)
  ·
    refine ⟨58359000819756880144293427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77812001093009173525724569 58359000819756880144293427)
    ·
      refine ⟨87538501229635320216440141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58359000819756880144293427 87538501229635320216440141)
      ·
        refine ⟨32826937961113245081165053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87538501229635320216440141 32826937961113245081165053)
        ·
          refine ⟨12310101735417466905436895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32826937961113245081165053 12310101735417466905436895)
          ·
            refine ⟨18465152603126200358155343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12310101735417466905436895 18465152603126200358155343)
            ·
              refine ⟨27697728904689300537233015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18465152603126200358155343 27697728904689300537233015)
              ·
                refine ⟨41546593357033950805849523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27697728904689300537233015 41546593357033950805849523)
                ·
                  refine ⟨62319890035550926208774285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41546593357033950805849523 62319890035550926208774285)
                  ·
                    refine ⟨23369958763331597328290357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62319890035550926208774285 23369958763331597328290357)
                    ·
                      refine ⟨2190933634062337249527221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23369958763331597328290357 2190933634062337249527221)
                      ·
                        rfl

theorem cell23_4266828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4266828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266828 prefixEnd_4266828 := by exact prefixLift 4266828
  have htrace : WordTrace (prefixWord ++ tailWord_4266828) baseStart_4266828 baseEnd_4266828 := by
    simpa [prefixWord, tailWord_4266828, baseEnd_4266828] using wordTrace_append hprefix tailTrace_4266828
  have hstable : (prefixWord ++ tailWord_4266828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266828).length < 2 ^ (prefixWord ++ tailWord_4266828).sum := by decide
  have hdescent : baseEnd_4266828 < baseStart_4266828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266842 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_4266842 : Nat := 118140960795 + 4266842 * 2 ^ 59
def prefixEnd_4266842 : Nat := 4983230072969 + 3 ^ 40 * 4266842 * 2
def baseEnd_4266842 : Nat := 2190940822791500194752157

theorem tailTrace_4266842 : CollatzResearch.WordTrace tailWord_4266842 prefixEnd_4266842 2190940822791500194752157 := by
  unfold tailWord_4266842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38906128201991906860614695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103749675205311751628305853 38906128201991906860614695)
  ·
    refine ⟨58359192302987860290922043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38906128201991906860614695 58359192302987860290922043)
    ·
      refine ⟨87538788454481790436383065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58359192302987860290922043 87538788454481790436383065)
      ·
        refine ⟨65654091340861342827287299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87538788454481790436383065 65654091340861342827287299)
        ·
          refine ⟨98481137011292014240930949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65654091340861342827287299 98481137011292014240930949)
          ·
            refine ⟨18465213189617252670174553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98481137011292014240930949 18465213189617252670174553)
            ·
              refine ⟨13848909892212939502630915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18465213189617252670174553 13848909892212939502630915)
              ·
                refine ⟨20773364838319409253946373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13848909892212939502630915 20773364838319409253946373)
                ·
                  refine ⟨3895005907184889235114945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20773364838319409253946373 3895005907184889235114945)
                  ·
                    refine ⟨2921254430388666926336209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895005907184889235114945 2921254430388666926336209)
                    ·
                      refine ⟨2190940822791500194752157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921254430388666926336209 2190940822791500194752157)
                      ·
                        rfl

theorem cell23_4266842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_4266842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266842 prefixEnd_4266842 := by exact prefixLift 4266842
  have htrace : WordTrace (prefixWord ++ tailWord_4266842) baseStart_4266842 baseEnd_4266842 := by
    simpa [prefixWord, tailWord_4266842, baseEnd_4266842] using wordTrace_append hprefix tailTrace_4266842
  have hstable : (prefixWord ++ tailWord_4266842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266842).length < 2 ^ (prefixWord ++ tailWord_4266842).sum := by decide
  have hdescent : baseEnd_4266842 < baseStart_4266842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266859 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 2, 2, 2]
def baseStart_4266859 : Nat := 118140960795 + 4266859 * 2 ^ 59
def prefixEnd_4266859 : Nat := 4983230072969 + 3 ^ 40 * 4266859 * 2
def baseEnd_4266859 : Nat := 2190949551962626628239579

theorem tailTrace_4266859 : CollatzResearch.WordTrace tailWord_4266859 prefixEnd_4266859 2190949551962626628239579 := by
  unfold tailWord_4266859
  simp only [CollatzResearch.WordTrace]
  refine ⟨155625132848906039345827631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103750088565937359563885087 155625132848906039345827631)
  ·
    refine ⟨233437699273359059018741447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155625132848906039345827631 233437699273359059018741447)
    ·
      refine ⟨350156548910038588528112171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233437699273359059018741447 350156548910038588528112171)
      ·
        refine ⟨525234823365057882792168257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350156548910038588528112171 525234823365057882792168257)
        ·
          refine ⟨393926117523793412094126193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525234823365057882792168257 393926117523793412094126193)
          ·
            refine ⟨295444588142845059070594645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393926117523793412094126193 295444588142845059070594645)
            ·
              refine ⟨3462241267298965535983531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 295444588142845059070594645 3462241267298965535983531)
              ·
                refine ⟨5193361900948448303975297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462241267298965535983531 5193361900948448303975297)
                ·
                  refine ⟨3895021425711336227981473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5193361900948448303975297 3895021425711336227981473)
                  ·
                    refine ⟨2921266069283502170986105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895021425711336227981473 2921266069283502170986105)
                    ·
                      refine ⟨2190949551962626628239579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921266069283502170986105 2190949551962626628239579)
                      ·
                        rfl

theorem cell23_4266859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 2, 2].length) (baseStart_4266859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266859 prefixEnd_4266859 := by exact prefixLift 4266859
  have htrace : WordTrace (prefixWord ++ tailWord_4266859) baseStart_4266859 baseEnd_4266859 := by
    simpa [prefixWord, tailWord_4266859, baseEnd_4266859] using wordTrace_append hprefix tailTrace_4266859
  have hstable : (prefixWord ++ tailWord_4266859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266859).length < 2 ^ (prefixWord ++ tailWord_4266859).sum := by decide
  have hdescent : baseEnd_4266859 < baseStart_4266859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266915 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 6, 2]
def baseStart_4266915 : Nat := 118140960795 + 4266915 * 2 ^ 59
def prefixEnd_4266915 : Nat := 4983230072969 + 3 ^ 40 * 4266915 * 2
def baseEnd_4266915 : Nat := 2190978306879278409139321

theorem tailTrace_4266915 : CollatzResearch.WordTrace tailWord_4266915 prefixEnd_4266915 2190978306879278409139321 := by
  unfold tailWord_4266915
  simp only [CollatzResearch.WordTrace]
  refine ⟨155627175336703160909866199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103751450224468773939910799 155627175336703160909866199)
  ·
    refine ⟨233440763005054741364799299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155627175336703160909866199 233440763005054741364799299)
    ·
      refine ⟨350161144507582112047198949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233440763005054741364799299 350161144507582112047198949)
      ·
        refine ⟨65655214595171646008849803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 350161144507582112047198949 65655214595171646008849803)
        ·
          refine ⟨98482821892757469013274705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65655214595171646008849803 98482821892757469013274705)
          ·
            refine ⟨73862116419568101759956029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98482821892757469013274705 73862116419568101759956029)
            ·
              refine ⟨27698293657338038159983511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73862116419568101759956029 27698293657338038159983511)
              ·
                refine ⟨41547440486007057239975267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27698293657338038159983511 41547440486007057239975267)
                ·
                  refine ⟨62321160729010585859962901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41547440486007057239975267 62321160729010585859962901)
                  ·
                    refine ⟨2921304409172371212185761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62321160729010585859962901 2921304409172371212185761)
                    ·
                      refine ⟨2190978306879278409139321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921304409172371212185761 2190978306879278409139321)
                      ·
                        rfl

theorem cell23_4266915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_4266915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266915 prefixEnd_4266915 := by exact prefixLift 4266915
  have htrace : WordTrace (prefixWord ++ tailWord_4266915) baseStart_4266915 baseEnd_4266915 := by
    simpa [prefixWord, tailWord_4266915, baseEnd_4266915] using wordTrace_append hprefix tailTrace_4266915
  have hstable : (prefixWord ++ tailWord_4266915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266915).length < 2 ^ (prefixWord ++ tailWord_4266915).sum := by decide
  have hdescent : baseEnd_4266915 < baseStart_4266915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266929 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_4266929 : Nat := 118140960795 + 4266929 * 2 ^ 59
def prefixEnd_4266929 : Nat := 4983230072969 + 3 ^ 40 * 4266929 * 2
def baseEnd_4266929 : Nat := 730328498536147118121419

theorem tailTrace_4266929 : CollatzResearch.WordTrace tailWord_4266929 prefixEnd_4266929 730328498536147118121419 := by
  unfold tailWord_4266929
  simp only [CollatzResearch.WordTrace]
  refine ⟨155627685958652441300875841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103751790639101627533917227 155627685958652441300875841)
  ·
    refine ⟨116720764468989330975656881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155627685958652441300875841 116720764468989330975656881)
    ·
      refine ⟨87540573351741998231742661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116720764468989330975656881 87540573351741998231742661)
      ·
        refine ⟨16413857503451624668451749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87540573351741998231742661 16413857503451624668451749)
        ·
          refine ⟨3077598281897179625334703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16413857503451624668451749 3077598281897179625334703)
          ·
            refine ⟨4616397422845769438002055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077598281897179625334703 4616397422845769438002055)
            ·
              refine ⟨6924596134268654157003083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616397422845769438002055 6924596134268654157003083)
              ·
                refine ⟨10386894201402981235504625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924596134268654157003083 10386894201402981235504625)
                ·
                  refine ⟨7790170651052235926628469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10386894201402981235504625 7790170651052235926628469)
                  ·
                    refine ⟨730328498536147118121419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7790170651052235926628469 730328498536147118121419)
                    ·
                      rfl

theorem cell23_4266929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_4266929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266929 prefixEnd_4266929 := by exact prefixLift 4266929
  have htrace : WordTrace (prefixWord ++ tailWord_4266929) baseStart_4266929 baseEnd_4266929 := by
    simpa [prefixWord, tailWord_4266929, baseEnd_4266929] using wordTrace_append hprefix tailTrace_4266929
  have hstable : (prefixWord ++ tailWord_4266929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266929).length < 2 ^ (prefixWord ++ tailWord_4266929).sum := by decide
  have hdescent : baseEnd_4266929 < baseStart_4266929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266938 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_4266938 : Nat := 118140960795 + 4266938 * 2 ^ 59
def prefixEnd_4266938 : Nat := 4983230072969 + 3 ^ 40 * 4266938 * 2
def baseEnd_4266938 : Nat := 243443346326036868794635

theorem tailTrace_4266938 : CollatzResearch.WordTrace tailWord_4266938 prefixEnd_4266938 243443346326036868794635 := by
  unfold tailWord_4266938
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907003553904958959488367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103752009477079890558635645 38907003553904958959488367)
  ·
    refine ⟨58360505330857438439232551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38907003553904958959488367 58360505330857438439232551)
    ·
      refine ⟨87540757996286157658848827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58360505330857438439232551 87540757996286157658848827)
      ·
        refine ⟨131311136994429236488273241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87540757996286157658848827 131311136994429236488273241)
        ·
          refine ⟨98483352745821927366204931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131311136994429236488273241 98483352745821927366204931)
          ·
            refine ⟨147725029118732891049307397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98483352745821927366204931 147725029118732891049307397)
            ·
              refine ⟨27698442959762417071745137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147725029118732891049307397 27698442959762417071745137)
              ·
                refine ⟨20773832219821812803808853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27698442959762417071745137 20773832219821812803808853)
                ·
                  refine ⟨243443346326036868794635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20773832219821812803808853 243443346326036868794635)
                  ·
                    rfl

theorem cell23_4266938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_4266938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266938 prefixEnd_4266938 := by exact prefixLift 4266938
  have htrace : WordTrace (prefixWord ++ tailWord_4266938) baseStart_4266938 baseEnd_4266938 := by
    simpa [prefixWord, tailWord_4266938, baseEnd_4266938] using wordTrace_append hprefix tailTrace_4266938
  have hstable : (prefixWord ++ tailWord_4266938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266938).length < 2 ^ (prefixWord ++ tailWord_4266938).sum := by decide
  have hdescent : baseEnd_4266938 < baseStart_4266938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266955 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 6]
def baseStart_4266955 : Nat := 118140960795 + 4266955 * 2 ^ 59
def prefixEnd_4266955 : Nat := 4983230072969 + 3 ^ 40 * 4266955 * 2
def baseEnd_4266955 : Nat := 243444316233939805848793

theorem tailTrace_4266955 : CollatzResearch.WordTrace tailWord_4266955 prefixEnd_4266955 243444316233939805848793 := by
  unfold tailWord_4266955
  simp only [CollatzResearch.WordTrace]
  refine ⟨155628634256558247741322319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103752422837705498494214879 155628634256558247741322319)
  ·
    refine ⟨233442951384837371611983479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155628634256558247741322319 233442951384837371611983479)
    ·
      refine ⟨350164427077256057417975219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233442951384837371611983479 350164427077256057417975219)
      ·
        refine ⟨525246640615884086126962829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350164427077256057417975219 525246640615884086126962829)
        ·
          refine ⟨196967490230956532297611061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 525246640615884086126962829 196967490230956532297611061)
          ·
            refine ⟨18465702209152174902901037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196967490230956532297611061 18465702209152174902901037)
            ·
              refine ⟨6924638328432065588587889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18465702209152174902901037 6924638328432065588587889)
              ·
                refine ⟨5193478746324049191440917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6924638328432065588587889 5193478746324049191440917)
                ·
                  refine ⟨243444316233939805848793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5193478746324049191440917 243444316233939805848793)
                  ·
                    rfl

theorem cell23_4266955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 6].length) (baseStart_4266955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266955 prefixEnd_4266955 := by exact prefixLift 4266955
  have htrace : WordTrace (prefixWord ++ tailWord_4266955) baseStart_4266955 baseEnd_4266955 := by
    simpa [prefixWord, tailWord_4266955, baseEnd_4266955] using wordTrace_append hprefix tailTrace_4266955
  have hstable : (prefixWord ++ tailWord_4266955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266955).length < 2 ^ (prefixWord ++ tailWord_4266955).sum := by decide
  have hdescent : baseEnd_4266955 < baseStart_4266955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4266992 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2]
def baseStart_4266992 : Nat := 118140960795 + 4266992 * 2 ^ 59
def prefixEnd_4266992 : Nat := 4983230072969 + 3 ^ 40 * 4266992 * 2
def baseEnd_4266992 : Nat := 2191017844889674607876467

theorem tailTrace_4266992 : CollatzResearch.WordTrace tailWord_4266992 prefixEnd_4266992 2191017844889674607876467 := by
  unfold tailWord_4266992
  simp only [CollatzResearch.WordTrace]
  refine ⟨77814991878712101530209615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103753322504949468706946153 77814991878712101530209615)
  ·
    refine ⟨116722487818068152295314423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77814991878712101530209615 116722487818068152295314423)
    ·
      refine ⟨175083731727102228442971635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116722487818068152295314423 175083731727102228442971635)
      ·
        refine ⟨262625597590653342664457453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175083731727102228442971635 262625597590653342664457453)
        ·
          refine ⟨98484599096495003499171545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262625597590653342664457453 98484599096495003499171545)
          ·
            refine ⟨73863449322371252624378659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98484599096495003499171545 73863449322371252624378659)
            ·
              refine ⟨110795173983556878936567989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73863449322371252624378659 110795173983556878936567989)
              ·
                refine ⟨10387047560958457400303249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110795173983556878936567989 10387047560958457400303249)
                ·
                  refine ⟨7790285670718843050227437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10387047560958457400303249 7790285670718843050227437)
                  ·
                    refine ⟨2921357126519566143835289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7790285670718843050227437 2921357126519566143835289)
                    ·
                      refine ⟨2191017844889674607876467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921357126519566143835289 2191017844889674607876467)
                      ·
                        rfl

theorem cell23_4266992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2].length) (baseStart_4266992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4266992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4266992 prefixEnd_4266992 := by exact prefixLift 4266992
  have htrace : WordTrace (prefixWord ++ tailWord_4266992) baseStart_4266992 baseEnd_4266992 := by
    simpa [prefixWord, tailWord_4266992, baseEnd_4266992] using wordTrace_append hprefix tailTrace_4266992
  have hstable : (prefixWord ++ tailWord_4266992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4266992).length < 2 ^ (prefixWord ++ tailWord_4266992).sum := by decide
  have hdescent : baseEnd_4266992 < baseStart_4266992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4266992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267005 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_4267005 : Nat := 118140960795 + 4267005 * 2 ^ 59
def prefixEnd_4267005 : Nat := 4983230072969 + 3 ^ 40 * 4267005 * 2
def baseEnd_4267005 : Nat := 2191024520138183057013907

theorem tailTrace_4267005 : CollatzResearch.WordTrace tailWord_4267005 prefixEnd_4267005 2191024520138183057013907 := by
  unfold tailWord_4267005
  simp only [CollatzResearch.WordTrace]
  refine ⟨155630457906377106280642469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103753638604251404187094979 155630457906377106280642469)
  ·
    refine ⟨29180710857445707427620463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155630457906377106280642469 29180710857445707427620463)
    ·
      refine ⟨43771066286168561141430695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29180710857445707427620463 43771066286168561141430695)
      ·
        refine ⟨65656599429252841712146043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43771066286168561141430695 65656599429252841712146043)
        ·
          refine ⟨98484899143879262568219065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65656599429252841712146043 98484899143879262568219065)
          ·
            refine ⟨73863674357909446926164299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98484899143879262568219065 73863674357909446926164299)
            ·
              refine ⟨110795511536864170389246449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73863674357909446926164299 110795511536864170389246449)
              ·
                refine ⟨83096633652648127791934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110795511536864170389246449 83096633652648127791934837)
                ·
                  refine ⟨7790309404935761980493891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83096633652648127791934837 7790309404935761980493891)
                  ·
                    refine ⟨11685464107403642970740837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7790309404935761980493891 11685464107403642970740837)
                    ·
                      refine ⟨2191024520138183057013907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11685464107403642970740837 2191024520138183057013907)
                      ·
                        rfl

theorem cell23_4267005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_4267005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267005 prefixEnd_4267005 := by exact prefixLift 4267005
  have htrace : WordTrace (prefixWord ++ tailWord_4267005) baseStart_4267005 baseEnd_4267005 := by
    simpa [prefixWord, tailWord_4267005, baseEnd_4267005] using wordTrace_append hprefix tailTrace_4267005
  have hstable : (prefixWord ++ tailWord_4267005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267005).length < 2 ^ (prefixWord ++ tailWord_4267005).sum := by decide
  have hdescent : baseEnd_4267005 < baseStart_4267005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267009 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_4267009 : Nat := 118140960795 + 4267009 * 2 ^ 59
def prefixEnd_4267009 : Nat := 4983230072969 + 3 ^ 40 * 4267009 * 2
def baseEnd_4267009 : Nat := 2191026574060801041363889

theorem tailTrace_4267009 : CollatzResearch.WordTrace tailWord_4267009 prefixEnd_4267009 2191026574060801041363889 := by
  unfold tailWord_4267009
  simp only [CollatzResearch.WordTrace]
  refine ⟨155630603798362614963788081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103753735865575076642525387 155630603798362614963788081)
  ·
    refine ⟨116722952848771961222841061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155630603798362614963788081 116722952848771961222841061)
    ·
      refine ⟨21885553659144742729282699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116722952848771961222841061 21885553659144742729282699)
      ·
        refine ⟨32828330488717114093924049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885553659144742729282699 32828330488717114093924049)
        ·
          refine ⟨24621247866537835570443037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32828330488717114093924049 24621247866537835570443037)
          ·
            refine ⟨9232967949951688338916139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24621247866537835570443037 9232967949951688338916139)
            ·
              refine ⟨13849451924927532508374209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9232967949951688338916139 13849451924927532508374209)
              ·
                refine ⟨10387088943695649381280657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13849451924927532508374209 10387088943695649381280657)
                ·
                  refine ⟨7790316707771737035960493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10387088943695649381280657 7790316707771737035960493)
                  ·
                    refine ⟨2921368765414401388485185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7790316707771737035960493 2921368765414401388485185)
                    ·
                      refine ⟨2191026574060801041363889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921368765414401388485185 2191026574060801041363889)
                      ·
                        rfl

theorem cell23_4267009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_4267009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267009 prefixEnd_4267009 := by exact prefixLift 4267009
  have htrace : WordTrace (prefixWord ++ tailWord_4267009) baseStart_4267009 baseEnd_4267009 := by
    simpa [prefixWord, tailWord_4267009, baseEnd_4267009] using wordTrace_append hprefix tailTrace_4267009
  have hstable : (prefixWord ++ tailWord_4267009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267009).length < 2 ^ (prefixWord ++ tailWord_4267009).sum := by decide
  have hdescent : baseEnd_4267009 < baseStart_4267009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267010 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4267010 : Nat := 118140960795 + 4267010 * 2 ^ 59
def prefixEnd_4267010 : Nat := 4983230072969 + 3 ^ 40 * 4267010 * 2
def baseEnd_4267010 : Nat := 730342362513818512483795

theorem tailTrace_4267010 : CollatzResearch.WordTrace tailWord_4267010 prefixEnd_4267010 730342362513818512483795 := by
  unfold tailWord_4267010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907660067839748033643621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103753760180905994756382989 38907660067839748033643621)
  ·
    refine ⟨7295186262719952756308179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38907660067839748033643621 7295186262719952756308179)
    ·
      refine ⟨10942779394079929134462269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7295186262719952756308179 10942779394079929134462269)
      ·
        refine ⟨4103542272779973425423351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10942779394079929134462269 4103542272779973425423351)
        ·
          refine ⟨6155313409169960138135027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103542272779973425423351 6155313409169960138135027)
          ·
            refine ⟨9232970113754940207202541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155313409169960138135027 9232970113754940207202541)
            ·
              refine ⟨3462363792658102577700953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9232970113754940207202541 3462363792658102577700953)
              ·
                refine ⟨2596772844493576933275715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462363792658102577700953 2596772844493576933275715)
                ·
                  refine ⟨3895159266740365399913573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596772844493576933275715 3895159266740365399913573)
                  ·
                    refine ⟨730342362513818512483795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895159266740365399913573 730342362513818512483795)
                    ·
                      rfl

theorem cell23_4267010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4267010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267010 prefixEnd_4267010 := by exact prefixLift 4267010
  have htrace : WordTrace (prefixWord ++ tailWord_4267010) baseStart_4267010 baseEnd_4267010 := by
    simpa [prefixWord, tailWord_4267010, baseEnd_4267010] using wordTrace_append hprefix tailTrace_4267010
  have hstable : (prefixWord ++ tailWord_4267010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267010).length < 2 ^ (prefixWord ++ tailWord_4267010).sum := by decide
  have hdescent : baseEnd_4267010 < baseStart_4267010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267036 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_4267036 : Nat := 118140960795 + 4267036 * 2 ^ 59
def prefixEnd_4267036 : Nat := 4983230072969 + 3 ^ 40 * 4267036 * 2
def baseEnd_4267036 : Nat := 730346812679490811908755

theorem tailTrace_4267036 : CollatzResearch.WordTrace tailWord_4267036 prefixEnd_4267036 730346812679490811908755 := by
  unfold tailWord_4267036
  simp only [CollatzResearch.WordTrace]
  refine ⟨77815794284632399287510481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103754392379509865716680641 77815794284632399287510481)
  ·
    refine ⟨58361845713474299465632861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77815794284632399287510481 58361845713474299465632861)
    ·
      refine ⟨21885692142552862299612323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58361845713474299465632861 21885692142552862299612323)
      ·
        refine ⟨32828538213829293449418485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885692142552862299612323 32828538213829293449418485)
        ·
          refine ⟨3077675457546496260882983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32828538213829293449418485 3077675457546496260882983)
          ·
            refine ⟨4616513186319744391324475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077675457546496260882983 4616513186319744391324475)
            ·
              refine ⟨6924769779479616586986713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616513186319744391324475 6924769779479616586986713)
              ·
                refine ⟨5193577334609712440240035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6924769779479616586986713 5193577334609712440240035)
                ·
                  refine ⟨7790366001914568660360053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193577334609712440240035 7790366001914568660360053)
                  ·
                    refine ⟨730346812679490811908755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7790366001914568660360053 730346812679490811908755)
                    ·
                      rfl

theorem cell23_4267036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_4267036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267036 prefixEnd_4267036 := by exact prefixLift 4267036
  have htrace : WordTrace (prefixWord ++ tailWord_4267036) baseStart_4267036 baseEnd_4267036 := by
    simpa [prefixWord, tailWord_4267036, baseEnd_4267036] using wordTrace_append hprefix tailTrace_4267036
  have hstable : (prefixWord ++ tailWord_4267036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267036).length < 2 ^ (prefixWord ++ tailWord_4267036).sum := by decide
  have hdescent : baseEnd_4267036 < baseStart_4267036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267039 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_4267039 : Nat := 118140960795 + 4267039 * 2 ^ 59
def prefixEnd_4267039 : Nat := 4983230072969 + 3 ^ 40 * 4267039 * 2
def baseEnd_4267039 : Nat := 2191041978480435923988751

theorem tailTrace_4267039 : CollatzResearch.WordTrace tailWord_4267039 prefixEnd_4267039 2191041978480435923988751 := by
  unfold tailWord_4267039
  simp only [CollatzResearch.WordTrace]
  refine ⟨155631697988253930087380171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103754465325502620058253447 155631697988253930087380171)
  ·
    refine ⟨233447546982380895131070257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155631697988253930087380171 233447546982380895131070257)
    ·
      refine ⟨175085660236785671348302693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233447546982380895131070257 175085660236785671348302693)
      ·
        refine ⟨32828561294397313377806755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175085660236785671348302693 32828561294397313377806755)
        ·
          refine ⟨49242841941595970066710133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32828561294397313377806755 49242841941595970066710133)
          ·
            refine ⟨4616516432024622193754075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49242841941595970066710133 4616516432024622193754075)
            ·
              refine ⟨6924774648036933290631113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616516432024622193754075 6924774648036933290631113)
              ·
                refine ⟨5193580986027699967973335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6924774648036933290631113 5193580986027699967973335)
                ·
                  refine ⟨7790371479041549951960003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193580986027699967973335 7790371479041549951960003)
                  ·
                    refine ⟨11685557218562324927940005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7790371479041549951960003 11685557218562324927940005)
                    ·
                      refine ⟨2191041978480435923988751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11685557218562324927940005 2191041978480435923988751)
                      ·
                        rfl

theorem cell23_4267039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_4267039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267039 prefixEnd_4267039 := by exact prefixLift 4267039
  have htrace : WordTrace (prefixWord ++ tailWord_4267039) baseStart_4267039 baseEnd_4267039 := by
    simpa [prefixWord, tailWord_4267039, baseEnd_4267039] using wordTrace_append hprefix tailTrace_4267039
  have hstable : (prefixWord ++ tailWord_4267039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267039).length < 2 ^ (prefixWord ++ tailWord_4267039).sum := by decide
  have hdescent : baseEnd_4267039 < baseStart_4267039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267056 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 1, 2, 2]
def baseStart_4267056 : Nat := 118140960795 + 4267056 * 2 ^ 59
def prefixEnd_4267056 : Nat := 4983230072969 + 3 ^ 40 * 4267056 * 2
def baseEnd_4267056 : Nat := 2191050707651562357476173

theorem tailTrace_4267056 : CollatzResearch.WordTrace tailWord_4267056 prefixEnd_4267056 2191050707651562357476173 := by
  unfold tailWord_4267056
  simp only [CollatzResearch.WordTrace]
  refine ⟨77816159014596170995374511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103754878686128227993832681 77816159014596170995374511)
  ·
    refine ⟨116724238521894256493061767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77816159014596170995374511 116724238521894256493061767)
    ·
      refine ⟨175086357782841384739592651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116724238521894256493061767 175086357782841384739592651)
      ·
        refine ⟨262629536674262077109388977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175086357782841384739592651 262629536674262077109388977)
        ·
          refine ⟨196972152505696557832041733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262629536674262077109388977 196972152505696557832041733)
          ·
            refine ⟨36932278594818104593507825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196972152505696557832041733 36932278594818104593507825)
            ·
              refine ⟨27699208946113578445130869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36932278594818104593507825 27699208946113578445130869)
              ·
                refine ⟨2596800838698147979231019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27699208946113578445130869 2596800838698147979231019)
                ·
                  refine ⟨3895201258047221968846529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596800838698147979231019 3895201258047221968846529)
                  ·
                    refine ⟨2921400943535416476634897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895201258047221968846529 2921400943535416476634897)
                    ·
                      refine ⟨2191050707651562357476173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921400943535416476634897 2191050707651562357476173)
                      ·
                        rfl

theorem cell23_4267056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 2, 2].length) (baseStart_4267056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267056 prefixEnd_4267056 := by exact prefixLift 4267056
  have htrace : WordTrace (prefixWord ++ tailWord_4267056) baseStart_4267056 baseEnd_4267056 := by
    simpa [prefixWord, tailWord_4267056, baseEnd_4267056] using wordTrace_append hprefix tailTrace_4267056
  have hstable : (prefixWord ++ tailWord_4267056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267056).length < 2 ^ (prefixWord ++ tailWord_4267056).sum := by decide
  have hdescent : baseEnd_4267056 < baseStart_4267056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267089 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_4267089 : Nat := 118140960795 + 4267089 * 2 ^ 59
def prefixEnd_4267089 : Nat := 4983230072969 + 3 ^ 40 * 4267089 * 2
def baseEnd_4267089 : Nat := 2191067652513160728363521

theorem tailTrace_4267089 : CollatzResearch.WordTrace tailWord_4267089 prefixEnd_4267089 2191067652513160728363521 := by
  unfold tailWord_4267089
  simp only [CollatzResearch.WordTrace]
  refine ⟨155633521638072788626700321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103755681092048525751133547 155633521638072788626700321)
  ·
    refine ⟨116725141228554591470025241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155633521638072788626700321 116725141228554591470025241)
    ·
      refine ⟨87543855921415943602518931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116725141228554591470025241 87543855921415943602518931)
      ·
        refine ⟨131315783882123915403778397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87543855921415943602518931 131315783882123915403778397)
        ·
          refine ⟨49243418955796468276416899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131315783882123915403778397 49243418955796468276416899)
          ·
            refine ⟨73865128433694702414625349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49243418955796468276416899 73865128433694702414625349)
            ·
              refine ⟨13849711581317756702742253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73865128433694702414625349 13849711581317756702742253)
              ·
                refine ⟨5193641842994158763528345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13849711581317756702742253 5193641842994158763528345)
                ·
                  refine ⟨3895231382245619072646259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5193641842994158763528345 3895231382245619072646259)
                  ·
                    refine ⟨5842847073368428608969389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895231382245619072646259 5842847073368428608969389)
                    ·
                      refine ⟨2191067652513160728363521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5842847073368428608969389 2191067652513160728363521)
                      ·
                        rfl

theorem cell23_4267089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_4267089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267089 prefixEnd_4267089 := by exact prefixLift 4267089
  have htrace : WordTrace (prefixWord ++ tailWord_4267089) baseStart_4267089 baseEnd_4267089 := by
    simpa [prefixWord, tailWord_4267089, baseEnd_4267089] using wordTrace_append hprefix tailTrace_4267089
  have hstable : (prefixWord ++ tailWord_4267089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267089).length < 2 ^ (prefixWord ++ tailWord_4267089).sum := by decide
  have hdescent : baseEnd_4267089 < baseStart_4267089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267095 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4267095 : Nat := 118140960795 + 4267095 * 2 ^ 59
def prefixEnd_4267095 : Nat := 4983230072969 + 3 ^ 40 * 4267095 * 2
def baseEnd_4267095 : Nat := 2191070733397087704888493

theorem tailTrace_4267095 : CollatzResearch.WordTrace tailWord_4267095 prefixEnd_4267095 2191070733397087704888493 := by
  unfold tailWord_4267095
  simp only [CollatzResearch.WordTrace]
  refine ⟨155633740476051051651418739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103755826984034034434279159 155633740476051051651418739)
  ·
    refine ⟨233450610714076577477128109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155633740476051051651418739 233450610714076577477128109)
    ·
      refine ⟨87543979017778716553923041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233450610714076577477128109 87543979017778716553923041)
      ·
        refine ⟨65657984263334037415442281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87543979017778716553923041 65657984263334037415442281)
        ·
          refine ⟨49243488197500528061581711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65657984263334037415442281 49243488197500528061581711)
          ·
            refine ⟨73865232296250792092372567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49243488197500528061581711 73865232296250792092372567)
            ·
              refine ⟨110797848444376188138558851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73865232296250792092372567 110797848444376188138558851)
              ·
                refine ⟨166196772666564282207838277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110797848444376188138558851 166196772666564282207838277)
                ·
                  refine ⟨31161894874980802913969677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166196772666564282207838277 31161894874980802913969677)
                  ·
                    refine ⟨11685710578117801092738629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31161894874980802913969677 11685710578117801092738629)
                    ·
                      refine ⟨2191070733397087704888493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11685710578117801092738629 2191070733397087704888493)
                      ·
                        rfl

theorem cell23_4267095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4267095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267095 prefixEnd_4267095 := by exact prefixLift 4267095
  have htrace : WordTrace (prefixWord ++ tailWord_4267095) baseStart_4267095 baseEnd_4267095 := by
    simpa [prefixWord, tailWord_4267095, baseEnd_4267095] using wordTrace_append hprefix tailTrace_4267095
  have hstable : (prefixWord ++ tailWord_4267095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267095).length < 2 ^ (prefixWord ++ tailWord_4267095).sum := by decide
  have hdescent : baseEnd_4267095 < baseStart_4267095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267186 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_4267186 : Nat := 118140960795 + 4267186 * 2 ^ 59
def prefixEnd_4267186 : Nat := 4983230072969 + 3 ^ 40 * 4267186 * 2
def baseEnd_4267186 : Nat := 243457495570738538761175

theorem tailTrace_4267186 : CollatzResearch.WordTrace tailWord_4267186 prefixEnd_4267186 243457495570738538761175 := by
  unfold tailWord_4267186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38909264879680343548245353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103758039679147582795320941 38909264879680343548245353)
  ·
    refine ⟨29181948659760257661184015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38909264879680343548245353 29181948659760257661184015)
    ·
      refine ⟨43772922989640386491776023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29181948659760257661184015 43772922989640386491776023)
      ·
        refine ⟨65659384484460579737664035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43772922989640386491776023 65659384484460579737664035)
        ·
          refine ⟨98489076726690869606496053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65659384484460579737664035 98489076726690869606496053)
          ·
            refine ⟨9233350943127269025609005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98489076726690869606496053 9233350943127269025609005)
            ·
              refine ⟨3462506603672725884603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9233350943127269025609005 3462506603672725884603377)
              ·
                refine ⟨2596879952754544413452533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462506603672725884603377 2596879952754544413452533)
                ·
                  refine ⟨243457495570738538761175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596879952754544413452533 243457495570738538761175)
                  ·
                    rfl

theorem cell23_4267186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_4267186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267186 prefixEnd_4267186 := by exact prefixLift 4267186
  have htrace : WordTrace (prefixWord ++ tailWord_4267186) baseStart_4267186 baseEnd_4267186 := by
    simpa [prefixWord, tailWord_4267186, baseEnd_4267186] using wordTrace_append hprefix tailTrace_4267186
  have hstable : (prefixWord ++ tailWord_4267186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267186).length < 2 ^ (prefixWord ++ tailWord_4267186).sum := by decide
  have hdescent : baseEnd_4267186 < baseStart_4267186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267195 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 8]
def baseStart_4267195 : Nat := 118140960795 + 4267195 * 2 ^ 59
def prefixEnd_4267195 : Nat := 4983230072969 + 3 ^ 40 * 4267195 * 2
def baseEnd_4267195 : Nat := 730374027154179104546011

theorem tailTrace_4267195 : CollatzResearch.WordTrace tailWord_4267195 prefixEnd_4267195 730374027154179104546011 := by
  unfold tailWord_4267195
  simp only [CollatzResearch.WordTrace]
  refine ⟨155637387775688768730059039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103758258517125845820039359 155637387775688768730059039)
  ·
    refine ⟨233456081663533153095088559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155637387775688768730059039 233456081663533153095088559)
    ·
      refine ⟨350184122495299729642632839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233456081663533153095088559 350184122495299729642632839)
      ·
        refine ⟨525276183742949594463949259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350184122495299729642632839 525276183742949594463949259)
        ·
          refine ⟨787914275614424391695923889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525276183742949594463949259 787914275614424391695923889)
          ·
            refine ⟨590935706710818293771942917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787914275614424391695923889 590935706710818293771942917)
            ·
              refine ⟨110800445008278430082239297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 590935706710818293771942917 110800445008278430082239297)
              ·
                refine ⟨83100333756208822561679473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110800445008278430082239297 83100333756208822561679473)
                ·
                  refine ⟨62325250317156616921259605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83100333756208822561679473 62325250317156616921259605)
                  ·
                    refine ⟨730374027154179104546011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62325250317156616921259605 730374027154179104546011)
                    ·
                      rfl

theorem cell23_4267195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_4267195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267195 prefixEnd_4267195 := by exact prefixLift 4267195
  have htrace : WordTrace (prefixWord ++ tailWord_4267195) baseStart_4267195 baseEnd_4267195 := by
    simpa [prefixWord, tailWord_4267195, baseEnd_4267195] using wordTrace_append hprefix tailTrace_4267195
  have hstable : (prefixWord ++ tailWord_4267195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267195).length < 2 ^ (prefixWord ++ tailWord_4267195).sum := by decide
  have hdescent : baseEnd_4267195 < baseStart_4267195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267326 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_4267326 : Nat := 118140960795 + 4267326 * 2 ^ 59
def prefixEnd_4267326 : Nat := 4983230072969 + 3 ^ 40 * 4267326 * 2
def baseEnd_4267326 : Nat := 2191189347428276301099931

theorem tailTrace_4267326 : CollatzResearch.WordTrace tailWord_4267326 prefixEnd_4267326 2191189347428276301099931 := by
  unfold tailWord_4267326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19455270717276772262884729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103761443825476118735385221 19455270717276772262884729)
  ·
    refine ⟨14591453037957579197163547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19455270717276772262884729 14591453037957579197163547)
    ·
      refine ⟨21887179556936368795745321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14591453037957579197163547 21887179556936368795745321)
      ·
        refine ⟨16415384667702276596808991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21887179556936368795745321 16415384667702276596808991)
        ·
          refine ⟨24623077001553414895213487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16415384667702276596808991 24623077001553414895213487)
          ·
            refine ⟨36934615502330122342820231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24623077001553414895213487 36934615502330122342820231)
            ·
              refine ⟨55401923253495183514230347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36934615502330122342820231 55401923253495183514230347)
              ·
                refine ⟨83102884880242775271345521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55401923253495183514230347 83102884880242775271345521)
                ·
                  refine ⟨62327163660182081453509141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83102884880242775271345521 62327163660182081453509141)
                  ·
                    refine ⟨2921585796571035068133241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62327163660182081453509141 2921585796571035068133241)
                    ·
                      refine ⟨2191189347428276301099931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921585796571035068133241 2191189347428276301099931)
                      ·
                        rfl

theorem cell23_4267326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_4267326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267326 prefixEnd_4267326 := by exact prefixLift 4267326
  have htrace : WordTrace (prefixWord ++ tailWord_4267326) baseStart_4267326 baseEnd_4267326 := by
    simpa [prefixWord, tailWord_4267326, baseEnd_4267326] using wordTrace_append hprefix tailTrace_4267326
  have hstable : (prefixWord ++ tailWord_4267326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267326).length < 2 ^ (prefixWord ++ tailWord_4267326).sum := by decide
  have hdescent : baseEnd_4267326 < baseStart_4267326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267349 : List Nat := [1, 3, 2, 2, 3, 3, 9]
def baseStart_4267349 : Nat := 118140960795 + 4267349 * 2 ^ 59
def prefixEnd_4267349 : Nat := 4983230072969 + 3 ^ 40 * 4267349 * 2
def baseEnd_4267349 : Nat := 27051866141769502606325

theorem tailTrace_4267349 : CollatzResearch.WordTrace tailWord_4267349 prefixEnd_4267349 27051866141769502606325 := by
  unfold tailWord_4267349
  simp only [CollatzResearch.WordTrace]
  refine ⟨155643004617130853031165101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103762003078087235354110067 155643004617130853031165101)
  ·
    refine ⟨58366126731424069886686913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155643004617130853031165101 58366126731424069886686913)
    ·
      refine ⟨43774595048568052415015185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58366126731424069886686913 43774595048568052415015185)
      ·
        refine ⟨32830946286426039311261389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43774595048568052415015185 32830946286426039311261389)
        ·
          refine ⟨12311604857409764741723021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32830946286426039311261389 12311604857409764741723021)
          ·
            refine ⟨4616851821528661778146133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12311604857409764741723021 4616851821528661778146133)
            ·
              refine ⟨27051866141769502606325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4616851821528661778146133 27051866141769502606325)
              ·
                rfl

theorem cell23_4267349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 9].length) (baseStart_4267349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267349 prefixEnd_4267349 := by exact prefixLift 4267349
  have htrace : WordTrace (prefixWord ++ tailWord_4267349) baseStart_4267349 baseEnd_4267349 := by
    simpa [prefixWord, tailWord_4267349, baseEnd_4267349] using wordTrace_append hprefix tailTrace_4267349
  have hstable : (prefixWord ++ tailWord_4267349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267349).length < 2 ^ (prefixWord ++ tailWord_4267349).sum := by decide
  have hdescent : baseEnd_4267349 < baseStart_4267349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267360 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2]
def baseStart_4267360 : Nat := 118140960795 + 4267360 * 2 ^ 59
def prefixEnd_4267360 : Nat := 4983230072969 + 3 ^ 40 * 4267360 * 2
def baseEnd_4267360 : Nat := 2191206805770529168074775

theorem tailTrace_4267360 : CollatzResearch.WordTrace tailWord_4267360 prefixEnd_4267360 2191206805770529168074775 := by
  unfold tailWord_4267360
  simp only [CollatzResearch.WordTrace]
  refine ⟨77821702910045500954907767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103762270546727334606543689 77821702910045500954907767)
  ·
    refine ⟨116732554365068251432361651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77821702910045500954907767 116732554365068251432361651)
    ·
      refine ⟨175098831547602377148542477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116732554365068251432361651 175098831547602377148542477)
      ·
        refine ⟨65662061830350891430703429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175098831547602377148542477 65662061830350891430703429)
        ·
          refine ⟨12311636593190792143256893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65662061830350891430703429 12311636593190792143256893)
          ·
            refine ⟨4616863722446547053721335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12311636593190792143256893 4616863722446547053721335)
            ·
              refine ⟨6925295583669820580582003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616863722446547053721335 6925295583669820580582003)
              ·
                refine ⟨10387943375504730870873005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925295583669820580582003 10387943375504730870873005)
                ·
                  refine ⟨3895478765814274076577377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10387943375504730870873005 3895478765814274076577377)
                  ·
                    refine ⟨2921609074360705557433033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895478765814274076577377 2921609074360705557433033)
                    ·
                      refine ⟨2191206805770529168074775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921609074360705557433033 2191206805770529168074775)
                      ·
                        rfl

theorem cell23_4267360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_4267360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267360 prefixEnd_4267360 := by exact prefixLift 4267360
  have htrace : WordTrace (prefixWord ++ tailWord_4267360) baseStart_4267360 baseEnd_4267360 := by
    simpa [prefixWord, tailWord_4267360, baseEnd_4267360] using wordTrace_append hprefix tailTrace_4267360
  have hstable : (prefixWord ++ tailWord_4267360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267360).length < 2 ^ (prefixWord ++ tailWord_4267360).sum := by decide
  have hdescent : baseEnd_4267360 < baseStart_4267360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267386 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_4267386 : Nat := 118140960795 + 4267386 * 2 ^ 59
def prefixEnd_4267386 : Nat := 4983230072969 + 3 ^ 40 * 4267386 * 2
def baseEnd_4267386 : Nat := 2191220156267546066349655

theorem tailTrace_4267386 : CollatzResearch.WordTrace tailWord_4267386 prefixEnd_4267386 2191220156267546066349655 := by
  unfold tailWord_4267386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911088529499202087565503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103762902745331205566841341 38911088529499202087565503)
  ·
    refine ⟨58366632794248803131348255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38911088529499202087565503 58366632794248803131348255)
    ·
      refine ⟨87549949191373204697022383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58366632794248803131348255 87549949191373204697022383)
      ·
        refine ⟨131324923787059807045533575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87549949191373204697022383 131324923787059807045533575)
        ·
          refine ⟨196987385680589710568300363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131324923787059807045533575 196987385680589710568300363)
          ·
            refine ⟨295481078520884565852450545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196987385680589710568300363 295481078520884565852450545)
            ·
              refine ⟨221610808890663424389337909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295481078520884565852450545 221610808890663424389337909)
              ·
                refine ⟨20776013333499696036500429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221610808890663424389337909 20776013333499696036500429)
                ·
                  refine ⟨7791005000062386013687661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20776013333499696036500429 7791005000062386013687661)
                  ·
                    refine ⟨2921626875023394755132873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7791005000062386013687661 2921626875023394755132873)
                    ·
                      refine ⟨2191220156267546066349655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921626875023394755132873 2191220156267546066349655)
                      ·
                        rfl

theorem cell23_4267386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_4267386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267386 prefixEnd_4267386 := by exact prefixLift 4267386
  have htrace : WordTrace (prefixWord ++ tailWord_4267386) baseStart_4267386 baseEnd_4267386 := by
    simpa [prefixWord, tailWord_4267386, baseEnd_4267386] using wordTrace_append hprefix tailTrace_4267386
  have hstable : (prefixWord ++ tailWord_4267386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267386).length < 2 ^ (prefixWord ++ tailWord_4267386).sum := by decide
  have hdescent : baseEnd_4267386 < baseStart_4267386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267390 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4267390 : Nat := 118140960795 + 4267390 * 2 ^ 59
def prefixEnd_4267390 : Nat := 4983230072969 + 3 ^ 40 * 4267390 * 2
def baseEnd_4267390 : Nat := 2191222210190164050699637

theorem tailTrace_4267390 : CollatzResearch.WordTrace tailWord_4267390 prefixEnd_4267390 2191222210190164050699637 := by
  unfold tailWord_4267390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19455562501247789629175953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103763000006654878022271749 19455562501247789629175953)
  ·
    refine ⟨14591671875935842221881965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19455562501247789629175953 14591671875935842221881965)
    ·
      refine ⟨5471876953475940833205737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14591671875935842221881965 5471876953475940833205737)
      ·
        refine ⟨4103907715106955624904303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5471876953475940833205737 4103907715106955624904303)
        ·
          refine ⟨6155861572660433437356455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103907715106955624904303 6155861572660433437356455)
          ·
            refine ⟨9233792358990650156034683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155861572660433437356455 9233792358990650156034683)
            ·
              refine ⟨13850688538485975234052025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233792358990650156034683 13850688538485975234052025)
              ·
                refine ⟨10388016403864481425539019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13850688538485975234052025 10388016403864481425539019)
                ·
                  refine ⟨15582024605796722138308529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10388016403864481425539019 15582024605796722138308529)
                  ·
                    refine ⟨11686518454347541603731397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15582024605796722138308529 11686518454347541603731397)
                    ·
                      refine ⟨2191222210190164050699637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11686518454347541603731397 2191222210190164050699637)
                      ·
                        rfl

theorem cell23_4267390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4267390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267390 prefixEnd_4267390 := by exact prefixLift 4267390
  have htrace : WordTrace (prefixWord ++ tailWord_4267390) baseStart_4267390 baseEnd_4267390 := by
    simpa [prefixWord, tailWord_4267390, baseEnd_4267390] using wordTrace_append hprefix tailTrace_4267390
  have hstable : (prefixWord ++ tailWord_4267390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267390).length < 2 ^ (prefixWord ++ tailWord_4267390).sum := by decide
  have hdescent : baseEnd_4267390 < baseStart_4267390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267393 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4267393 : Nat := 118140960795 + 4267393 * 2 ^ 59
def prefixEnd_4267393 : Nat := 4983230072969 + 3 ^ 40 * 4267393 * 2
def baseEnd_4267393 : Nat := 2191223750632127538962123

theorem tailTrace_4267393 : CollatzResearch.WordTrace tailWord_4267393 prefixEnd_4267393 2191223750632127538962123 := by
  unfold tailWord_4267393
  simp only [CollatzResearch.WordTrace]
  refine ⟨155644609428971448545766833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103763072952647632363844555 155644609428971448545766833)
  ·
    refine ⟨116733457071728586409325125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155644609428971448545766833 116733457071728586409325125)
    ·
      refine ⟨21887523200949109951748461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116733457071728586409325125 21887523200949109951748461)
      ·
        refine ⟨8207821200355916231905673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21887523200949109951748461 8207821200355916231905673)
        ·
          refine ⟨6155865900266937173929255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8207821200355916231905673 6155865900266937173929255)
          ·
            refine ⟨9233798850400405760893883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155865900266937173929255 9233798850400405760893883)
            ·
              refine ⟨13850698275600608641340825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233798850400405760893883 13850698275600608641340825)
              ·
                refine ⟨10388023706700456481005619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13850698275600608641340825 10388023706700456481005619)
                ·
                  refine ⟨15582035560050684721508429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10388023706700456481005619 15582035560050684721508429)
                  ·
                    refine ⟨5843263335019006770565661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15582035560050684721508429 5843263335019006770565661)
                    ·
                      refine ⟨2191223750632127538962123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843263335019006770565661 2191223750632127538962123)
                      ·
                        rfl

theorem cell23_4267393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4267393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267393 prefixEnd_4267393 := by exact prefixLift 4267393
  have htrace : WordTrace (prefixWord ++ tailWord_4267393) baseStart_4267393 baseEnd_4267393 := by
    simpa [prefixWord, tailWord_4267393, baseEnd_4267393] using wordTrace_append hprefix tailTrace_4267393
  have hstable : (prefixWord ++ tailWord_4267393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267393).length < 2 ^ (prefixWord ++ tailWord_4267393).sum := by decide
  have hdescent : baseEnd_4267393 < baseStart_4267393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267426 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4267426 : Nat := 118140960795 + 4267426 * 2 ^ 59
def prefixEnd_4267426 : Nat := 4983230072969 + 3 ^ 40 * 4267426 * 2
def baseEnd_4267426 : Nat := 730413565164575303283157

theorem tailTrace_4267426 : CollatzResearch.WordTrace tailWord_4267426 prefixEnd_4267426 730413565164575303283157 := by
  unfold tailWord_4267426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911453259462973795429533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103763875358567930121145421 38911453259462973795429533)
  ·
    refine ⟨14591794972298615173286075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38911453259462973795429533 14591794972298615173286075)
    ·
      refine ⟨21887692458447922759929113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14591794972298615173286075 21887692458447922759929113)
      ·
        refine ⟨16415769343835942069946835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21887692458447922759929113 16415769343835942069946835)
        ·
          refine ⟨24623654015753913104920253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16415769343835942069946835 24623654015753913104920253)
          ·
            refine ⟨9233870255907717414345095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24623654015753913104920253 9233870255907717414345095)
            ·
              refine ⟨13850805383861576121517643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233870255907717414345095 13850805383861576121517643)
              ·
                refine ⟨20776208075792364182276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13850805383861576121517643 20776208075792364182276465)
                ·
                  refine ⟨15582156056844273136707349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20776208075792364182276465 15582156056844273136707349)
                  ·
                    refine ⟨730413565164575303283157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15582156056844273136707349 730413565164575303283157)
                    ·
                      rfl

theorem cell23_4267426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4267426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267426 prefixEnd_4267426 := by exact prefixLift 4267426
  have htrace : WordTrace (prefixWord ++ tailWord_4267426) baseStart_4267426 baseEnd_4267426 := by
    simpa [prefixWord, tailWord_4267426, baseEnd_4267426] using wordTrace_append hprefix tailTrace_4267426
  have hstable : (prefixWord ++ tailWord_4267426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267426).length < 2 ^ (prefixWord ++ tailWord_4267426).sum := by decide
  have hdescent : baseEnd_4267426 < baseStart_4267426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267456 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 5]
def baseStart_4267456 : Nat := 118140960795 + 4267456 * 2 ^ 59
def prefixEnd_4267456 : Nat := 4983230072969 + 3 ^ 40 * 4267456 * 2
def baseEnd_4267456 : Nat := 243472899990373421386037

theorem tailTrace_4267456 : CollatzResearch.WordTrace tailWord_4267456 prefixEnd_4267456 243472899990373421386037 := by
  unfold tailWord_4267456
  simp only [CollatzResearch.WordTrace]
  refine ⟨77823453613871605152655111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103764604818495473536873481 77823453613871605152655111)
  ·
    refine ⟨116735180420807407728982667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77823453613871605152655111 116735180420807407728982667)
    ·
      refine ⟨175102770631211111593474001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116735180420807407728982667 175102770631211111593474001)
      ·
        refine ⟨131327077973408333695105501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175102770631211111593474001 131327077973408333695105501)
        ·
          refine ⟨49247654240028125135664563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131327077973408333695105501 49247654240028125135664563)
          ·
            refine ⟨73871481360042187703496845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49247654240028125135664563 73871481360042187703496845)
            ·
              refine ⟨27701805510015820388811317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73871481360042187703496845 27701805510015820388811317)
              ·
                refine ⟨2597044266563983161451061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27701805510015820388811317 2597044266563983161451061)
                ·
                  refine ⟨243472899990373421386037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597044266563983161451061 243472899990373421386037)
                  ·
                    rfl

theorem cell23_4267456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 5].length) (baseStart_4267456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267456 prefixEnd_4267456 := by exact prefixLift 4267456
  have htrace : WordTrace (prefixWord ++ tailWord_4267456) baseStart_4267456 baseEnd_4267456 := by
    simpa [prefixWord, tailWord_4267456, baseEnd_4267456] using wordTrace_append hprefix tailTrace_4267456
  have hstable : (prefixWord ++ tailWord_4267456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267456).length < 2 ^ (prefixWord ++ tailWord_4267456).sum := by decide
  have hdescent : baseEnd_4267456 < baseStart_4267456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267466 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_4267466 : Nat := 118140960795 + 4267466 * 2 ^ 59
def prefixEnd_4267466 : Nat := 4983230072969 + 3 ^ 40 * 4267466 * 2
def baseEnd_4267466 : Nat := 2191261234719905753349287

theorem tailTrace_4267466 : CollatzResearch.WordTrace tailWord_4267466 prefixEnd_4267466 2191261234719905753349287 := by
  unfold tailWord_4267466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911817989426745503293563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103764847971804654675449501 38911817989426745503293563)
  ·
    refine ⟨58367726984140118254940345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38911817989426745503293563 58367726984140118254940345)
    ·
      refine ⟨43775795238105088691205259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58367726984140118254940345 43775795238105088691205259)
      ·
        refine ⟨65663692857157633036807889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43775795238105088691205259 65663692857157633036807889)
        ·
          refine ⟨49247769642868224777605917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65663692857157633036807889 49247769642868224777605917)
          ·
            refine ⟨18467913616075584291602219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49247769642868224777605917 18467913616075584291602219)
            ·
              refine ⟨27701870424113376437403329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18467913616075584291602219 27701870424113376437403329)
              ·
                refine ⟨20776402818085032328052497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27701870424113376437403329 20776402818085032328052497)
                ·
                  refine ⟨15582302113563774246039373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20776402818085032328052497 15582302113563774246039373)
                  ·
                    refine ⟨5843363292586415342264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15582302113563774246039373 5843363292586415342264765)
                    ·
                      refine ⟨2191261234719905753349287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843363292586415342264765 2191261234719905753349287)
                      ·
                        rfl

theorem cell23_4267466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_4267466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267466 prefixEnd_4267466 := by exact prefixLift 4267466
  have htrace : WordTrace (prefixWord ++ tailWord_4267466) baseStart_4267466 baseEnd_4267466 := by
    simpa [prefixWord, tailWord_4267466, baseEnd_4267466] using wordTrace_append hprefix tailTrace_4267466
  have hstable : (prefixWord ++ tailWord_4267466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267466).length < 2 ^ (prefixWord ++ tailWord_4267466).sum := by decide
  have hdescent : baseEnd_4267466 < baseStart_4267466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267479 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4267479 : Nat := 118140960795 + 4267479 * 2 ^ 59
def prefixEnd_4267479 : Nat := 4983230072969 + 3 ^ 40 * 4267479 * 2
def baseEnd_4267479 : Nat := 2191267909968414202486727

theorem tailTrace_4267479 : CollatzResearch.WordTrace tailWord_4267479 prefixEnd_4267479 2191267909968414202486727 := by
  unfold tailWord_4267479
  simp only [CollatzResearch.WordTrace]
  refine ⟨155647746106659885233397491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103765164071106590155598327 155647746106659885233397491)
  ·
    refine ⟨233471619159989827850096237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155647746106659885233397491 233471619159989827850096237)
    ·
      refine ⟨87551857184996185443786089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233471619159989827850096237 87551857184996185443786089)
      ·
        refine ⟨65663892888747139082839567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87551857184996185443786089 65663892888747139082839567)
        ·
          refine ⟨98495839333120708624259351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65663892888747139082839567 98495839333120708624259351)
          ·
            refine ⟨147743758999681062936389027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98495839333120708624259351 147743758999681062936389027)
            ·
              refine ⟨221615638499521594404583541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147743758999681062936389027 221615638499521594404583541)
              ·
                refine ⟨20776466109330149475429707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221615638499521594404583541 20776466109330149475429707)
                ·
                  refine ⟨31164699163995224213144561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20776466109330149475429707 31164699163995224213144561)
                  ·
                    refine ⟨23373524372996418159858421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31164699163995224213144561 23373524372996418159858421)
                    ·
                      refine ⟨2191267909968414202486727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23373524372996418159858421 2191267909968414202486727)
                      ·
                        rfl

theorem cell23_4267479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4267479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267479 prefixEnd_4267479 := by exact prefixLift 4267479
  have htrace : WordTrace (prefixWord ++ tailWord_4267479) baseStart_4267479 baseEnd_4267479 := by
    simpa [prefixWord, tailWord_4267479, baseEnd_4267479] using wordTrace_append hprefix tailTrace_4267479
  have hstable : (prefixWord ++ tailWord_4267479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267479).length < 2 ^ (prefixWord ++ tailWord_4267479).sum := by decide
  have hdescent : baseEnd_4267479 < baseStart_4267479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267516 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_4267516 : Nat := 118140960795 + 4267516 * 2 ^ 59
def prefixEnd_4267516 : Nat := 4983230072969 + 3 ^ 40 * 4267516 * 2
def baseEnd_4267516 : Nat := 730428969584210185908019

theorem tailTrace_4267516 : CollatzResearch.WordTrace tailWord_4267516 prefixEnd_4267516 730428969584210185908019 := by
  unfold tailWord_4267516
  simp only [CollatzResearch.WordTrace]
  refine ⟨77824547803762920276247201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103766063738350560368329601 77824547803762920276247201)
  ·
    refine ⟨58368410852822190207185401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77824547803762920276247201 58368410852822190207185401)
    ·
      refine ⟨43776308139616642655389051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58368410852822190207185401 43776308139616642655389051)
      ·
        refine ⟨65664462209424963983083577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43776308139616642655389051 65664462209424963983083577)
        ·
          refine ⟨49248346657068722987312683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65664462209424963983083577 49248346657068722987312683)
          ·
            refine ⟨73872519985603084480969025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49248346657068722987312683 73872519985603084480969025)
            ·
              refine ⟨55404389989202313360726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73872519985603084480969025 55404389989202313360726769)
              ·
                refine ⟨41553292491901735020545077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55404389989202313360726769 41553292491901735020545077)
                ·
                  refine ⟨3895621171115787658176101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41553292491901735020545077 3895621171115787658176101)
                  ·
                    refine ⟨730428969584210185908019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895621171115787658176101 730428969584210185908019)
                    ·
                      rfl

theorem cell23_4267516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_4267516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267516 prefixEnd_4267516 := by exact prefixLift 4267516
  have htrace : WordTrace (prefixWord ++ tailWord_4267516) baseStart_4267516 baseEnd_4267516 := by
    simpa [prefixWord, tailWord_4267516, baseEnd_4267516] using wordTrace_append hprefix tailTrace_4267516
  have hstable : (prefixWord ++ tailWord_4267516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267516).length < 2 ^ (prefixWord ++ tailWord_4267516).sum := by decide
  have hdescent : baseEnd_4267516 < baseStart_4267516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267519 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_4267519 : Nat := 118140960795 + 4267519 * 2 ^ 59
def prefixEnd_4267519 : Nat := 4983230072969 + 3 ^ 40 * 4267519 * 2
def baseEnd_4267519 : Nat := 2191288449194594045986543

theorem tailTrace_4267519 : CollatzResearch.WordTrace tailWord_4267519 prefixEnd_4267519 2191288449194594045986543 := by
  unfold tailWord_4267519
  simp only [CollatzResearch.WordTrace]
  refine ⟨155649205026514972064853611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103766136684343314709902407 155649205026514972064853611)
  ·
    refine ⟨233473807539772458097280417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155649205026514972064853611 233473807539772458097280417)
    ·
      refine ⟨175105355654829343572960313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233473807539772458097280417 175105355654829343572960313)
      ·
        refine ⟨131329016741122007679720235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175105355654829343572960313 131329016741122007679720235)
        ·
          refine ⟨196993525111683011519580353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131329016741122007679720235 196993525111683011519580353)
          ·
            refine ⟨147745143833762258639685265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196993525111683011519580353 147745143833762258639685265)
            ·
              refine ⟨110808857875321693979763949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147745143833762258639685265 110808857875321693979763949)
              ·
                refine ⟨41553321703245635242411481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110808857875321693979763949 41553321703245635242411481)
                ·
                  refine ⟨31164991277434226431808611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41553321703245635242411481 31164991277434226431808611)
                  ·
                    refine ⟨46747486916151339647712917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31164991277434226431808611 46747486916151339647712917)
                    ·
                      refine ⟨2191288449194594045986543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46747486916151339647712917 2191288449194594045986543)
                      ·
                        rfl

theorem cell23_4267519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_4267519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267519 prefixEnd_4267519 := by exact prefixLift 4267519
  have htrace : WordTrace (prefixWord ++ tailWord_4267519) baseStart_4267519 baseEnd_4267519 := by
    simpa [prefixWord, tailWord_4267519, baseEnd_4267519] using wordTrace_append hprefix tailTrace_4267519
  have hstable : (prefixWord ++ tailWord_4267519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267519).length < 2 ^ (prefixWord ++ tailWord_4267519).sum := by decide
  have hdescent : baseEnd_4267519 < baseStart_4267519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267529 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 8]
def baseStart_4267529 : Nat := 118140960795 + 4267529 * 2 ^ 59
def prefixEnd_4267529 : Nat := 4983230072969 + 3 ^ 40 * 4267529 * 2
def baseEnd_4267529 : Nat := 243477064889015445206833

theorem tailTrace_4267529 : CollatzResearch.WordTrace tailWord_4267529 prefixEnd_4267529 243477064889015445206833 := by
  unfold tailWord_4267529
  simp only [CollatzResearch.WordTrace]
  refine ⟨155649569756478743772717641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103766379837652495848478427 155649569756478743772717641)
  ·
    refine ⟨116737177317359057829538231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155649569756478743772717641 116737177317359057829538231)
    ·
      refine ⟨175105765976038586744307347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116737177317359057829538231 175105765976038586744307347)
      ·
        refine ⟨262658648964057880116461021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175105765976038586744307347 262658648964057880116461021)
        ·
          refine ⟨98496993361521705043672883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262658648964057880116461021 98496993361521705043672883)
          ·
            refine ⟨147745490042282557565509325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98496993361521705043672883 147745490042282557565509325)
            ·
              refine ⟨55404558765855959087065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147745490042282557565509325 55404558765855959087065997)
              ·
                refine ⟨20776709537195984657649749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55404558765855959087065997 20776709537195984657649749)
                ·
                  refine ⟨243477064889015445206833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20776709537195984657649749 243477064889015445206833)
                  ·
                    rfl

theorem cell23_4267529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_4267529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267529 prefixEnd_4267529 := by exact prefixLift 4267529
  have htrace : WordTrace (prefixWord ++ tailWord_4267529) baseStart_4267529 baseEnd_4267529 := by
    simpa [prefixWord, tailWord_4267529, baseEnd_4267529] using wordTrace_append hprefix tailTrace_4267529
  have hstable : (prefixWord ++ tailWord_4267529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267529).length < 2 ^ (prefixWord ++ tailWord_4267529).sum := by decide
  have hdescent : baseEnd_4267529 < baseStart_4267529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267624 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4267624 : Nat := 118140960795 + 4267624 * 2 ^ 59
def prefixEnd_4267624 : Nat := 4983230072969 + 3 ^ 40 * 4267624 * 2
def baseEnd_4267624 : Nat := 2191342364663316135173561

theorem tailTrace_4267624 : CollatzResearch.WordTrace tailWord_4267624 prefixEnd_4267624 2191342364663316135173561 := by
  unfold tailWord_4267624
  simp only [CollatzResearch.WordTrace]
  refine ⟨77826517345567287498712963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103768689794089716664950617 77826517345567287498712963)
  ·
    refine ⟨116739776018350931248069445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77826517345567287498712963 116739776018350931248069445)
    ·
      refine ⟨21888708003440799609013021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116739776018350931248069445 21888708003440799609013021)
      ·
        refine ⟨8208265501290299853379883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21888708003440799609013021 8208265501290299853379883)
        ·
          refine ⟨12312398251935449780069825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208265501290299853379883 12312398251935449780069825)
          ·
            refine ⟨9234298688951587335052369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12312398251935449780069825 9234298688951587335052369)
            ·
              refine ⟨6925724016713690501289277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9234298688951587335052369 6925724016713690501289277)
              ·
                refine ⟨2597146506267633937983479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6925724016713690501289277 2597146506267633937983479)
                ·
                  refine ⟨3895719759401450906975219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597146506267633937983479 3895719759401450906975219)
                  ·
                    refine ⟨5843579639102176360462829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895719759401450906975219 5843579639102176360462829)
                    ·
                      refine ⟨2191342364663316135173561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843579639102176360462829 2191342364663316135173561)
                      ·
                        rfl

theorem cell23_4267624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4267624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267624 prefixEnd_4267624 := by exact prefixLift 4267624
  have htrace : WordTrace (prefixWord ++ tailWord_4267624) baseStart_4267624 baseEnd_4267624 := by
    simpa [prefixWord, tailWord_4267624, baseEnd_4267624] using wordTrace_append hprefix tailTrace_4267624
  have hstable : (prefixWord ++ tailWord_4267624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267624).length < 2 ^ (prefixWord ++ tailWord_4267624).sum := by decide
  have hdescent : baseEnd_4267624 < baseStart_4267624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267663 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_4267663 : Nat := 118140960795 + 4267663 * 2 ^ 59
def prefixEnd_4267663 : Nat := 4983230072969 + 3 ^ 40 * 4267663 * 2
def baseEnd_4267663 : Nat := 2191362390408841482585881

theorem tailTrace_4267663 : CollatzResearch.WordTrace tailWord_4267663 prefixEnd_4267663 2191362390408841482585881 := by
  unfold tailWord_4267663
  simp only [CollatzResearch.WordTrace]
  refine ⟨155654457137993284658095643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103769638091995523105397095 155654457137993284658095643)
  ·
    refine ⟨233481685706989926987143465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155654457137993284658095643 233481685706989926987143465)
    ·
      refine ⟨175111264280242445240357599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233481685706989926987143465 175111264280242445240357599)
      ·
        refine ⟨262666896420363667860536399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175111264280242445240357599 262666896420363667860536399)
        ·
          refine ⟨394000344630545501790804599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262666896420363667860536399 394000344630545501790804599)
          ·
            refine ⟨591000516945818252686206899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394000344630545501790804599 591000516945818252686206899)
            ·
              refine ⟨886500775418727379029310349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591000516945818252686206899 886500775418727379029310349)
              ·
                refine ⟨332437790782022767135991381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 886500775418727379029310349 332437790782022767135991381)
                ·
                  refine ⟨3895755360726829302374899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 332437790782022767135991381 3895755360726829302374899)
                  ·
                    refine ⟨5843633041090243953562349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895755360726829302374899 5843633041090243953562349)
                    ·
                      refine ⟨2191362390408841482585881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843633041090243953562349 2191362390408841482585881)
                      ·
                        rfl

theorem cell23_4267663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_4267663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267663 prefixEnd_4267663 := by exact prefixLift 4267663
  have htrace : WordTrace (prefixWord ++ tailWord_4267663) baseStart_4267663 baseEnd_4267663 := by
    simpa [prefixWord, tailWord_4267663, baseEnd_4267663] using wordTrace_append hprefix tailTrace_4267663
  have hstable : (prefixWord ++ tailWord_4267663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267663).length < 2 ^ (prefixWord ++ tailWord_4267663).sum := by decide
  have hdescent : baseEnd_4267663 < baseStart_4267663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267680 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4267680 : Nat := 118140960795 + 4267680 * 2 ^ 59
def prefixEnd_4267680 : Nat := 4983230072969 + 3 ^ 40 * 4267680 * 2
def baseEnd_4267680 : Nat := 2191371119579967916073303

theorem tailTrace_4267680 : CollatzResearch.WordTrace tailWord_4267680 prefixEnd_4267680 2191371119579967916073303 := by
  unfold tailWord_4267680
  simp only [CollatzResearch.WordTrace]
  refine ⟨77827538589465848280732247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103770051452621131040976329 77827538589465848280732247)
  ·
    refine ⟨116741307884198772421098371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77827538589465848280732247 116741307884198772421098371)
    ·
      refine ⟨175111961826298158631647557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116741307884198772421098371 175111961826298158631647557)
      ·
        refine ⟨32833492842430904743433917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175111961826298158631647557 32833492842430904743433917)
        ·
          refine ⟨12312559815911589278787719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32833492842430904743433917 12312559815911589278787719)
          ·
            refine ⟨18468839723867383918181579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12312559815911589278787719 18468839723867383918181579)
            ·
              refine ⟨27703259585801075877272369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18468839723867383918181579 27703259585801075877272369)
              ·
                refine ⟨20777444689350806907954277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27703259585801075877272369 20777444689350806907954277)
                ·
                  refine ⟨3895770879253276295241427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20777444689350806907954277 3895770879253276295241427)
                  ·
                    refine ⟨5843656318879914442862141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895770879253276295241427 5843656318879914442862141)
                    ·
                      refine ⟨2191371119579967916073303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843656318879914442862141 2191371119579967916073303)
                      ·
                        rfl

theorem cell23_4267680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4267680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267680 prefixEnd_4267680 := by exact prefixLift 4267680
  have htrace : WordTrace (prefixWord ++ tailWord_4267680) baseStart_4267680 baseEnd_4267680 := by
    simpa [prefixWord, tailWord_4267680, baseEnd_4267680] using wordTrace_append hprefix tailTrace_4267680
  have hstable : (prefixWord ++ tailWord_4267680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267680).length < 2 ^ (prefixWord ++ tailWord_4267680).sum := by decide
  have hdescent : baseEnd_4267680 < baseStart_4267680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267681 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4267681 : Nat := 118140960795 + 4267681 * 2 ^ 59
def prefixEnd_4267681 : Nat := 4983230072969 + 3 ^ 40 * 4267681 * 2
def baseEnd_4267681 : Nat := 2191371633060622412160799

theorem tailTrace_4267681 : CollatzResearch.WordTrace tailWord_4267681 prefixEnd_4267681 2191371633060622412160799 := by
  unfold tailWord_4267681
  simp only [CollatzResearch.WordTrace]
  refine ⟨155655113651928073732250897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103770075767952049154833931 155655113651928073732250897)
  ·
    refine ⟨116741335238946055299188173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155655113651928073732250897 116741335238946055299188173)
    ·
      refine ⟨43778000714604770737195565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116741335238946055299188173 43778000714604770737195565)
      ·
        refine ⟨16416750267976789026448337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43778000714604770737195565 16416750267976789026448337)
        ·
          refine ⟨12312562700982591769836253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16416750267976789026448337 12312562700982591769836253)
          ·
            refine ⟨4617211012868471913688595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12312562700982591769836253 4617211012868471913688595)
            ·
              refine ⟨6925816519302707870532893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617211012868471913688595 6925816519302707870532893)
              ·
                refine ⟨2597181194738515451449835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6925816519302707870532893 2597181194738515451449835)
                ·
                  refine ⟨3895771792107773177174753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597181194738515451449835 3895771792107773177174753)
                  ·
                    refine ⟨2921828844080829882881065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895771792107773177174753 2921828844080829882881065)
                    ·
                      refine ⟨2191371633060622412160799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921828844080829882881065 2191371633060622412160799)
                      ·
                        rfl

theorem cell23_4267681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4267681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267681 prefixEnd_4267681 := by exact prefixLift 4267681
  have htrace : WordTrace (prefixWord ++ tailWord_4267681) baseStart_4267681 baseEnd_4267681 := by
    simpa [prefixWord, tailWord_4267681, baseEnd_4267681] using wordTrace_append hprefix tailTrace_4267681
  have hstable : (prefixWord ++ tailWord_4267681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267681).length < 2 ^ (prefixWord ++ tailWord_4267681).sum := by decide
  have hdescent : baseEnd_4267681 < baseStart_4267681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267693 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4267693 : Nat := 118140960795 + 4267693 * 2 ^ 59
def prefixEnd_4267693 : Nat := 4983230072969 + 3 ^ 40 * 4267693 * 2
def baseEnd_4267693 : Nat := 2191377794828476365210743

theorem tailTrace_4267693 : CollatzResearch.WordTrace tailWord_4267693 prefixEnd_4267693 2191377794828476365210743 := by
  unfold tailWord_4267693
  simp only [CollatzResearch.WordTrace]
  refine ⟨155655551327884599781687733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103770367551923066521125155 155655551327884599781687733)
  ·
    refine ⟨14592707936989181229533225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155655551327884599781687733 14592707936989181229533225)
    ·
      refine ⟨10944530952741885922149919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14592707936989181229533225 10944530952741885922149919)
      ·
        refine ⟨16416796429112828883224879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10944530952741885922149919 16416796429112828883224879)
        ·
          refine ⟨24625194643669243324837319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16416796429112828883224879 24625194643669243324837319)
          ·
            refine ⟨36937791965503864987255979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24625194643669243324837319 36937791965503864987255979)
            ·
              refine ⟨55406687948255797480883969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36937791965503864987255979 55406687948255797480883969)
              ·
                refine ⟨41555015961191848110662977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55406687948255797480883969 41555015961191848110662977)
                ·
                  refine ⟨31166261970893886082997233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41555015961191848110662977 31166261970893886082997233)
                  ·
                    refine ⟨23374696478170414562247925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31166261970893886082997233 23374696478170414562247925)
                    ·
                      refine ⟨2191377794828476365210743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23374696478170414562247925 2191377794828476365210743)
                      ·
                        rfl

theorem cell23_4267693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4267693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267693 prefixEnd_4267693 := by exact prefixLift 4267693
  have htrace : WordTrace (prefixWord ++ tailWord_4267693) baseStart_4267693 baseEnd_4267693 := by
    simpa [prefixWord, tailWord_4267693, baseEnd_4267693] using wordTrace_append hprefix tailTrace_4267693
  have hstable : (prefixWord ++ tailWord_4267693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267693).length < 2 ^ (prefixWord ++ tailWord_4267693).sum := by decide
  have hdescent : baseEnd_4267693 < baseStart_4267693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267696 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_4267696 : Nat := 118140960795 + 4267696 * 2 ^ 59
def prefixEnd_4267696 : Nat := 4983230072969 + 3 ^ 40 * 4267696 * 2
def baseEnd_4267696 : Nat := 730459778423479951157743

theorem tailTrace_4267696 : CollatzResearch.WordTrace tailWord_4267696 prefixEnd_4267696 730459778423479951157743 := by
  unfold tailWord_4267696
  simp only [CollatzResearch.WordTrace]
  refine ⟨77827830373436865647023471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103770440497915820862697961 77827830373436865647023471)
  ·
    refine ⟨116741745560155298470535207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77827830373436865647023471 116741745560155298470535207)
    ·
      refine ⟨175112618340232947705802811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116741745560155298470535207 175112618340232947705802811)
      ·
        refine ⟨262668927510349421558704217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175112618340232947705802811 262668927510349421558704217)
        ·
          refine ⟨197001695632762066169028163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262668927510349421558704217 197001695632762066169028163)
          ·
            refine ⟨295502543449143099253542245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197001695632762066169028163 295502543449143099253542245)
            ·
              refine ⟨55406726896714331110039171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 295502543449143099253542245 55406726896714331110039171)
              ·
                refine ⟨83110090345071496665058757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55406726896714331110039171 83110090345071496665058757)
                ·
                  refine ⟨15583141939700905624698517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83110090345071496665058757 15583141939700905624698517)
                  ·
                    refine ⟨730459778423479951157743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15583141939700905624698517 730459778423479951157743)
                    ·
                      rfl

theorem cell23_4267696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_4267696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267696 prefixEnd_4267696 := by exact prefixLift 4267696
  have htrace : WordTrace (prefixWord ++ tailWord_4267696) baseStart_4267696 baseEnd_4267696 := by
    simpa [prefixWord, tailWord_4267696, baseEnd_4267696] using wordTrace_append hprefix tailTrace_4267696
  have hstable : (prefixWord ++ tailWord_4267696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267696).length < 2 ^ (prefixWord ++ tailWord_4267696).sum := by decide
  have hdescent : baseEnd_4267696 < baseStart_4267696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267720 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_4267720 : Nat := 118140960795 + 4267720 * 2 ^ 59
def prefixEnd_4267720 : Nat := 4983230072969 + 3 ^ 40 * 4267720 * 2
def baseEnd_4267720 : Nat := 2191391658806147759573119

theorem tailTrace_4267720 : CollatzResearch.WordTrace tailWord_4267720 prefixEnd_4267720 2191391658806147759573119 := by
  unfold tailWord_4267720
  simp only [CollatzResearch.WordTrace]
  refine ⟨77828268049393391696460307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103771024065857855595280409 77828268049393391696460307)
  ·
    refine ⟨116742402074090087544690461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77828268049393391696460307 116742402074090087544690461)
    ·
      refine ⟨43778400777783782829258923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116742402074090087544690461 43778400777783782829258923)
      ·
        refine ⟨65667601166675674243888385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43778400777783782829258923 65667601166675674243888385)
        ·
          refine ⟨49250700875006755682916289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65667601166675674243888385 49250700875006755682916289)
          ·
            refine ⟨36938025656255066762187217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49250700875006755682916289 36938025656255066762187217)
            ·
              refine ⟨27703519242191300071640413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36938025656255066762187217 27703519242191300071640413)
              ·
                refine ⟨10388819715821737526865155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27703519242191300071640413 10388819715821737526865155)
                ·
                  refine ⟨15583229573732606290297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10388819715821737526865155 15583229573732606290297733)
                  ·
                    refine ⟨2921855545074863679430825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15583229573732606290297733 2921855545074863679430825)
                    ·
                      refine ⟨2191391658806147759573119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2921855545074863679430825 2191391658806147759573119)
                      ·
                        rfl

theorem cell23_4267720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_4267720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267720 prefixEnd_4267720 := by exact prefixLift 4267720
  have htrace : WordTrace (prefixWord ++ tailWord_4267720) baseStart_4267720 baseEnd_4267720 := by
    simpa [prefixWord, tailWord_4267720, baseEnd_4267720] using wordTrace_append hprefix tailTrace_4267720
  have hstable : (prefixWord ++ tailWord_4267720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267720).length < 2 ^ (prefixWord ++ tailWord_4267720).sum := by decide
  have hdescent : baseEnd_4267720 < baseStart_4267720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267753 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_4267753 : Nat := 118140960795 + 4267753 * 2 ^ 59
def prefixEnd_4267753 : Nat := 4983230072969 + 3 ^ 40 * 4267753 * 2
def baseEnd_4267753 : Nat := 2191408603667746130460467

theorem tailTrace_4267753 : CollatzResearch.WordTrace tailWord_4267753 prefixEnd_4267753 2191408603667746130460467 := by
  unfold tailWord_4267753
  simp only [CollatzResearch.WordTrace]
  refine ⟨155657739707667230028871913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103771826471778153352581275 155657739707667230028871913)
  ·
    refine ⟨116743304780750422521653935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155657739707667230028871913 116743304780750422521653935)
    ·
      refine ⟨175114957171125633782480903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116743304780750422521653935 175114957171125633782480903)
      ·
        refine ⟨262672435756688450673721355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175114957171125633782480903 262672435756688450673721355)
        ·
          refine ⟨394008653635032676010582033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262672435756688450673721355 394008653635032676010582033)
          ·
            refine ⟨295506490226274507007936525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394008653635032676010582033 295506490226274507007936525)
            ·
              refine ⟨110814933834852940127976197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295506490226274507007936525 110814933834852940127976197)
              ·
                refine ⟨20777800094034926273995537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110814933834852940127976197 20777800094034926273995537)
                ·
                  refine ⟨15583350070526194705496653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20777800094034926273995537 15583350070526194705496653)
                  ·
                    refine ⟨5843756276447323014561245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15583350070526194705496653 5843756276447323014561245)
                    ·
                      refine ⟨2191408603667746130460467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843756276447323014561245 2191408603667746130460467)
                      ·
                        rfl

theorem cell23_4267753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_4267753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267753 prefixEnd_4267753 := by exact prefixLift 4267753
  have htrace : WordTrace (prefixWord ++ tailWord_4267753) baseStart_4267753 baseEnd_4267753 := by
    simpa [prefixWord, tailWord_4267753, baseEnd_4267753] using wordTrace_append hprefix tailTrace_4267753
  have hstable : (prefixWord ++ tailWord_4267753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267753).length < 2 ^ (prefixWord ++ tailWord_4267753).sum := by decide
  have hdescent : baseEnd_4267753 < baseStart_4267753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267790 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_4267790 : Nat := 118140960795 + 4267790 * 2 ^ 59
def prefixEnd_4267790 : Nat := 4983230072969 + 3 ^ 40 * 4267790 * 2
def baseEnd_4267790 : Nat := 730475867483987495232599

theorem tailTrace_4267790 : CollatzResearch.WordTrace tailWord_4267790 prefixEnd_4267790 730475867483987495232599 := by
  unfold tailWord_4267790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457386151066648168496103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103772726139022123565312549 19457386151066648168496103)
  ·
    refine ⟨29186079226599972252744155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19457386151066648168496103 29186079226599972252744155)
    ·
      refine ⟨43779118839899958379116233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29186079226599972252744155 43779118839899958379116233)
      ·
        refine ⟨32834339129924968784337175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43779118839899958379116233 32834339129924968784337175)
        ·
          refine ⟨49251508694887453176505763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32834339129924968784337175 49251508694887453176505763)
          ·
            refine ⟨73877263042331179764758645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49251508694887453176505763 73877263042331179764758645)
            ·
              refine ⟨6925993410218548102946123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73877263042331179764758645 6925993410218548102946123)
              ·
                refine ⟨10388990115327822154419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925993410218548102946123 10388990115327822154419185)
                ·
                  refine ⟨7791742586495866615814389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10388990115327822154419185 7791742586495866615814389)
                  ·
                    refine ⟨730475867483987495232599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7791742586495866615814389 730475867483987495232599)
                    ·
                      rfl

theorem cell23_4267790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_4267790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267790 prefixEnd_4267790 := by exact prefixLift 4267790
  have htrace : WordTrace (prefixWord ++ tailWord_4267790) baseStart_4267790 baseEnd_4267790 := by
    simpa [prefixWord, tailWord_4267790, baseEnd_4267790] using wordTrace_append hprefix tailTrace_4267790
  have hstable : (prefixWord ++ tailWord_4267790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267790).length < 2 ^ (prefixWord ++ tailWord_4267790).sum := by decide
  have hdescent : baseEnd_4267790 < baseStart_4267790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267794 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_4267794 : Nat := 118140960795 + 4267794 * 2 ^ 59
def prefixEnd_4267794 : Nat := 4983230072969 + 3 ^ 40 * 4267794 * 2
def baseEnd_4267794 : Nat := 243492184041620052227531

theorem tailTrace_4267794 : CollatzResearch.WordTrace tailWord_4267794 prefixEnd_4267794 243492184041620052227531 := by
  unfold tailWord_4267794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38914808775129673507778609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103772823400345796020742957 38914808775129673507778609)
  ·
    refine ⟨29186106581347255130833957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38914808775129673507778609 29186106581347255130833957)
    ·
      refine ⟨5472394984002610337031367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29186106581347255130833957 5472394984002610337031367)
      ·
        refine ⟨8208592476003915505547051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472394984002610337031367 8208592476003915505547051)
        ·
          refine ⟨12312888714005873258320577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208592476003915505547051 12312888714005873258320577)
          ·
            refine ⟨9234666535504404943740433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12312888714005873258320577 9234666535504404943740433)
            ·
              refine ⟨6925999901628303707805325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9234666535504404943740433 6925999901628303707805325)
              ·
                refine ⟨2597249963110613890426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6925999901628303707805325 2597249963110613890426997)
                ·
                  refine ⟨243492184041620052227531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597249963110613890426997 243492184041620052227531)
                  ·
                    rfl

theorem cell23_4267794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_4267794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267794 prefixEnd_4267794 := by exact prefixLift 4267794
  have htrace : WordTrace (prefixWord ++ tailWord_4267794) baseStart_4267794 baseEnd_4267794 := by
    simpa [prefixWord, tailWord_4267794, baseEnd_4267794] using wordTrace_append hprefix tailTrace_4267794
  have hstable : (prefixWord ++ tailWord_4267794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267794).length < 2 ^ (prefixWord ++ tailWord_4267794).sum := by decide
  have hdescent : baseEnd_4267794 < baseStart_4267794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267810 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4267810 : Nat := 118140960795 + 4267810 * 2 ^ 59
def prefixEnd_4267810 : Nat := 4983230072969 + 3 ^ 40 * 4267810 * 2
def baseEnd_4267810 : Nat := 2191437872065052407447705

theorem tailTrace_4267810 : CollatzResearch.WordTrace tailWord_4267810 prefixEnd_4267810 2191437872065052407447705 := by
  unfold tailWord_4267810
  simp only [CollatzResearch.WordTrace]
  refine ⟨38914954667115182190924221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103773212445640485842464589 38914954667115182190924221)
  ·
    refine ⟨14593108000168193321596583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38914954667115182190924221 14593108000168193321596583)
    ·
      refine ⟨21889662000252289982394875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14593108000168193321596583 21889662000252289982394875)
      ·
        refine ⟨32834493000378434973592313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21889662000252289982394875 32834493000378434973592313)
        ·
          refine ⟨24625869750283826230194235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32834493000378434973592313 24625869750283826230194235)
          ·
            refine ⟨36938804625425739345291353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24625869750283826230194235 36938804625425739345291353)
            ·
              refine ⟨27704103469069304508968515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36938804625425739345291353 27704103469069304508968515)
              ·
                refine ⟨41556155203603956763452773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27704103469069304508968515 41556155203603956763452773)
                ·
                  refine ⟨7791779100675741893147395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41556155203603956763452773 7791779100675741893147395)
                  ·
                    refine ⟨11687668651013612839721093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7791779100675741893147395 11687668651013612839721093)
                    ·
                      refine ⟨2191437872065052407447705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11687668651013612839721093 2191437872065052407447705)
                      ·
                        rfl

theorem cell23_4267810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4267810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267810 prefixEnd_4267810 := by exact prefixLift 4267810
  have htrace : WordTrace (prefixWord ++ tailWord_4267810) baseStart_4267810 baseEnd_4267810 := by
    simpa [prefixWord, tailWord_4267810, baseEnd_4267810] using wordTrace_append hprefix tailTrace_4267810
  have hstable : (prefixWord ++ tailWord_4267810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267810).length < 2 ^ (prefixWord ++ tailWord_4267810).sum := by decide
  have hdescent : baseEnd_4267810 < baseStart_4267810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267820 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_4267820 : Nat := 118140960795 + 4267820 * 2 ^ 59
def prefixEnd_4267820 : Nat := 4983230072969 + 3 ^ 40 * 4267820 * 2
def baseEnd_4267820 : Nat := 730481002290532456107553

theorem tailTrace_4267820 : CollatzResearch.WordTrace tailWord_4267820 prefixEnd_4267820 730481002290532456107553 := by
  unfold tailWord_4267820
  simp only [CollatzResearch.WordTrace]
  refine ⟨77830091699212250235780457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103773455598949666981040609 77830091699212250235780457)
  ·
    refine ⟨58372568774409187676835343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77830091699212250235780457 58372568774409187676835343)
    ·
      refine ⟨87558853161613781515253015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58372568774409187676835343 87558853161613781515253015)
      ·
        refine ⟨131338279742420672272879523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87558853161613781515253015 131338279742420672272879523)
        ·
          refine ⟨197007419613631008409319285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131338279742420672272879523 197007419613631008409319285)
          ·
            refine ⟨18469445588777907038373683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197007419613631008409319285 18469445588777907038373683)
            ·
              refine ⟨27704168383166860557560525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18469445588777907038373683 27704168383166860557560525)
              ·
                refine ⟨10389063143687572709085197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27704168383166860557560525 10389063143687572709085197)
                ·
                  refine ⟨3895898678882839765906949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10389063143687572709085197 3895898678882839765906949)
                  ·
                    refine ⟨730481002290532456107553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895898678882839765906949 730481002290532456107553)
                    ·
                      rfl

theorem cell23_4267820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_4267820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267820 prefixEnd_4267820 := by exact prefixLift 4267820
  have htrace : WordTrace (prefixWord ++ tailWord_4267820) baseStart_4267820 baseEnd_4267820 := by
    simpa [prefixWord, tailWord_4267820, baseEnd_4267820] using wordTrace_append hprefix tailTrace_4267820
  have hstable : (prefixWord ++ tailWord_4267820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267820).length < 2 ^ (prefixWord ++ tailWord_4267820).sum := by decide
  have hdescent : baseEnd_4267820 < baseStart_4267820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267837 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_4267837 : Nat := 118140960795 + 4267837 * 2 ^ 59
def prefixEnd_4267837 : Nat := 4983230072969 + 3 ^ 40 * 4267837 * 2
def baseEnd_4267837 : Nat := 730483912014241267270027

theorem tailTrace_4267837 : CollatzResearch.WordTrace tailWord_4267837 prefixEnd_4267837 730483912014241267270027 := by
  unfold tailWord_4267837
  simp only [CollatzResearch.WordTrace]
  refine ⟨155660803439362912374929765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103773868959575274916619843 155660803439362912374929765)
  ·
    refine ⟨29186400644880546070299331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155660803439362912374929765 29186400644880546070299331)
    ·
      refine ⟨43779600967320819105448997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29186400644880546070299331 43779600967320819105448997)
      ·
        refine ⟨8208675181372653582271687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43779600967320819105448997 8208675181372653582271687)
        ·
          refine ⟨12313012772058980373407531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208675181372653582271687 12313012772058980373407531)
          ·
            refine ⟨18469519158088470560111297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12313012772058980373407531 18469519158088470560111297)
            ·
              refine ⟨13852139368566352920083473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18469519158088470560111297 13852139368566352920083473)
              ·
                refine ⟨10389104526424764690062605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13852139368566352920083473 10389104526424764690062605)
                ·
                  refine ⟨3895914197409286758773477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10389104526424764690062605 3895914197409286758773477)
                  ·
                    refine ⟨730483912014241267270027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895914197409286758773477 730483912014241267270027)
                    ·
                      rfl

theorem cell23_4267837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_4267837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267837 prefixEnd_4267837 := by exact prefixLift 4267837
  have htrace : WordTrace (prefixWord ++ tailWord_4267837) baseStart_4267837 baseEnd_4267837 := by
    simpa [prefixWord, tailWord_4267837, baseEnd_4267837] using wordTrace_append hprefix tailTrace_4267837
  have hstable : (prefixWord ++ tailWord_4267837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267837).length < 2 ^ (prefixWord ++ tailWord_4267837).sum := by decide
  have hdescent : baseEnd_4267837 < baseStart_4267837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267880 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_4267880 : Nat := 118140960795 + 4267880 * 2 ^ 59
def prefixEnd_4267880 : Nat := 4983230072969 + 3 ^ 40 * 4267880 * 2
def baseEnd_4267880 : Nat := 730491271903622377857461

theorem tailTrace_4267880 : CollatzResearch.WordTrace tailWord_4267880 prefixEnd_4267880 730491271903622377857461 := by
  unfold tailWord_4267880
  simp only [CollatzResearch.WordTrace]
  refine ⟨77831185889103565359372547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103774914518804753812496729 77831185889103565359372547)
  ·
    refine ⟨116746778833655348039058821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77831185889103565359372547 116746778833655348039058821)
    ·
      refine ⟨21890021031310377757323529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116746778833655348039058821 21890021031310377757323529)
      ·
        refine ⟨16417515773482783317992647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21890021031310377757323529 16417515773482783317992647)
        ·
          refine ⟨24626273660224174976988971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16417515773482783317992647 24626273660224174976988971)
          ·
            refine ⟨36939410490336262465483457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24626273660224174976988971 36939410490336262465483457)
            ·
              refine ⟨27704557867752196849112593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36939410490336262465483457 27704557867752196849112593)
              ·
                refine ⟨20778418400814147636834445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27704557867752196849112593 20778418400814147636834445)
                ·
                  refine ⟨7791906900305305363812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20778418400814147636834445 7791906900305305363812917)
                  ·
                    refine ⟨730491271903622377857461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7791906900305305363812917 730491271903622377857461)
                    ·
                      rfl

theorem cell23_4267880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_4267880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267880 prefixEnd_4267880 := by exact prefixLift 4267880
  have htrace : WordTrace (prefixWord ++ tailWord_4267880) baseStart_4267880 baseEnd_4267880 := by
    simpa [prefixWord, tailWord_4267880, baseEnd_4267880] using wordTrace_append hprefix tailTrace_4267880
  have hstable : (prefixWord ++ tailWord_4267880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267880).length < 2 ^ (prefixWord ++ tailWord_4267880).sum := by decide
  have hdescent : baseEnd_4267880 < baseStart_4267880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267883 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_4267883 : Nat := 118140960795 + 4267883 * 2 ^ 59
def prefixEnd_4267883 : Nat := 4983230072969 + 3 ^ 40 * 4267883 * 2
def baseEnd_4267883 : Nat := 2191475356152830621834869

theorem tailTrace_4267883 : CollatzResearch.WordTrace tailWord_4267883 prefixEnd_4267883 2191475356152830621834869 := by
  unfold tailWord_4267883
  simp only [CollatzResearch.WordTrace]
  refine ⟨155662481197196262231104303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103774987464797508154069535 155662481197196262231104303)
  ·
    refine ⟨233493721795794393346656455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155662481197196262231104303 233493721795794393346656455)
    ·
      refine ⟨350240582693691590019984683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233493721795794393346656455 350240582693691590019984683)
      ·
        refine ⟨525360874040537385029977025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350240582693691590019984683 525360874040537385029977025)
        ·
          refine ⟨394020655530403038772482769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525360874040537385029977025 394020655530403038772482769)
          ·
            refine ⟨295515491647802279079362077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394020655530403038772482769 295515491647802279079362077)
            ·
              refine ⟨110818309367925854654760779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295515491647802279079362077 110818309367925854654760779)
              ·
                refine ⟨166227464051888781982141169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110818309367925854654760779 166227464051888781982141169)
                ·
                  refine ⟨124670598038916586486605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166227464051888781982141169 124670598038916586486605877)
                  ·
                    refine ⟨11687868566148429983119301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124670598038916586486605877 11687868566148429983119301)
                    ·
                      refine ⟨2191475356152830621834869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11687868566148429983119301 2191475356152830621834869)
                      ·
                        rfl

theorem cell23_4267883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_4267883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267883 prefixEnd_4267883 := by exact prefixLift 4267883
  have htrace : WordTrace (prefixWord ++ tailWord_4267883) baseStart_4267883 baseEnd_4267883 := by
    simpa [prefixWord, tailWord_4267883, baseEnd_4267883] using wordTrace_append hprefix tailTrace_4267883
  have hstable : (prefixWord ++ tailWord_4267883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267883).length < 2 ^ (prefixWord ++ tailWord_4267883).sum := by decide
  have hdescent : baseEnd_4267883 < baseStart_4267883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_4267920 : Nat := 118140960795 + 4267920 * 2 ^ 59
def prefixEnd_4267920 : Nat := 4983230072969 + 3 ^ 40 * 4267920 * 2
def baseEnd_4267920 : Nat := 2191494354937046977072199

theorem tailTrace_4267920 : CollatzResearch.WordTrace tailWord_4267920 prefixEnd_4267920 2191494354937046977072199 := by
  unfold tailWord_4267920
  simp only [CollatzResearch.WordTrace]
  refine ⟨77831915349031108775100607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103775887132041478366800809 77831915349031108775100607)
  ·
    refine ⟨116747873023546663162650911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77831915349031108775100607 116747873023546663162650911)
    ·
      refine ⟨175121809535319994743976367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116747873023546663162650911 175121809535319994743976367)
      ·
        refine ⟨262682714302979992115964551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175121809535319994743976367 262682714302979992115964551)
        ·
          refine ⟨394024071454469988173946827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262682714302979992115964551 394024071454469988173946827)
          ·
            refine ⟨591036107181704982260920241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394024071454469988173946827 591036107181704982260920241)
            ·
              refine ⟨443277080386278736695690181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591036107181704982260920241 443277080386278736695690181)
              ·
                refine ⟨83114452572427263130441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443277080386278736695690181 83114452572427263130441909)
                ·
                  refine ⟨7791979928665055918478929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83114452572427263130441909 7791979928665055918478929)
                  ·
                    refine ⟨5843984946498791938859197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7791979928665055918478929 5843984946498791938859197)
                    ·
                      refine ⟨2191494354937046977072199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843984946498791938859197 2191494354937046977072199)
                      ·
                        rfl

theorem cell23_4267920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_4267920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267920 prefixEnd_4267920 := by exact prefixLift 4267920
  have htrace : WordTrace (prefixWord ++ tailWord_4267920) baseStart_4267920 baseEnd_4267920 := by
    simpa [prefixWord, tailWord_4267920, baseEnd_4267920] using wordTrace_append hprefix tailTrace_4267920
  have hstable : (prefixWord ++ tailWord_4267920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267920).length < 2 ^ (prefixWord ++ tailWord_4267920).sum := by decide
  have hdescent : baseEnd_4267920 < baseStart_4267920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267927 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 2, 4]
def baseStart_4267927 : Nat := 118140960795 + 4267927 * 2 ^ 59
def prefixEnd_4267927 : Nat := 4983230072969 + 3 ^ 40 * 4267927 * 2
def baseEnd_4267927 : Nat := 730499316433876149894889

theorem tailTrace_4267927 : CollatzResearch.WordTrace tailWord_4267927 prefixEnd_4267927 730499316433876149894889 := by
  unfold tailWord_4267927
  simp only [CollatzResearch.WordTrace]
  refine ⟨155664086009036857745706035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103776057339357905163804023 155664086009036857745706035)
  ·
    refine ⟨233496129013555286618559053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155664086009036857745706035 233496129013555286618559053)
    ·
      refine ⟨87561048380083232481959645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233496129013555286618559053 87561048380083232481959645)
      ·
        refine ⟨32835393142531212180734867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87561048380083232481959645 32835393142531212180734867)
        ·
          refine ⟨49253089713796818271102301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32835393142531212180734867 49253089713796818271102301)
          ·
            refine ⟨18469908642673806851663363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49253089713796818271102301 18469908642673806851663363)
            ·
              refine ⟨27704862964010710277495045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18469908642673806851663363 27704862964010710277495045)
              ·
                refine ⟨5194661805752008177030321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27704862964010710277495045 5194661805752008177030321)
                ·
                  refine ⟨3895996354314006132772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194661805752008177030321 3895996354314006132772741)
                  ·
                    refine ⟨730499316433876149894889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895996354314006132772741 730499316433876149894889)
                    ·
                      rfl

theorem cell23_4267927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_4267927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267927 prefixEnd_4267927 := by exact prefixLift 4267927
  have htrace : WordTrace (prefixWord ++ tailWord_4267927) baseStart_4267927 baseEnd_4267927 := by
    simpa [prefixWord, tailWord_4267927, baseEnd_4267927] using wordTrace_append hprefix tailTrace_4267927
  have hstable : (prefixWord ++ tailWord_4267927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267927).length < 2 ^ (prefixWord ++ tailWord_4267927).sum := by decide
  have hdescent : baseEnd_4267927 < baseStart_4267927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267928 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4267928 : Nat := 118140960795 + 4267928 * 2 ^ 59
def prefixEnd_4267928 : Nat := 4983230072969 + 3 ^ 40 * 4267928 * 2
def baseEnd_4267928 : Nat := 2191498462782282945772163

theorem tailTrace_4267928 : CollatzResearch.WordTrace tailWord_4267928 prefixEnd_4267928 2191498462782282945772163 := by
  unfold tailWord_4267928
  simp only [CollatzResearch.WordTrace]
  refine ⟨77832061241016617458246219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103776081654688823277661625 77832061241016617458246219)
  ·
    refine ⟨116748091861524926187369329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77832061241016617458246219 116748091861524926187369329)
    ·
      refine ⟨87561068896143694640526997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116748091861524926187369329 87561068896143694640526997)
      ·
        refine ⟨4104425104506735686274703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87561068896143694640526997 4104425104506735686274703)
        ·
          refine ⟨6156637656760103529412055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104425104506735686274703 6156637656760103529412055)
          ·
            refine ⟨9234956485140155294118083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156637656760103529412055 9234956485140155294118083)
            ·
              refine ⟨13852434727710232941177125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9234956485140155294118083 13852434727710232941177125)
              ·
                refine ⟨2597331511445668676470711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13852434727710232941177125 2597331511445668676470711)
                ·
                  refine ⟨3895997267168503014706067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597331511445668676470711 3895997267168503014706067)
                  ·
                    refine ⟨5843995900752754522059101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895997267168503014706067 5843995900752754522059101)
                    ·
                      refine ⟨2191498462782282945772163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5843995900752754522059101 2191498462782282945772163)
                      ·
                        rfl

theorem cell23_4267928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4267928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267928 prefixEnd_4267928 := by exact prefixLift 4267928
  have htrace : WordTrace (prefixWord ++ tailWord_4267928) baseStart_4267928 baseEnd_4267928 := by
    simpa [prefixWord, tailWord_4267928, baseEnd_4267928] using wordTrace_append hprefix tailTrace_4267928
  have hstable : (prefixWord ++ tailWord_4267928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267928).length < 2 ^ (prefixWord ++ tailWord_4267928).sum := by decide
  have hdescent : baseEnd_4267928 < baseStart_4267928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267940 : List Nat := [2, 3, 1, 2, 1, 3, 3, 8]
def baseStart_4267940 : Nat := 118140960795 + 4267940 * 2 ^ 59
def prefixEnd_4267940 : Nat := 4983230072969 + 3 ^ 40 * 4267940 * 2
def baseEnd_4267940 : Nat := 81166837946301366623041

theorem tailTrace_4267940 : CollatzResearch.WordTrace tailWord_4267940 prefixEnd_4267940 81166837946301366623041 := by
  unfold tailWord_4267940
  simp only [CollatzResearch.WordTrace]
  refine ⟨77832280078994880482964637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103776373438659840643952849 77832280078994880482964637)
  ·
    refine ⟨29187105029623080181111739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77832280078994880482964637 29187105029623080181111739)
    ·
      refine ⟨43780657544434620271667609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29187105029623080181111739 43780657544434620271667609)
      ·
        refine ⟨32835493158325965203750707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43780657544434620271667609 32835493158325965203750707)
        ·
          refine ⟨49253239737488947805626061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32835493158325965203750707 49253239737488947805626061)
          ·
            refine ⟨18469964901558355427109773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49253239737488947805626061 18469964901558355427109773)
            ·
              refine ⟨6926236838084383285166165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18469964901558355427109773 6926236838084383285166165)
              ·
                refine ⟨81166837946301366623041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6926236838084383285166165 81166837946301366623041)
                ·
                  rfl

theorem cell23_4267940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 8].length) (baseStart_4267940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267940 prefixEnd_4267940 := by exact prefixLift 4267940
  have htrace : WordTrace (prefixWord ++ tailWord_4267940) baseStart_4267940 baseEnd_4267940 := by
    simpa [prefixWord, tailWord_4267940, baseEnd_4267940] using wordTrace_append hprefix tailTrace_4267940
  have hstable : (prefixWord ++ tailWord_4267940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267940).length < 2 ^ (prefixWord ++ tailWord_4267940).sum := by decide
  have hdescent : baseEnd_4267940 < baseStart_4267940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267957 : List Nat := [1, 3, 3, 2, 1, 3, 3, 7]
def baseStart_4267957 : Nat := 118140960795 + 4267957 * 2 ^ 59
def prefixEnd_4267957 : Nat := 4983230072969 + 3 ^ 40 * 4267957 * 2
def baseEnd_4267957 : Nat := 81167161248935678974427

theorem tailTrace_4267957 : CollatzResearch.WordTrace tailWord_4267957 prefixEnd_4267957 81167161248935678974427 := by
  unfold tailWord_4267957
  simp only [CollatzResearch.WordTrace]
  refine ⟨155665180198928172869298125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103776786799285448579532083 155665180198928172869298125)
  ·
    refine ⟨58374442574598064825986797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155665180198928172869298125 58374442574598064825986797)
    ·
      refine ⟨21890415965474274309745049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58374442574598064825986797 21890415965474274309745049)
      ·
        refine ⟨16417811974105705732308787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21890415965474274309745049 16417811974105705732308787)
        ·
          refine ⟨24626717961158558598463181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16417811974105705732308787 24626717961158558598463181)
          ·
            refine ⟨9235019235434459474423693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24626717961158558598463181 9235019235434459474423693)
            ·
              refine ⟨3463132213287922302908885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9235019235434459474423693 3463132213287922302908885)
              ·
                refine ⟨81167161248935678974427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3463132213287922302908885 81167161248935678974427)
                ·
                  rfl

theorem cell23_4267957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 7].length) (baseStart_4267957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267957 prefixEnd_4267957 := by exact prefixLift 4267957
  have htrace : WordTrace (prefixWord ++ tailWord_4267957) baseStart_4267957 baseEnd_4267957 := by
    simpa [prefixWord, tailWord_4267957, baseEnd_4267957] using wordTrace_append hprefix tailTrace_4267957
  have hstable : (prefixWord ++ tailWord_4267957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267957).length < 2 ^ (prefixWord ++ tailWord_4267957).sum := by decide
  have hdescent : baseEnd_4267957 < baseStart_4267957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267967 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_4267967 : Nat := 118140960795 + 4267967 * 2 ^ 59
def prefixEnd_4267967 : Nat := 4983230072969 + 3 ^ 40 * 4267967 * 2
def baseEnd_4267967 : Nat := 2191518488527808293184483

theorem tailTrace_4267967 : CollatzResearch.WordTrace tailWord_4267967 prefixEnd_4267967 2191518488527808293184483 := by
  unfold tailWord_4267967
  simp only [CollatzResearch.WordTrace]
  refine ⟨155665544928891944577162155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103777029952594629718108103 155665544928891944577162155)
  ·
    refine ⟨233498317393337916865743233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155665544928891944577162155 233498317393337916865743233)
    ·
      refine ⟨175123738045003437649307425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233498317393337916865743233 175123738045003437649307425)
      ·
        refine ⟨131342803533752578236980569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175123738045003437649307425 131342803533752578236980569)
        ·
          refine ⟨98507102650314433677735427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131342803533752578236980569 98507102650314433677735427)
          ·
            refine ⟨147760653975471650516603141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98507102650314433677735427 147760653975471650516603141)
            ·
              refine ⟨27705122620400934471863089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147760653975471650516603141 27705122620400934471863089)
              ·
                refine ⟨20778841965300700853897317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27705122620400934471863089 20778841965300700853897317)
                ·
                  refine ⟨3896032868493881410105747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20778841965300700853897317 3896032868493881410105747)
                  ·
                    refine ⟨5844049302740822115158621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896032868493881410105747 5844049302740822115158621)
                    ·
                      refine ⟨2191518488527808293184483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844049302740822115158621 2191518488527808293184483)
                      ·
                        rfl

theorem cell23_4267967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_4267967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267967 prefixEnd_4267967 := by exact prefixLift 4267967
  have htrace : WordTrace (prefixWord ++ tailWord_4267967) baseStart_4267967 baseEnd_4267967 := by
    simpa [prefixWord, tailWord_4267967, baseEnd_4267967] using wordTrace_append hprefix tailTrace_4267967
  have hstable : (prefixWord ++ tailWord_4267967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267967).length < 2 ^ (prefixWord ++ tailWord_4267967).sum := by decide
  have hdescent : baseEnd_4267967 < baseStart_4267967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4267984 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_4267984 : Nat := 118140960795 + 4267984 * 2 ^ 59
def prefixEnd_4267984 : Nat := 4983230072969 + 3 ^ 40 * 4267984 * 2
def baseEnd_4267984 : Nat := 2191527217698934726671905

theorem tailTrace_4267984 : CollatzResearch.WordTrace tailWord_4267984 prefixEnd_4267984 2191527217698934726671905 := by
  unfold tailWord_4267984
  simp only [CollatzResearch.WordTrace]
  refine ⟨77833082484915178240265503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103777443313220237653687337 77833082484915178240265503)
  ·
    refine ⟨116749623727372767360398255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77833082484915178240265503 116749623727372767360398255)
    ·
      refine ⟨175124435591059151040597383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116749623727372767360398255 175124435591059151040597383)
      ·
        refine ⟨262686653386588726560896075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175124435591059151040597383 262686653386588726560896075)
        ·
          refine ⟨394029980079883089841344113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262686653386588726560896075 394029980079883089841344113)
          ·
            refine ⟨295522485059912317381008085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394029980079883089841344113 295522485059912317381008085)
            ·
              refine ⟨6926308243591694938617377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 295522485059912317381008085 6926308243591694938617377)
              ·
                refine ⟨5194731182693771203963033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6926308243591694938617377 5194731182693771203963033)
                ·
                  refine ⟨3896048387020328402972275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194731182693771203963033 3896048387020328402972275)
                  ·
                    refine ⟨5844072580530492604458413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896048387020328402972275 5844072580530492604458413)
                    ·
                      refine ⟨2191527217698934726671905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844072580530492604458413 2191527217698934726671905)
                      ·
                        rfl

theorem cell23_4267984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_4267984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4267984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4267984 prefixEnd_4267984 := by exact prefixLift 4267984
  have htrace : WordTrace (prefixWord ++ tailWord_4267984) baseStart_4267984 baseEnd_4267984 := by
    simpa [prefixWord, tailWord_4267984, baseEnd_4267984] using wordTrace_append hprefix tailTrace_4267984
  have hstable : (prefixWord ++ tailWord_4267984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4267984).length < 2 ^ (prefixWord ++ tailWord_4267984).sum := by decide
  have hdescent : baseEnd_4267984 < baseStart_4267984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4267984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268024 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_4268024 : Nat := 118140960795 + 4268024 * 2 ^ 59
def prefixEnd_4268024 : Nat := 4983230072969 + 3 ^ 40 * 4268024 * 2
def baseEnd_4268024 : Nat := 2191547756925114570171721

theorem tailTrace_4268024 : CollatzResearch.WordTrace tailWord_4268024 prefixEnd_4268024 2191547756925114570171721 := by
  unfold tailWord_4268024
  simp only [CollatzResearch.WordTrace]
  refine ⟨77833811944842721655993563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103778415926456962207991417 77833811944842721655993563)
  ·
    refine ⟨116750717917264082483990345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77833811944842721655993563 116750717917264082483990345)
    ·
      refine ⟨87563038437948061862992759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116750717917264082483990345 87563038437948061862992759)
      ·
        refine ⟨131344557656922092794489139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87563038437948061862992759 131344557656922092794489139)
        ·
          refine ⟨197016836485383139191733709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131344557656922092794489139 197016836485383139191733709)
          ·
            refine ⟨73881313682018677196900141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197016836485383139191733709 73881313682018677196900141)
            ·
              refine ⟨27705492630757003948837553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73881313682018677196900141 27705492630757003948837553)
              ·
                refine ⟨20779119473067752961628165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27705492630757003948837553 20779119473067752961628165)
                ·
                  refine ⟨3896084901200203680305281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20779119473067752961628165 3896084901200203680305281)
                  ·
                    refine ⟨2922063675900152760228961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896084901200203680305281 2922063675900152760228961)
                    ·
                      refine ⟨2191547756925114570171721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922063675900152760228961 2191547756925114570171721)
                      ·
                        rfl

theorem cell23_4268024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_4268024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268024 prefixEnd_4268024 := by exact prefixLift 4268024
  have htrace : WordTrace (prefixWord ++ tailWord_4268024) baseStart_4268024 baseEnd_4268024 := by
    simpa [prefixWord, tailWord_4268024, baseEnd_4268024] using wordTrace_append hprefix tailTrace_4268024
  have hstable : (prefixWord ++ tailWord_4268024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268024).length < 2 ^ (prefixWord ++ tailWord_4268024).sum := by decide
  have hdescent : baseEnd_4268024 < baseStart_4268024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268040 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4268040 : Nat := 118140960795 + 4268040 * 2 ^ 59
def prefixEnd_4268040 : Nat := 4983230072969 + 3 ^ 40 * 4268040 * 2
def baseEnd_4268040 : Nat := 2191555972615586507571647

theorem tailTrace_4268040 : CollatzResearch.WordTrace tailWord_4268040 prefixEnd_4268040 2191555972615586507571647 := by
  unfold tailWord_4268040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77834103728813739022284787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103778804971751652029713049 77834103728813739022284787)
  ·
    refine ⟨116751155593220608533427181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77834103728813739022284787 116751155593220608533427181)
    ·
      refine ⟨43781683347457728200035193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116751155593220608533427181 43781683347457728200035193)
      ·
        refine ⟨32836262510593296150026395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43781683347457728200035193 32836262510593296150026395)
        ·
          refine ⟨49254393765889944225039593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32836262510593296150026395 49254393765889944225039593)
          ·
            refine ⟨36940795324417458168779695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49254393765889944225039593 36940795324417458168779695)
            ·
              refine ⟨55411192986626187253169543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36940795324417458168779695 55411192986626187253169543)
              ·
                refine ⟨83116789479939280879754315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55411192986626187253169543 83116789479939280879754315)
                ·
                  refine ⟨124675184219908921319631473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83116789479939280879754315 124675184219908921319631473)
                  ·
                    refine ⟨93506388164931690989723605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124675184219908921319631473 93506388164931690989723605)
                    ·
                      refine ⟨2191555972615586507571647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93506388164931690989723605 2191555972615586507571647)
                      ·
                        rfl

theorem cell23_4268040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4268040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268040 prefixEnd_4268040 := by exact prefixLift 4268040
  have htrace : WordTrace (prefixWord ++ tailWord_4268040) baseStart_4268040 baseEnd_4268040 := by
    simpa [prefixWord, tailWord_4268040, baseEnd_4268040] using wordTrace_append hprefix tailTrace_4268040
  have hstable : (prefixWord ++ tailWord_4268040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268040).length < 2 ^ (prefixWord ++ tailWord_4268040).sum := by decide
  have hdescent : baseEnd_4268040 < baseStart_4268040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268052 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4268052 : Nat := 118140960795 + 4268052 * 2 ^ 59
def prefixEnd_4268052 : Nat := 4983230072969 + 3 ^ 40 * 4268052 * 2
def baseEnd_4268052 : Nat := 2191562134383440460621593

theorem tailTrace_4268052 : CollatzResearch.WordTrace tailWord_4268052 prefixEnd_4268052 2191562134383440460621593 := by
  unfold tailWord_4268052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77834322566792002047003205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103779096755722669396004273 77834322566792002047003205)
  ·
    refine ⟨14593935481273500383813101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77834322566792002047003205 14593935481273500383813101)
    ·
      refine ⟨5472725805477562643929913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14593935481273500383813101 5472725805477562643929913)
      ·
        refine ⟨4104544354108171982947435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5472725805477562643929913 4104544354108171982947435)
        ·
          refine ⟨6156816531162257974421153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104544354108171982947435 6156816531162257974421153)
          ·
            refine ⟨4617612398371693480815865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6156816531162257974421153 4617612398371693480815865)
            ·
              refine ⟨3463209298778770110611899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4617612398371693480815865 3463209298778770110611899)
              ·
                refine ⟨5194813948168155165917849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463209298778770110611899 5194813948168155165917849)
                ·
                  refine ⟨3896110461126116374438387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194813948168155165917849 3896110461126116374438387)
                  ·
                    refine ⟨5844165691689174561657581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896110461126116374438387 5844165691689174561657581)
                    ·
                      refine ⟨2191562134383440460621593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844165691689174561657581 2191562134383440460621593)
                      ·
                        rfl

theorem cell23_4268052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4268052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268052 prefixEnd_4268052 := by exact prefixLift 4268052
  have htrace : WordTrace (prefixWord ++ tailWord_4268052) baseStart_4268052 baseEnd_4268052 := by
    simpa [prefixWord, tailWord_4268052, baseEnd_4268052] using wordTrace_append hprefix tailTrace_4268052
  have hstable : (prefixWord ++ tailWord_4268052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268052).length < 2 ^ (prefixWord ++ tailWord_4268052).sum := by decide
  have hdescent : baseEnd_4268052 < baseStart_4268052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268058 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_4268058 : Nat := 118140960795 + 4268058 * 2 ^ 59
def prefixEnd_4268058 : Nat := 4983230072969 + 3 ^ 40 * 4268058 * 2
def baseEnd_4268058 : Nat := 2191565215267367437146565

theorem tailTrace_4268058 : CollatzResearch.WordTrace tailWord_4268058 prefixEnd_4268058 2191565215267367437146565 := by
  unfold tailWord_4268058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38917215992890566779681207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103779242647708178079149885 38917215992890566779681207)
  ·
    refine ⟨58375823989335850169521811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38917215992890566779681207 58375823989335850169521811)
    ·
      refine ⟨87563735984003775254282717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58375823989335850169521811 87563735984003775254282717)
      ·
        refine ⟨32836400994001415720356019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87563735984003775254282717 32836400994001415720356019)
        ·
          refine ⟨49254601491002123580534029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32836400994001415720356019 49254601491002123580534029)
          ·
            refine ⟨18470475559125796342700261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49254601491002123580534029 18470475559125796342700261)
            ·
              refine ⟨3463214167336086814256299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18470475559125796342700261 3463214167336086814256299)
              ·
                refine ⟨5194821251004130221384449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463214167336086814256299 5194821251004130221384449)
                ·
                  refine ⟨3896115938253097666038337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194821251004130221384449 3896115938253097666038337)
                  ·
                    refine ⟨2922086953689823249528753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896115938253097666038337 2922086953689823249528753)
                    ·
                      refine ⟨2191565215267367437146565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922086953689823249528753 2191565215267367437146565)
                      ·
                        rfl

theorem cell23_4268058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_4268058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268058 prefixEnd_4268058 := by exact prefixLift 4268058
  have htrace : WordTrace (prefixWord ++ tailWord_4268058) baseStart_4268058 baseEnd_4268058 := by
    simpa [prefixWord, tailWord_4268058, baseEnd_4268058] using wordTrace_append hprefix tailTrace_4268058
  have hstable : (prefixWord ++ tailWord_4268058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268058).length < 2 ^ (prefixWord ++ tailWord_4268058).sum := by decide
  have hdescent : baseEnd_4268058 < baseStart_4268058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268124 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4268124 : Nat := 118140960795 + 4268124 * 2 ^ 59
def prefixEnd_4268124 : Nat := 4983230072969 + 3 ^ 40 * 4268124 * 2
def baseEnd_4268124 : Nat := 730533034996854726307087

theorem tailTrace_4268124 : CollatzResearch.WordTrace tailWord_4268124 prefixEnd_4268124 730533034996854726307087 := by
  unfold tailWord_4268124
  simp only [CollatzResearch.WordTrace]
  refine ⟨77835635594661580195313713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103780847459548773593751617 77835635594661580195313713)
  ·
    refine ⟨58376726695996185146485285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77835635594661580195313713 58376726695996185146485285)
    ·
      refine ⟨10945636255499284714965991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58376726695996185146485285 10945636255499284714965991)
      ·
        refine ⟨16418454383248927072448987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10945636255499284714965991 16418454383248927072448987)
        ·
          refine ⟨24627681574873390608673481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16418454383248927072448987 24627681574873390608673481)
          ·
            refine ⟨18470761181155042956505111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24627681574873390608673481 18470761181155042956505111)
            ·
              refine ⟨27706141771732564434757667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18470761181155042956505111 27706141771732564434757667)
              ·
                refine ⟨41559212657598846652136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27706141771732564434757667 41559212657598846652136501)
                ·
                  refine ⟨3896176186649891873637797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41559212657598846652136501 3896176186649891873637797)
                  ·
                    refine ⟨730533034996854726307087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3896176186649891873637797 730533034996854726307087)
                    ·
                      rfl

theorem cell23_4268124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4268124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268124 prefixEnd_4268124 := by exact prefixLift 4268124
  have htrace : WordTrace (prefixWord ++ tailWord_4268124) baseStart_4268124 baseEnd_4268124 := by
    simpa [prefixWord, tailWord_4268124, baseEnd_4268124] using wordTrace_append hprefix tailTrace_4268124
  have hstable : (prefixWord ++ tailWord_4268124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268124).length < 2 ^ (prefixWord ++ tailWord_4268124).sum := by decide
  have hdescent : baseEnd_4268124 < baseStart_4268124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268157 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_4268157 : Nat := 118140960795 + 4268157 * 2 ^ 59
def prefixEnd_4268157 : Nat := 4983230072969 + 3 ^ 40 * 4268157 * 2
def baseEnd_4268157 : Nat := 2191616049852162549808609

theorem tailTrace_4268157 : CollatzResearch.WordTrace tailWord_4268157 prefixEnd_4268157 2191616049852162549808609 := by
  unfold tailWord_4268157
  simp only [CollatzResearch.WordTrace]
  refine ⟨155672474798203607026578725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103781649865469071351052483 155672474798203607026578725)
  ·
    refine ⟨29188589024663176317483511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155672474798203607026578725 29188589024663176317483511)
    ·
      refine ⟨43782883536994764476225267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29188589024663176317483511 43782883536994764476225267)
      ·
        refine ⟨65674325305492146714337901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43782883536994764476225267 65674325305492146714337901)
        ·
          refine ⟨24627871989559555017876713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65674325305492146714337901 24627871989559555017876713)
          ·
            refine ⟨18470903992169666263407535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24627871989559555017876713 18470903992169666263407535)
            ·
              refine ⟨27706355988254499395111303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18470903992169666263407535 27706355988254499395111303)
              ·
                refine ⟨41559533982381749092666955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27706355988254499395111303 41559533982381749092666955)
                ·
                  refine ⟨62339300973572623639000433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41559533982381749092666955 62339300973572623639000433)
                  ·
                    refine ⟨46754475730179467729250325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62339300973572623639000433 46754475730179467729250325)
                    ·
                      refine ⟨2191616049852162549808609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46754475730179467729250325 2191616049852162549808609)
                      ·
                        rfl

theorem cell23_4268157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_4268157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268157 prefixEnd_4268157 := by exact prefixLift 4268157
  have htrace : WordTrace (prefixWord ++ tailWord_4268157) baseStart_4268157 baseEnd_4268157 := by
    simpa [prefixWord, tailWord_4268157, baseEnd_4268157] using wordTrace_append hprefix tailTrace_4268157
  have hstable : (prefixWord ++ tailWord_4268157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268157).length < 2 ^ (prefixWord ++ tailWord_4268157).sum := by decide
  have hdescent : baseEnd_4268157 < baseStart_4268157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268167 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 5, 5]
def baseStart_4268167 : Nat := 118140960795 + 4268167 * 2 ^ 59
def prefixEnd_4268167 : Nat := 4983230072969 + 3 ^ 40 * 4268167 * 2
def baseEnd_4268167 : Nat := 730540394886235836894521

theorem tailTrace_4268167 : CollatzResearch.WordTrace tailWord_4268167 prefixEnd_4268167 730540394886235836894521 := by
  unfold tailWord_4268167
  simp only [CollatzResearch.WordTrace]
  refine ⟨155672839528167378734442755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103781893018778252489628503 155672839528167378734442755)
  ·
    refine ⟨233509259292251068101664133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155672839528167378734442755 233509259292251068101664133)
    ·
      refine ⟨43782986117297075269062025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233509259292251068101664133 43782986117297075269062025)
      ·
        refine ⟨32837239587972806451796519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43782986117297075269062025 32837239587972806451796519)
        ·
          refine ⟨49255859381959209677694779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32837239587972806451796519 49255859381959209677694779)
          ·
            refine ⟨73883789072938814516542169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49255859381959209677694779 73883789072938814516542169)
            ·
              refine ⟨55412841804704110887406627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73883789072938814516542169 55412841804704110887406627)
              ·
                refine ⟨83119262707056166331109941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55412841804704110887406627 83119262707056166331109941)
                ·
                  refine ⟨7792430878786515593541557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83119262707056166331109941 7792430878786515593541557)
                  ·
                    refine ⟨730540394886235836894521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7792430878786515593541557 730540394886235836894521)
                    ·
                      rfl

theorem cell23_4268167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_4268167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268167 prefixEnd_4268167 := by exact prefixLift 4268167
  have htrace : WordTrace (prefixWord ++ tailWord_4268167) baseStart_4268167 baseEnd_4268167 := by
    simpa [prefixWord, tailWord_4268167, baseEnd_4268167] using wordTrace_append hprefix tailTrace_4268167
  have hstable : (prefixWord ++ tailWord_4268167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268167).length < 2 ^ (prefixWord ++ tailWord_4268167).sum := by decide
  have hdescent : baseEnd_4268167 < baseStart_4268167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268191 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4268191 : Nat := 118140960795 + 4268191 * 2 ^ 59
def prefixEnd_4268191 : Nat := 4983230072969 + 3 ^ 40 * 4268191 * 2
def baseEnd_4268191 : Nat := 2191633508194415416783453

theorem tailTrace_4268191 : CollatzResearch.WordTrace tailWord_4268191 prefixEnd_4268191 2191633508194415416783453 := by
  unfold tailWord_4268191
  simp only [CollatzResearch.WordTrace]
  refine ⟨155673714880080430833316427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103782476586720287222210951 155673714880080430833316427)
  ·
    refine ⟨233510572320120646249974641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155673714880080430833316427 233510572320120646249974641)
    ·
      refine ⟨175132929240090484687480981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233510572320120646249974641 175132929240090484687480981)
      ·
        refine ⟨8209356058129241469725671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175132929240090484687480981 8209356058129241469725671)
        ·
          refine ⟨12314034087193862204588507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8209356058129241469725671 12314034087193862204588507)
          ·
            refine ⟨18471051130790793306882761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12314034087193862204588507 18471051130790793306882761)
            ·
              refine ⟨13853288348093094980162071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18471051130790793306882761 13853288348093094980162071)
              ·
                refine ⟨20779932522139642470243107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13853288348093094980162071 20779932522139642470243107)
                ·
                  refine ⟨31169898783209463705364661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20779932522139642470243107 31169898783209463705364661)
                  ·
                    refine ⟨2922178010925887222377937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31169898783209463705364661 2922178010925887222377937)
                    ·
                      refine ⟨2191633508194415416783453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922178010925887222377937 2191633508194415416783453)
                      ·
                        rfl

theorem cell23_4268191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4268191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268191 prefixEnd_4268191 := by exact prefixLift 4268191
  have htrace : WordTrace (prefixWord ++ tailWord_4268191) baseStart_4268191 baseEnd_4268191 := by
    simpa [prefixWord, tailWord_4268191, baseEnd_4268191] using wordTrace_append hprefix tailTrace_4268191
  have hstable : (prefixWord ++ tailWord_4268191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268191).length < 2 ^ (prefixWord ++ tailWord_4268191).sum := by decide
  have hdescent : baseEnd_4268191 < baseStart_4268191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268197 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_4268197 : Nat := 118140960795 + 4268197 * 2 ^ 59
def prefixEnd_4268197 : Nat := 4983230072969 + 3 ^ 40 * 4268197 * 2
def baseEnd_4268197 : Nat := 730545529692780797769475

theorem tailTrace_4268197 : CollatzResearch.WordTrace tailWord_4268197 prefixEnd_4268197 730545529692780797769475 := by
  unfold tailWord_4268197
  simp only [CollatzResearch.WordTrace]
  refine ⟨155673933718058693858034845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103782622478705795905356563 155673933718058693858034845)
  ·
    refine ⟨58377725144272010196763067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155673933718058693858034845 58377725144272010196763067)
    ·
      refine ⟨87566587716408015295144601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58377725144272010196763067 87566587716408015295144601)
      ·
        refine ⟨65674940787306011471358451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87566587716408015295144601 65674940787306011471358451)
        ·
          refine ⟨98512411180959017207037677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65674940787306011471358451 98512411180959017207037677)
          ·
            refine ⟨36942154192859631452639129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98512411180959017207037677 36942154192859631452639129)
            ·
              refine ⟨27706615644644723589479347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36942154192859631452639129 27706615644644723589479347)
              ·
                refine ⟨41559923466967085384219021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27706615644644723589479347 41559923466967085384219021)
                ·
                  refine ⟨15584971300112657019082133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41559923466967085384219021 15584971300112657019082133)
                  ·
                    refine ⟨730545529692780797769475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15584971300112657019082133 730545529692780797769475)
                    ·
                      rfl

theorem cell23_4268197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_4268197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268197 prefixEnd_4268197 := by exact prefixLift 4268197
  have htrace : WordTrace (prefixWord ++ tailWord_4268197) baseStart_4268197 baseEnd_4268197 := by
    simpa [prefixWord, tailWord_4268197, baseEnd_4268197] using wordTrace_append hprefix tailTrace_4268197
  have hstable : (prefixWord ++ tailWord_4268197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268197).length < 2 ^ (prefixWord ++ tailWord_4268197).sum := by decide
  have hdescent : baseEnd_4268197 < baseStart_4268197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268215 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_4268215 : Nat := 118140960795 + 4268215 * 2 ^ 59
def prefixEnd_4268215 : Nat := 4983230072969 + 3 ^ 40 * 4268215 * 2
def baseEnd_4268215 : Nat := 2191645831730123322883343

theorem tailTrace_4268215 : CollatzResearch.WordTrace tailWord_4268215 prefixEnd_4268215 2191645831730123322883343 := by
  unfold tailWord_4268215
  simp only [CollatzResearch.WordTrace]
  refine ⟨155674590231993482932190099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103783060154662321954793399 155674590231993482932190099)
  ·
    refine ⟨233511885347990224398285149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155674590231993482932190099 233511885347990224398285149)
    ·
      refine ⟨87566957005496334149356931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233511885347990224398285149 87566957005496334149356931)
      ·
        refine ⟨131350435508244501224035397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87566957005496334149356931 131350435508244501224035397)
        ·
          refine ⟨24628206657795843979506637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131350435508244501224035397 24628206657795843979506637)
          ·
            refine ⟨9235577496673441492314989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24628206657795843979506637 9235577496673441492314989)
            ·
              refine ⟨3463341561252540559618121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9235577496673441492314989 3463341561252540559618121)
              ·
                refine ⟨2597506170939405419713591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463341561252540559618121 2597506170939405419713591)
                ·
                  refine ⟨3896259256409108129570387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597506170939405419713591 3896259256409108129570387)
                  ·
                    refine ⟨5844388884613662194355581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896259256409108129570387 5844388884613662194355581)
                    ·
                      refine ⟨2191645831730123322883343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844388884613662194355581 2191645831730123322883343)
                      ·
                        rfl

theorem cell23_4268215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_4268215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268215 prefixEnd_4268215 := by exact prefixLift 4268215
  have htrace : WordTrace (prefixWord ++ tailWord_4268215) baseStart_4268215 baseEnd_4268215 := by
    simpa [prefixWord, tailWord_4268215, baseEnd_4268215] using wordTrace_append hprefix tailTrace_4268215
  have hstable : (prefixWord ++ tailWord_4268215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268215).length < 2 ^ (prefixWord ++ tailWord_4268215).sum := by decide
  have hdescent : baseEnd_4268215 < baseStart_4268215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268217 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4268217 : Nat := 118140960795 + 4268217 * 2 ^ 59
def prefixEnd_4268217 : Nat := 4983230072969 + 3 ^ 40 * 4268217 * 2
def baseEnd_4268217 : Nat := 2191646858691432315058333

theorem tailTrace_4268217 : CollatzResearch.WordTrace tailWord_4268217 prefixEnd_4268217 2191646858691432315058333 := by
  unfold tailWord_4268217
  simp only [CollatzResearch.WordTrace]
  refine ⟨155674663177986237273762905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103783108785324158182508603 155674663177986237273762905)
  ·
    refine ⟨116755997383489677955322179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155674663177986237273762905 116755997383489677955322179)
    ·
      refine ⟨175133996075234516932983269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116755997383489677955322179 175133996075234516932983269)
      ·
        refine ⟨32837624264106471924934363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175133996075234516932983269 32837624264106471924934363)
        ·
          refine ⟨49256436396159707887401545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32837624264106471924934363 49256436396159707887401545)
          ·
            refine ⟨36942327297119780915551159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49256436396159707887401545 36942327297119780915551159)
            ·
              refine ⟨55413490945679671373326739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36942327297119780915551159 55413490945679671373326739)
              ·
                refine ⟨83120236418519507059990109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55413490945679671373326739 83120236418519507059990109)
                ·
                  refine ⟨31170088656944815147496291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83120236418519507059990109 31170088656944815147496291)
                  ·
                    refine ⟨46755132985417222721244437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31170088656944815147496291 46755132985417222721244437)
                    ·
                      refine ⟨2191646858691432315058333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46755132985417222721244437 2191646858691432315058333)
                      ·
                        rfl

theorem cell23_4268217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4268217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268217 prefixEnd_4268217 := by exact prefixLift 4268217
  have htrace : WordTrace (prefixWord ++ tailWord_4268217) baseStart_4268217 baseEnd_4268217 := by
    simpa [prefixWord, tailWord_4268217, baseEnd_4268217] using wordTrace_append hprefix tailTrace_4268217
  have hstable : (prefixWord ++ tailWord_4268217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268217).length < 2 ^ (prefixWord ++ tailWord_4268217).sum := by decide
  have hdescent : baseEnd_4268217 < baseStart_4268217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268224 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_4268224 : Nat := 118140960795 + 4268224 * 2 ^ 59
def prefixEnd_4268224 : Nat := 4983230072969 + 3 ^ 40 * 4268224 * 2
def baseEnd_4268224 : Nat := 2191650453056013787670801

theorem tailTrace_4268224 : CollatzResearch.WordTrace tailWord_4268224 prefixEnd_4268224 2191650453056013787670801 := by
  unfold tailWord_4268224
  simp only [CollatzResearch.WordTrace]
  refine ⟨77837459244480438734633863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103783278992640584979511817 77837459244480438734633863)
  ·
    refine ⟨116756188866720658101950795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77837459244480438734633863 116756188866720658101950795)
    ·
      refine ⟨175134283300080987152926193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116756188866720658101950795 175134283300080987152926193)
      ·
        refine ⟨131350712475060740364694645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175134283300080987152926193 131350712475060740364694645)
        ·
          refine ⟨12314129294536944409190123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131350712475060740364694645 12314129294536944409190123)
          ·
            refine ⟨18471193941805416613785185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12314129294536944409190123 18471193941805416613785185)
            ·
              refine ⟨13853395456354062460338889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18471193941805416613785185 13853395456354062460338889)
              ·
                refine ⟨10390046592265546845254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13853395456354062460338889 10390046592265546845254167)
                ·
                  refine ⟨15585069888398320267881251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10390046592265546845254167 15585069888398320267881251)
                  ·
                    refine ⟨23377604832597480401821877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15585069888398320267881251 23377604832597480401821877)
                    ·
                      refine ⟨2191650453056013787670801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23377604832597480401821877 2191650453056013787670801)
                      ·
                        rfl

theorem cell23_4268224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_4268224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268224 prefixEnd_4268224 := by exact prefixLift 4268224
  have htrace : WordTrace (prefixWord ++ tailWord_4268224) baseStart_4268224 baseEnd_4268224 := by
    simpa [prefixWord, tailWord_4268224, baseEnd_4268224] using wordTrace_append hprefix tailTrace_4268224
  have hstable : (prefixWord ++ tailWord_4268224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268224).length < 2 ^ (prefixWord ++ tailWord_4268224).sum := by decide
  have hdescent : baseEnd_4268224 < baseStart_4268224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268234 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_4268234 : Nat := 118140960795 + 4268234 * 2 ^ 59
def prefixEnd_4268234 : Nat := 4983230072969 + 3 ^ 40 * 4268234 * 2
def baseEnd_4268234 : Nat := 2191655587862558748545755

theorem tailTrace_4268234 : CollatzResearch.WordTrace tailWord_4268234 prefixEnd_4268234 2191655587862558748545755 := by
  unfold tailWord_4268234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38918820804731162294282939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103783522145949766118087837 38918820804731162294282939)
  ·
    refine ⟨58378231207096743441424409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38918820804731162294282939 58378231207096743441424409)
    ·
      refine ⟨43783673405322557581068307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58378231207096743441424409 43783673405322557581068307)
      ·
        refine ⟨65675510107983836371602461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43783673405322557581068307 65675510107983836371602461)
        ·
          refine ⟨24628316290493938639350923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65675510107983836371602461 24628316290493938639350923)
          ·
            refine ⟨36942474435740907959026385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24628316290493938639350923 36942474435740907959026385)
            ·
              refine ⟨27706855826805680969269789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36942474435740907959026385 27706855826805680969269789)
              ·
                refine ⟨10390070935052130363476171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27706855826805680969269789 10390070935052130363476171)
                ·
                  refine ⟨15585106402578195545214257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10390070935052130363476171 15585106402578195545214257)
                  ·
                    refine ⟨11688829801933646658910693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15585106402578195545214257 11688829801933646658910693)
                    ·
                      refine ⟨2191655587862558748545755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11688829801933646658910693 2191655587862558748545755)
                      ·
                        rfl

theorem cell23_4268234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_4268234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268234 prefixEnd_4268234 := by exact prefixLift 4268234
  have htrace : WordTrace (prefixWord ++ tailWord_4268234) baseStart_4268234 baseEnd_4268234 := by
    simpa [prefixWord, tailWord_4268234, baseEnd_4268234] using wordTrace_append hprefix tailTrace_4268234
  have hstable : (prefixWord ++ tailWord_4268234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268234).length < 2 ^ (prefixWord ++ tailWord_4268234).sum := by decide
  have hdescent : baseEnd_4268234 < baseStart_4268234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268238 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_4268238 : Nat := 118140960795 + 4268238 * 2 ^ 59
def prefixEnd_4268238 : Nat := 4983230072969 + 3 ^ 40 * 4268238 * 2
def baseEnd_4268238 : Nat := 2191657641785176732895737

theorem tailTrace_4268238 : CollatzResearch.WordTrace tailWord_4268238 prefixEnd_4268238 2191657641785176732895737 := by
  unfold tailWord_4268238
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459428638863769732534671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103783619407273438573518245 19459428638863769732534671)
  ·
    refine ⟨29189142958295654598802007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19459428638863769732534671 29189142958295654598802007)
    ·
      refine ⟨43783714437443481898203011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29189142958295654598802007 43783714437443481898203011)
      ·
        refine ⟨65675571656165222847304517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43783714437443481898203011 65675571656165222847304517)
        ·
          refine ⟨12314169685530979283869597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65675571656165222847304517 12314169685530979283869597)
          ·
            refine ⟨4617813632074117231451099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12314169685530979283869597 4617813632074117231451099)
            ·
              refine ⟨6926720448111175847176649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617813632074117231451099 6926720448111175847176649)
              ·
                refine ⟨5195040336083381885382487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6926720448111175847176649 5195040336083381885382487)
                ·
                  refine ⟨7792560504125072828073731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195040336083381885382487 7792560504125072828073731)
                  ·
                    refine ⟨11688840756187609242110597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7792560504125072828073731 11688840756187609242110597)
                    ·
                      refine ⟨2191657641785176732895737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11688840756187609242110597 2191657641785176732895737)
                      ·
                        rfl

theorem cell23_4268238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_4268238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268238 prefixEnd_4268238 := by exact prefixLift 4268238
  have htrace : WordTrace (prefixWord ++ tailWord_4268238) baseStart_4268238 baseEnd_4268238 := by
    simpa [prefixWord, tailWord_4268238, baseEnd_4268238] using wordTrace_append hprefix tailTrace_4268238
  have hstable : (prefixWord ++ tailWord_4268238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268238).length < 2 ^ (prefixWord ++ tailWord_4268238).sum := by decide
  have hdescent : baseEnd_4268238 < baseStart_4268238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268241 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_4268241 : Nat := 118140960795 + 4268241 * 2 ^ 59
def prefixEnd_4268241 : Nat := 4983230072969 + 3 ^ 40 * 4268241 * 2
def baseEnd_4268241 : Nat := 2191659182227140221158223

theorem tailTrace_4268241 : CollatzResearch.WordTrace tailWord_4268241 prefixEnd_4268241 2191659182227140221158223 := by
  unfold tailWord_4268241
  simp only [CollatzResearch.WordTrace]
  refine ⟨155675538529899289372636577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103783692353266192915091051 155675538529899289372636577)
  ·
    refine ⟨116756653897424467029477433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155675538529899289372636577 116756653897424467029477433)
    ·
      refine ⟨87567490423068350272108075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116756653897424467029477433 87567490423068350272108075)
      ·
        refine ⟨131351235634602525408162113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87567490423068350272108075 131351235634602525408162113)
        ·
          refine ⟨98513426725951894056121585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131351235634602525408162113 98513426725951894056121585)
          ·
            refine ⟨73885070044463920542091189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98513426725951894056121585 73885070044463920542091189)
            ·
              refine ⟨6926725316668492550821049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73885070044463920542091189 6926725316668492550821049)
              ·
                refine ⟨5195043987501369413115787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6926725316668492550821049 5195043987501369413115787)
                ·
                  refine ⟨7792565981252054119673681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195043987501369413115787 7792565981252054119673681)
                  ·
                    refine ⟨5844424485939040589755261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7792565981252054119673681 5844424485939040589755261)
                    ·
                      refine ⟨2191659182227140221158223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844424485939040589755261 2191659182227140221158223)
                      ·
                        rfl

theorem cell23_4268241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_4268241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268241 prefixEnd_4268241 := by exact prefixLift 4268241
  have htrace : WordTrace (prefixWord ++ tailWord_4268241) baseStart_4268241 baseEnd_4268241 := by
    simpa [prefixWord, tailWord_4268241, baseEnd_4268241] using wordTrace_append hprefix tailTrace_4268241
  have hstable : (prefixWord ++ tailWord_4268241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268241).length < 2 ^ (prefixWord ++ tailWord_4268241).sum := by decide
  have hdescent : baseEnd_4268241 < baseStart_4268241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268274 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_4268274 : Nat := 118140960795 + 4268274 * 2 ^ 59
def prefixEnd_4268274 : Nat := 4983230072969 + 3 ^ 40 * 4268274 * 2
def baseEnd_4268274 : Nat := 730558709029579530681857

theorem tailTrace_4268274 : CollatzResearch.WordTrace tailWord_4268274 prefixEnd_4268274 730558709029579530681857 := by
  unfold tailWord_4268274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38919185534694934002146969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103784494759186490672391917 38919185534694934002146969)
  ·
    refine ⟨29189389151021200501610227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38919185534694934002146969 29189389151021200501610227)
    ·
      refine ⟨43784083726531800752415341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29189389151021200501610227 43784083726531800752415341)
      ·
        refine ⟨16419031397449425282155753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43784083726531800752415341 16419031397449425282155753)
        ·
          refine ⟨12314273548087068961616815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16419031397449425282155753 12314273548087068961616815)
          ·
            refine ⟨18471410322130603442425223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12314273548087068961616815 18471410322130603442425223)
            ·
              refine ⟨27707115483195905163637835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18471410322130603442425223 27707115483195905163637835)
              ·
                refine ⟨41560673224793857745456753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27707115483195905163637835 41560673224793857745456753)
                ·
                  refine ⟨31170504918595393309092565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41560673224793857745456753 31170504918595393309092565)
                  ·
                    refine ⟨730558709029579530681857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31170504918595393309092565 730558709029579530681857)
                    ·
                      rfl

theorem cell23_4268274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_4268274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268274 prefixEnd_4268274 := by exact prefixLift 4268274
  have htrace : WordTrace (prefixWord ++ tailWord_4268274) baseStart_4268274 baseEnd_4268274 := by
    simpa [prefixWord, tailWord_4268274, baseEnd_4268274] using wordTrace_append hprefix tailTrace_4268274
  have hstable : (prefixWord ++ tailWord_4268274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268274).length < 2 ^ (prefixWord ++ tailWord_4268274).sum := by decide
  have hdescent : baseEnd_4268274 < baseStart_4268274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268345 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4268345 : Nat := 118140960795 + 4268345 * 2 ^ 59
def prefixEnd_4268345 : Nat := 4983230072969 + 3 ^ 40 * 4268345 * 2
def baseEnd_4268345 : Nat := 2191712584215207814257745

theorem tailTrace_4268345 : CollatzResearch.WordTrace tailWord_4268345 prefixEnd_4268345 2191712584215207814257745 := by
  unfold tailWord_4268345
  simp only [CollatzResearch.WordTrace]
  refine ⟨155679331721522515134422489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103786221147681676756281659 155679331721522515134422489)
  ·
    refine ⟨116759498791141886350816867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155679331721522515134422489 116759498791141886350816867)
    ·
      refine ⟨175139248186712829526225301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116759498791141886350816867 175139248186712829526225301)
      ·
        refine ⟨8209652258752163884041811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175139248186712829526225301 8209652258752163884041811)
        ·
          refine ⟨12314478388128245826062717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8209652258752163884041811 12314478388128245826062717)
          ·
            refine ⟨4617929395548092184773519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12314478388128245826062717 4617929395548092184773519)
            ·
              refine ⟨6926894093322138277160279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617929395548092184773519 6926894093322138277160279)
              ·
                refine ⟨10390341139983207415740419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6926894093322138277160279 10390341139983207415740419)
                ·
                  refine ⟨15585511709974811123610629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10390341139983207415740419 15585511709974811123610629)
                  ·
                    refine ⟨2922283445620277085676993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15585511709974811123610629 2922283445620277085676993)
                    ·
                      refine ⟨2191712584215207814257745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922283445620277085676993 2191712584215207814257745)
                      ·
                        rfl

theorem cell23_4268345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4268345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268345 prefixEnd_4268345 := by exact prefixLift 4268345
  have htrace : WordTrace (prefixWord ++ tailWord_4268345) baseStart_4268345 baseEnd_4268345 := by
    simpa [prefixWord, tailWord_4268345, baseEnd_4268345] using wordTrace_append hprefix tailTrace_4268345
  have hstable : (prefixWord ++ tailWord_4268345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268345).length < 2 ^ (prefixWord ++ tailWord_4268345).sum := by decide
  have hdescent : baseEnd_4268345 < baseStart_4268345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268364 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_4268364 : Nat := 118140960795 + 4268364 * 2 ^ 59
def prefixEnd_4268364 : Nat := 4983230072969 + 3 ^ 40 * 4268364 * 2
def baseEnd_4268364 : Nat := 730574113449214413306719

theorem tailTrace_4268364 : CollatzResearch.WordTrace tailWord_4268364 prefixEnd_4268364 730574113449214413306719 := by
  unfold tailWord_4268364
  simp only [CollatzResearch.WordTrace]
  refine ⟨77840012354226840689682073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103786683138969120919576097 77840012354226840689682073)
  ·
    refine ⟨58380009265670130517261555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77840012354226840689682073 58380009265670130517261555)
    ·
      refine ⟨87570013898505195775892333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58380009265670130517261555 87570013898505195775892333)
      ·
        refine ⟨32838755211939448415959625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87570013898505195775892333 32838755211939448415959625)
        ·
          refine ⟨24629066408954586311969719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32838755211939448415959625 24629066408954586311969719)
          ·
            refine ⟨36943599613431879467954579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24629066408954586311969719 36943599613431879467954579)
            ·
              refine ⟨55415399420147819201931869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36943599613431879467954579 55415399420147819201931869)
              ·
                refine ⟨20780774782555432200724451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55415399420147819201931869 20780774782555432200724451)
                ·
                  refine ⟨31171162173833148301086677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20780774782555432200724451 31171162173833148301086677)
                  ·
                    refine ⟨730574113449214413306719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31171162173833148301086677 730574113449214413306719)
                    ·
                      rfl

theorem cell23_4268364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_4268364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268364 prefixEnd_4268364 := by exact prefixLift 4268364
  have htrace : WordTrace (prefixWord ++ tailWord_4268364) baseStart_4268364 baseEnd_4268364 := by
    simpa [prefixWord, tailWord_4268364, baseEnd_4268364] using wordTrace_append hprefix tailTrace_4268364
  have hstable : (prefixWord ++ tailWord_4268364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268364).length < 2 ^ (prefixWord ++ tailWord_4268364).sum := by decide
  have hdescent : baseEnd_4268364 < baseStart_4268364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268368 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 5]
def baseStart_4268368 : Nat := 118140960795 + 4268368 * 2 ^ 59
def prefixEnd_4268368 : Nat := 4983230072969 + 3 ^ 40 * 4268368 * 2
def baseEnd_4268368 : Nat := 243524932696695691585571

theorem tailTrace_4268368 : CollatzResearch.WordTrace tailWord_4268368 prefixEnd_4268368 243524932696695691585571 := by
  unfold tailWord_4268368
  simp only [CollatzResearch.WordTrace]
  refine ⟨77840085300219595031254879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103786780400292793375006505 77840085300219595031254879)
  ·
    refine ⟨116760127950329392546882319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77840085300219595031254879 116760127950329392546882319)
    ·
      refine ⟨175140191925494088820323479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116760127950329392546882319 175140191925494088820323479)
      ·
        refine ⟨262710287888241133230485219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175140191925494088820323479 262710287888241133230485219)
        ·
          refine ⟨394065431832361699845727829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262710287888241133230485219 394065431832361699845727829)
          ·
            refine ⟨4617954279285488670067123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 394065431832361699845727829 4617954279285488670067123)
            ·
              refine ⟨6926931418928233005100685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617954279285488670067123 6926931418928233005100685)
              ·
                refine ⟨2597599282098087376912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6926931418928233005100685 2597599282098087376912757)
                ·
                  refine ⟨243524932696695691585571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597599282098087376912757 243524932696695691585571)
                  ·
                    rfl

theorem cell23_4268368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 5].length) (baseStart_4268368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268368 prefixEnd_4268368 := by exact prefixLift 4268368
  have htrace : WordTrace (prefixWord ++ tailWord_4268368) baseStart_4268368 baseEnd_4268368 := by
    simpa [prefixWord, tailWord_4268368, baseEnd_4268368] using wordTrace_append hprefix tailTrace_4268368
  have hstable : (prefixWord ++ tailWord_4268368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268368).length < 2 ^ (prefixWord ++ tailWord_4268368).sum := by decide
  have hdescent : baseEnd_4268368 < baseStart_4268368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268391 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_4268391 : Nat := 118140960795 + 4268391 * 2 ^ 59
def prefixEnd_4268391 : Nat := 4983230072969 + 3 ^ 40 * 4268391 * 2
def baseEnd_4268391 : Nat := 2191736204325314634282533

theorem tailTrace_4268391 : CollatzResearch.WordTrace tailWord_4268391 prefixEnd_4268391 2191736204325314634282533 := by
  unfold tailWord_4268391
  simp only [CollatzResearch.WordTrace]
  refine ⟨155681009479355864990597027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103787339652903909993731351 155681009479355864990597027)
  ·
    refine ⟨233521514219033797485895541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155681009479355864990597027 233521514219033797485895541)
    ·
      refine ⟨21892641958034418514302707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233521514219033797485895541 21892641958034418514302707)
      ·
        refine ⟨32838962937051627771454061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21892641958034418514302707 32838962937051627771454061)
        ·
          refine ⟨12314611101394360414295273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32838962937051627771454061 12314611101394360414295273)
          ·
            refine ⟨9235958326045770310721455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12314611101394360414295273 9235958326045770310721455)
            ·
              refine ⟨13853937489068655466082183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235958326045770310721455 13853937489068655466082183)
              ·
                refine ⟨20780906233602983199123275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13853937489068655466082183 20780906233602983199123275)
                ·
                  refine ⟨31171359350404474798684913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20780906233602983199123275 31171359350404474798684913)
                  ·
                    refine ⟨23378519512803356099013685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31171359350404474798684913 23378519512803356099013685)
                    ·
                      refine ⟨2191736204325314634282533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23378519512803356099013685 2191736204325314634282533)
                      ·
                        rfl

theorem cell23_4268391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_4268391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268391 prefixEnd_4268391 := by exact prefixLift 4268391
  have htrace : WordTrace (prefixWord ++ tailWord_4268391) baseStart_4268391 baseEnd_4268391 := by
    simpa [prefixWord, tailWord_4268391, baseEnd_4268391] using wordTrace_append hprefix tailTrace_4268391
  have hstable : (prefixWord ++ tailWord_4268391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268391).length < 2 ^ (prefixWord ++ tailWord_4268391).sum := by decide
  have hdescent : baseEnd_4268391 < baseStart_4268391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268401 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_4268401 : Nat := 118140960795 + 4268401 * 2 ^ 59
def prefixEnd_4268401 : Nat := 4983230072969 + 3 ^ 40 * 4268401 * 2
def baseEnd_4268401 : Nat := 2191741339131859595157487

theorem tailTrace_4268401 : CollatzResearch.WordTrace tailWord_4268401 prefixEnd_4268401 2191741339131859595157487 := by
  unfold tailWord_4268401
  simp only [CollatzResearch.WordTrace]
  refine ⟨155681374209319636698461057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103787582806213091132307371 155681374209319636698461057)
  ·
    refine ⟨116761030656989727523845793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155681374209319636698461057 116761030656989727523845793)
    ·
      refine ⟨87570772992742295642884345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116761030656989727523845793 87570772992742295642884345)
      ·
        refine ⟨65678079744556721732163259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87570772992742295642884345 65678079744556721732163259)
        ·
          refine ⟨98517119616835082598244889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65678079744556721732163259 98517119616835082598244889)
          ·
            refine ⟨73887839712626311948683667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98517119616835082598244889 73887839712626311948683667)
            ·
              refine ⟨110831759568939467923025501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73887839712626311948683667 110831759568939467923025501)
              ·
                refine ⟨41561909838352300471134563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110831759568939467923025501 41561909838352300471134563)
                ·
                  refine ⟨62342864757528450706701845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41561909838352300471134563 62342864757528450706701845)
                  ·
                    refine ⟨2922321785509146126876649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62342864757528450706701845 2922321785509146126876649)
                    ·
                      refine ⟨2191741339131859595157487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922321785509146126876649 2191741339131859595157487)
                      ·
                        rfl

theorem cell23_4268401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_4268401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268401 prefixEnd_4268401 := by exact prefixLift 4268401
  have htrace : WordTrace (prefixWord ++ tailWord_4268401) baseStart_4268401 baseEnd_4268401 := by
    simpa [prefixWord, tailWord_4268401, baseEnd_4268401] using wordTrace_append hprefix tailTrace_4268401
  have hstable : (prefixWord ++ tailWord_4268401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268401).length < 2 ^ (prefixWord ++ tailWord_4268401).sum := by decide
  have hdescent : baseEnd_4268401 < baseStart_4268401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268441 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 6]
def baseStart_4268441 : Nat := 118140960795 + 4268441 * 2 ^ 59
def prefixEnd_4268441 : Nat := 4983230072969 + 3 ^ 40 * 4268441 * 2
def baseEnd_4268441 : Nat := 243529097595337715406367

theorem tailTrace_4268441 : CollatzResearch.WordTrace tailWord_4268441 prefixEnd_4268441 243529097595337715406367 := by
  unfold tailWord_4268441
  simp only [CollatzResearch.WordTrace]
  refine ⟨155682833129174723529917177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103788555419449815686611451 155682833129174723529917177)
  ·
    refine ⟨116762124846881042647437883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155682833129174723529917177 116762124846881042647437883)
    ·
      refine ⟨175143187270321563971156825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116762124846881042647437883 175143187270321563971156825)
      ·
        refine ⟨131357390452741172978367619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175143187270321563971156825 131357390452741172978367619)
        ·
          refine ⟨197036085679111759467551429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131357390452741172978367619 197036085679111759467551429)
          ·
            refine ⟨36944266064833454900165893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197036085679111759467551429 36944266064833454900165893)
            ·
              refine ⟨6927049887156272793781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36944266064833454900165893 6927049887156272793781105)
              ·
                refine ⟨5195287415367204595335829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6927049887156272793781105 5195287415367204595335829)
                ·
                  refine ⟨243529097595337715406367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5195287415367204595335829 243529097595337715406367)
                  ·
                    rfl

theorem cell23_4268441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_4268441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268441 prefixEnd_4268441 := by exact prefixLift 4268441
  have htrace : WordTrace (prefixWord ++ tailWord_4268441) baseStart_4268441 baseEnd_4268441 := by
    simpa [prefixWord, tailWord_4268441, baseEnd_4268441] using wordTrace_append hprefix tailTrace_4268441
  have hstable : (prefixWord ++ tailWord_4268441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268441).length < 2 ^ (prefixWord ++ tailWord_4268441).sum := by decide
  have hdescent : baseEnd_4268441 < baseStart_4268441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268464 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_4268464 : Nat := 118140960795 + 4268464 * 2 ^ 59
def prefixEnd_4268464 : Nat := 4983230072969 + 3 ^ 40 * 4268464 * 2
def baseEnd_4268464 : Nat := 2191773688413092848669697

theorem tailTrace_4268464 : CollatzResearch.WordTrace tailWord_4268464 prefixEnd_4268464 2191773688413092848669697 := by
  unfold tailWord_4268464
  simp only [CollatzResearch.WordTrace]
  refine ⟨77841836004045699229002223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103789114672060932305336297 77841836004045699229002223)
  ·
    refine ⟨116762754006068548843503335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77841836004045699229002223 116762754006068548843503335)
    ·
      refine ⟨175144131009102823265255003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116762754006068548843503335 175144131009102823265255003)
      ·
        refine ⟨262716196513654234897882505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175144131009102823265255003 262716196513654234897882505)
        ·
          refine ⟨197037147385240676173411879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262716196513654234897882505 197037147385240676173411879)
          ·
            refine ⟨295555721077861014260117819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197037147385240676173411879 295555721077861014260117819)
            ·
              refine ⟨443333581616791521390176729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295555721077861014260117819 443333581616791521390176729)
              ·
                refine ⟨332500186212593641042632547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443333581616791521390176729 332500186212593641042632547)
                ·
                  refine ⟨498750279318890461563948821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332500186212593641042632547 498750279318890461563948821)
                  ·
                    refine ⟨23378919343072990385810101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 498750279318890461563948821 23378919343072990385810101)
                    ·
                      refine ⟨2191773688413092848669697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23378919343072990385810101 2191773688413092848669697)
                      ·
                        rfl

theorem cell23_4268464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_4268464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268464 prefixEnd_4268464 := by exact prefixLift 4268464
  have htrace : WordTrace (prefixWord ++ tailWord_4268464) baseStart_4268464 baseEnd_4268464 := by
    simpa [prefixWord, tailWord_4268464, baseEnd_4268464] using wordTrace_append hprefix tailTrace_4268464
  have hstable : (prefixWord ++ tailWord_4268464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268464).length < 2 ^ (prefixWord ++ tailWord_4268464).sum := by decide
  have hdescent : baseEnd_4268464 < baseStart_4268464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268471 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 3, 5]
def baseStart_4268471 : Nat := 118140960795 + 4268471 * 2 ^ 59
def prefixEnd_4268471 : Nat := 4983230072969 + 3 ^ 40 * 4268471 * 2
def baseEnd_4268471 : Nat := 730592427592558107094055

theorem tailTrace_4268471 : CollatzResearch.WordTrace tailWord_4268471 prefixEnd_4268471 730592427592558107094055 := by
  unfold tailWord_4268471
  simp only [CollatzResearch.WordTrace]
  refine ⟨155683927319066038653509267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103789284879377359102339511 155683927319066038653509267)
  ·
    refine ⟨233525890978599057980263901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155683927319066038653509267 233525890978599057980263901)
    ·
      refine ⟨87572209116974646742598963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233525890978599057980263901 87572209116974646742598963)
      ·
        refine ⟨131358313675461970113898445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87572209116974646742598963 131358313675461970113898445)
        ·
          refine ⟨49259367628298238792711917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131358313675461970113898445 49259367628298238792711917)
          ·
            refine ⟨18472262860611839547266969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49259367628298238792711917 18472262860611839547266969)
            ·
              refine ⟨13854197145458879660450227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18472262860611839547266969 13854197145458879660450227)
              ·
                refine ⟨20781295718188319490675341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13854197145458879660450227 20781295718188319490675341)
                ·
                  refine ⟨7792985894320619809003253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20781295718188319490675341 7792985894320619809003253)
                  ·
                    refine ⟨730592427592558107094055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7792985894320619809003253 730592427592558107094055)
                    ·
                      rfl

theorem cell23_4268471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_4268471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268471 prefixEnd_4268471 := by exact prefixLift 4268471
  have htrace : WordTrace (prefixWord ++ tailWord_4268471) baseStart_4268471 baseEnd_4268471 := by
    simpa [prefixWord, tailWord_4268471, baseEnd_4268471] using wordTrace_append hprefix tailTrace_4268471
  have hstable : (prefixWord ++ tailWord_4268471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268471).length < 2 ^ (prefixWord ++ tailWord_4268471).sum := by decide
  have hdescent : baseEnd_4268471 < baseStart_4268471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268488 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_4268488 : Nat := 118140960795 + 4268488 * 2 ^ 59
def prefixEnd_4268488 : Nat := 4983230072969 + 3 ^ 40 * 4268488 * 2
def baseEnd_4268488 : Nat := 730595337316266918256529

theorem tailTrace_4268488 : CollatzResearch.WordTrace tailWord_4268488 prefixEnd_4268488 730595337316266918256529 := by
  unfold tailWord_4268488
  simp only [CollatzResearch.WordTrace]
  refine ⟨77842273680002225278439059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103789698240002967037918745 77842273680002225278439059)
  ·
    refine ⟨116763410520003337917658589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77842273680002225278439059 116763410520003337917658589)
    ·
      refine ⟨43786278945001251719121971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116763410520003337917658589 43786278945001251719121971)
      ·
        refine ⟨65679418417501877578682957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43786278945001251719121971 65679418417501877578682957)
        ·
          refine ⟨24629781906563204092006109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65679418417501877578682957 24629781906563204092006109)
          ·
            refine ⟨9236168214961201534502291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24629781906563204092006109 9236168214961201534502291)
            ·
              refine ⟨13854252322441802301753437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9236168214961201534502291 13854252322441802301753437)
              ·
                refine ⟨5195344620915675863157539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13854252322441802301753437 5195344620915675863157539)
                ·
                  refine ⟨7793016931373513794736309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195344620915675863157539 7793016931373513794736309)
                  ·
                    refine ⟨730595337316266918256529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7793016931373513794736309 730595337316266918256529)
                    ·
                      rfl

theorem cell23_4268488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_4268488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268488 prefixEnd_4268488 := by exact prefixLift 4268488
  have htrace : WordTrace (prefixWord ++ tailWord_4268488) baseStart_4268488 baseEnd_4268488 := by
    simpa [prefixWord, tailWord_4268488, baseEnd_4268488] using wordTrace_append hprefix tailTrace_4268488
  have hstable : (prefixWord ++ tailWord_4268488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268488).length < 2 ^ (prefixWord ++ tailWord_4268488).sum := by decide
  have hdescent : baseEnd_4268488 < baseStart_4268488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268502 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4268502 : Nat := 118140960795 + 4268502 * 2 ^ 59
def prefixEnd_4268502 : Nat := 4983230072969 + 3 ^ 40 * 4268502 * 2
def baseEnd_4268502 : Nat := 2191793200677963699994523

theorem tailTrace_4268502 : CollatzResearch.WordTrace tailWord_4268502 prefixEnd_4268502 2191793200677963699994523 := by
  unfold tailWord_4268502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730316123872108184242985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103790038654635820631925173 9730316123872108184242985)
  ·
    refine ⟨7297737092904081138182239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9730316123872108184242985 7297737092904081138182239)
    ·
      refine ⟨10946605639356121707273359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297737092904081138182239 10946605639356121707273359)
      ·
        refine ⟨16419908459034182560910039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10946605639356121707273359 16419908459034182560910039)
        ·
          refine ⟨24629862688551273841365059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16419908459034182560910039 24629862688551273841365059)
          ·
            refine ⟨36944794032826910762047589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24629862688551273841365059 36944794032826910762047589)
            ·
              refine ⟨6927148881155045767883923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36944794032826910762047589 6927148881155045767883923)
              ·
                refine ⟨10390723321732568651825885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927148881155045767883923 10390723321732568651825885)
                ·
                  refine ⟨3896521245649713244434707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10390723321732568651825885 3896521245649713244434707)
                  ·
                    refine ⟨5844781868474569866652061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896521245649713244434707 5844781868474569866652061)
                    ·
                      refine ⟨2191793200677963699994523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844781868474569866652061 2191793200677963699994523)
                      ·
                        rfl

theorem cell23_4268502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4268502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268502 prefixEnd_4268502 := by exact prefixLift 4268502
  have htrace : WordTrace (prefixWord ++ tailWord_4268502) baseStart_4268502 baseEnd_4268502 := by
    simpa [prefixWord, tailWord_4268502, baseEnd_4268502] using wordTrace_append hprefix tailTrace_4268502
  have hstable : (prefixWord ++ tailWord_4268502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268502).length < 2 ^ (prefixWord ++ tailWord_4268502).sum := by decide
  have hdescent : baseEnd_4268502 < baseStart_4268502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268511 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_4268511 : Nat := 118140960795 + 4268511 * 2 ^ 59
def prefixEnd_4268511 : Nat := 4983230072969 + 3 ^ 40 * 4268511 * 2
def baseEnd_4268511 : Nat := 2191797822003854164781981

theorem tailTrace_4268511 : CollatzResearch.WordTrace tailWord_4268511 prefixEnd_4268511 2191797822003854164781981 := by
  unfold tailWord_4268511
  simp only [CollatzResearch.WordTrace]
  refine ⟨155685386238921125484965387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103790257492614083656643591 155685386238921125484965387)
  ·
    refine ⟨233528079358381688227448081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155685386238921125484965387 233528079358381688227448081)
    ·
      refine ⟨175146059518786266170586061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233528079358381688227448081 175146059518786266170586061)
      ·
        refine ⟨65679772319544849813969773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175146059518786266170586061 65679772319544849813969773)
        ·
          refine ⟨24629914619829318680238665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65679772319544849813969773 24629914619829318680238665)
          ·
            refine ⟨18472435964871989010178999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24629914619829318680238665 18472435964871989010178999)
            ·
              refine ⟨27708653947307983515268499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18472435964871989010178999 27708653947307983515268499)
              ·
                refine ⟨41562980920961975272902749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27708653947307983515268499 41562980920961975272902749)
                ·
                  refine ⟨15586117845360740727338531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41562980920961975272902749 15586117845360740727338531)
                  ·
                    refine ⟨23379176768041111091007797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15586117845360740727338531 23379176768041111091007797)
                    ·
                      refine ⟨2191797822003854164781981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23379176768041111091007797 2191797822003854164781981)
                      ·
                        rfl

theorem cell23_4268511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_4268511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268511 prefixEnd_4268511 := by exact prefixLift 4268511
  have htrace : WordTrace (prefixWord ++ tailWord_4268511) baseStart_4268511 baseEnd_4268511 := by
    simpa [prefixWord, tailWord_4268511, baseEnd_4268511] using wordTrace_append hprefix tailTrace_4268511
  have hstable : (prefixWord ++ tailWord_4268511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268511).length < 2 ^ (prefixWord ++ tailWord_4268511).sum := by decide
  have hdescent : baseEnd_4268511 < baseStart_4268511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268521 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_4268521 : Nat := 118140960795 + 4268521 * 2 ^ 59
def prefixEnd_4268521 : Nat := 4983230072969 + 3 ^ 40 * 4268521 * 2
def baseEnd_4268521 : Nat := 2191802956810399125656935

theorem tailTrace_4268521 : CollatzResearch.WordTrace tailWord_4268521 prefixEnd_4268521 2191802956810399125656935 := by
  unfold tailWord_4268521
  simp only [CollatzResearch.WordTrace]
  refine ⟨155685750968884897192829417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103790500645923264795219611 155685750968884897192829417)
  ·
    refine ⟨116764313226663672894622063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155685750968884897192829417 116764313226663672894622063)
    ·
      refine ⟨175146469839995509341933095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116764313226663672894622063 175146469839995509341933095)
      ·
        refine ⟨262719704759993264012899643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175146469839995509341933095 262719704759993264012899643)
        ·
          refine ⟨394079557139989896019349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262719704759993264012899643 394079557139989896019349465)
          ·
            refine ⟨295559667854992422014512099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394079557139989896019349465 295559667854992422014512099)
            ·
              refine ⟨443339501782488633021768149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295559667854992422014512099 443339501782488633021768149)
              ·
                refine ⟨10390769573027077336447691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 443339501782488633021768149 10390769573027077336447691)
                ·
                  refine ⟨15586154359540616004671537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10390769573027077336447691 15586154359540616004671537)
                  ·
                    refine ⟨11689615769655462003503653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15586154359540616004671537 11689615769655462003503653)
                    ·
                      refine ⟨2191802956810399125656935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11689615769655462003503653 2191802956810399125656935)
                      ·
                        rfl

theorem cell23_4268521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_4268521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268521 prefixEnd_4268521 := by exact prefixLift 4268521
  have htrace : WordTrace (prefixWord ++ tailWord_4268521) baseStart_4268521 baseEnd_4268521 := by
    simpa [prefixWord, tailWord_4268521, baseEnd_4268521] using wordTrace_append hprefix tailTrace_4268521
  have hstable : (prefixWord ++ tailWord_4268521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268521).length < 2 ^ (prefixWord ++ tailWord_4268521).sum := by decide
  have hdescent : baseEnd_4268521 < baseStart_4268521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268525 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4268525 : Nat := 118140960795 + 4268525 * 2 ^ 59
def prefixEnd_4268525 : Nat := 4983230072969 + 3 ^ 40 * 4268525 * 2
def baseEnd_4268525 : Nat := 2191805010733017110006917

theorem tailTrace_4268525 : CollatzResearch.WordTrace tailWord_4268525 prefixEnd_4268525 2191805010733017110006917 := by
  unfold tailWord_4268525
  simp only [CollatzResearch.WordTrace]
  refine ⟨155685896860870405875975029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103790597907246937250650019 155685896860870405875975029)
  ·
    refine ⟨14595552830706600550872659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155685896860870405875975029 14595552830706600550872659)
    ·
      refine ⟨21893329246059900826308989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14595552830706600550872659 21893329246059900826308989)
      ·
        refine ⟨8209998467272462809865871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21893329246059900826308989 8209998467272462809865871)
        ·
          refine ⟨12314997700908694214798807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8209998467272462809865871 12314997700908694214798807)
          ·
            refine ⟨18472496551363041322198211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12314997700908694214798807 18472496551363041322198211)
            ·
              refine ⟨27708744827044561983297317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18472496551363041322198211 27708744827044561983297317)
              ·
                refine ⟨5195389655070855371868247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27708744827044561983297317 5195389655070855371868247)
                ·
                  refine ⟨7793084482606283057802371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195389655070855371868247 7793084482606283057802371)
                  ·
                    refine ⟨11689626723909424586703557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7793084482606283057802371 11689626723909424586703557)
                    ·
                      refine ⟨2191805010733017110006917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11689626723909424586703557 2191805010733017110006917)
                      ·
                        rfl

theorem cell23_4268525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4268525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268525 prefixEnd_4268525 := by exact prefixLift 4268525
  have htrace : WordTrace (prefixWord ++ tailWord_4268525) baseStart_4268525 baseEnd_4268525 := by
    simpa [prefixWord, tailWord_4268525, baseEnd_4268525] using wordTrace_append hprefix tailTrace_4268525
  have hstable : (prefixWord ++ tailWord_4268525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268525).length < 2 ^ (prefixWord ++ tailWord_4268525).sum := by decide
  have hdescent : baseEnd_4268525 < baseStart_4268525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268545 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_4268545 : Nat := 118140960795 + 4268545 * 2 ^ 59
def prefixEnd_4268545 : Nat := 4983230072969 + 3 ^ 40 * 4268545 * 2
def baseEnd_4268545 : Nat := 2191815280346107031756825

theorem tailTrace_4268545 : CollatzResearch.WordTrace tailWord_4268545 prefixEnd_4268545 2191815280346107031756825 := by
  unfold tailWord_4268545
  simp only [CollatzResearch.WordTrace]
  refine ⟨155686626320797949291703089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103791084213865299527802059 155686626320797949291703089)
  ·
    refine ⟨116764969740598461968777317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155686626320797949291703089 116764969740598461968777317)
    ·
      refine ⟨21893431826362211619145747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116764969740598461968777317 21893431826362211619145747)
      ·
        refine ⟨32840147739543317428718621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21893431826362211619145747 32840147739543317428718621)
        ·
          refine ⟨12315055402328744035769483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32840147739543317428718621 12315055402328744035769483)
          ·
            refine ⟨18472583103493116053654225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12315055402328744035769483 18472583103493116053654225)
            ·
              refine ⟨13854437327619837040240669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18472583103493116053654225 13854437327619837040240669)
              ·
                refine ⟨5195413997857438890090251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13854437327619837040240669 5195413997857438890090251)
                ·
                  refine ⟨7793120996786158335135377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195413997857438890090251 7793120996786158335135377)
                  ·
                    refine ⟨5844840747589618751351533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7793120996786158335135377 5844840747589618751351533)
                    ·
                      refine ⟨2191815280346107031756825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844840747589618751351533 2191815280346107031756825)
                      ·
                        rfl

theorem cell23_4268545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_4268545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268545 prefixEnd_4268545 := by exact prefixLift 4268545
  have htrace : WordTrace (prefixWord ++ tailWord_4268545) baseStart_4268545 baseEnd_4268545 := by
    simpa [prefixWord, tailWord_4268545, baseEnd_4268545] using wordTrace_append hprefix tailTrace_4268545
  have hstable : (prefixWord ++ tailWord_4268545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268545).length < 2 ^ (prefixWord ++ tailWord_4268545).sum := by decide
  have hdescent : baseEnd_4268545 < baseStart_4268545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268548 : List Nat := [2, 3, 2, 3, 1, 3, 9]
def baseStart_4268548 : Nat := 118140960795 + 4268548 * 2 ^ 59
def prefixEnd_4268548 : Nat := 4983230072969 + 3 ^ 40 * 4268548 * 2
def baseEnd_4268548 : Nat := 27059466923309512592831

theorem tailTrace_4268548 : CollatzResearch.WordTrace tailWord_4268548 prefixEnd_4268548 27059466923309512592831 := by
  unfold tailWord_4268548
  simp only [CollatzResearch.WordTrace]
  refine ⟨77843367869893540402031149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103791157159858053869374865 77843367869893540402031149)
  ·
    refine ⟨29191262951210077650761681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77843367869893540402031149 29191262951210077650761681)
    ·
      refine ⟨21893447213407558238071261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29191262951210077650761681 21893447213407558238071261)
      ·
        refine ⟨8210042705027834339276723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21893447213407558238071261 8210042705027834339276723)
        ·
          refine ⟨12315064057541751508915085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210042705027834339276723 12315064057541751508915085)
          ·
            refine ⟨4618149021578156815843157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12315064057541751508915085 4618149021578156815843157)
            ·
              refine ⟨27059466923309512592831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4618149021578156815843157 27059466923309512592831)
              ·
                rfl

theorem cell23_4268548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 9].length) (baseStart_4268548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268548 prefixEnd_4268548 := by exact prefixLift 4268548
  have htrace : WordTrace (prefixWord ++ tailWord_4268548) baseStart_4268548 baseEnd_4268548 := by
    simpa [prefixWord, tailWord_4268548, baseEnd_4268548] using wordTrace_append hprefix tailTrace_4268548
  have hstable : (prefixWord ++ tailWord_4268548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268548).length < 2 ^ (prefixWord ++ tailWord_4268548).sum := by decide
  have hdescent : baseEnd_4268548 < baseStart_4268548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268589 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4268589 : Nat := 118140960795 + 4268589 * 2 ^ 59
def prefixEnd_4268589 : Nat := 4983230072969 + 3 ^ 40 * 4268589 * 2
def baseEnd_4268589 : Nat := 2191837873494904859606623

theorem tailTrace_4268589 : CollatzResearch.WordTrace tailWord_4268589 prefixEnd_4268589 2191837873494904859606623 := by
  unfold tailWord_4268589
  simp only [CollatzResearch.WordTrace]
  refine ⟨155688231132638544806304821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103792154088425696537536547 155688231132638544806304821)
  ·
    refine ⟨14595771668684863575591077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155688231132638544806304821 14595771668684863575591077)
    ·
      refine ⟨2736707187878411920423327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14595771668684863575591077 2736707187878411920423327)
      ·
        refine ⟨4105060781817617880634991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736707187878411920423327 4105060781817617880634991)
        ·
          refine ⟨6157591172726426820952487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105060781817617880634991 6157591172726426820952487)
          ·
            refine ⟨9236386759089640231428731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157591172726426820952487 9236386759089640231428731)
            ·
              refine ⟨13854580138634460347143097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9236386759089640231428731 13854580138634460347143097)
              ·
                refine ⟨10390935103975845260357323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13854580138634460347143097 10390935103975845260357323)
                ·
                  refine ⟨15586402655963767890535985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10390935103975845260357323 15586402655963767890535985)
                  ·
                    refine ⟨11689801991972825917901989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15586402655963767890535985 11689801991972825917901989)
                    ·
                      refine ⟨2191837873494904859606623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11689801991972825917901989 2191837873494904859606623)
                      ·
                        rfl

theorem cell23_4268589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4268589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268589 prefixEnd_4268589 := by exact prefixLift 4268589
  have htrace : WordTrace (prefixWord ++ tailWord_4268589) baseStart_4268589 baseEnd_4268589 := by
    simpa [prefixWord, tailWord_4268589, baseEnd_4268589] using wordTrace_append hprefix tailTrace_4268589
  have hstable : (prefixWord ++ tailWord_4268589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268589).length < 2 ^ (prefixWord ++ tailWord_4268589).sum := by decide
  have hdescent : baseEnd_4268589 < baseStart_4268589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268596 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4268596 : Nat := 118140960795 + 4268596 * 2 ^ 59
def prefixEnd_4268596 : Nat := 4983230072969 + 3 ^ 40 * 4268596 * 2
def baseEnd_4268596 : Nat := 2191841467859486332219091

theorem tailTrace_4268596 : CollatzResearch.WordTrace tailWord_4268596 prefixEnd_4268596 2191841467859486332219091 := by
  unfold tailWord_4268596
  simp only [CollatzResearch.WordTrace]
  refine ⟨77844243221806592500904821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103792324295742123334539761 77844243221806592500904821)
  ·
    refine ⟨7297897802044368046959827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77844243221806592500904821 7297897802044368046959827)
    ·
      refine ⟨10946846703066552070439741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297897802044368046959827 10946846703066552070439741)
      ·
        refine ⟨4105067513649957026414903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10946846703066552070439741 4105067513649957026414903)
        ·
          refine ⟨6157601270474935539622355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105067513649957026414903 6157601270474935539622355)
          ·
            refine ⟨9236401905712403309433533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157601270474935539622355 9236401905712403309433533)
            ·
              refine ⟨3463650714642151241037575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9236401905712403309433533 3463650714642151241037575)
              ·
                refine ⟨5195476071963226861556363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463650714642151241037575 5195476071963226861556363)
                ·
                  refine ⟨7793214107944840292334545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195476071963226861556363 7793214107944840292334545)
                  ·
                    refine ⟨5844910580958630219250909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7793214107944840292334545 5844910580958630219250909)
                    ·
                      refine ⟨2191841467859486332219091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844910580958630219250909 2191841467859486332219091)
                      ·
                        rfl

theorem cell23_4268596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4268596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268596 prefixEnd_4268596 := by exact prefixLift 4268596
  have htrace : WordTrace (prefixWord ++ tailWord_4268596) baseStart_4268596 baseEnd_4268596 := by
    simpa [prefixWord, tailWord_4268596, baseEnd_4268596] using wordTrace_append hprefix tailTrace_4268596
  have hstable : (prefixWord ++ tailWord_4268596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268596).length < 2 ^ (prefixWord ++ tailWord_4268596).sum := by decide
  have hdescent : baseEnd_4268596 < baseStart_4268596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268611 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_4268611 : Nat := 118140960795 + 4268611 * 2 ^ 59
def prefixEnd_4268611 : Nat := 4983230072969 + 3 ^ 40 * 4268611 * 2
def baseEnd_4268611 : Nat := 2191849170069303773531521

theorem tailTrace_4268611 : CollatzResearch.WordTrace tailWord_4268611 prefixEnd_4268611 2191849170069303773531521 := by
  unfold tailWord_4268611
  simp only [CollatzResearch.WordTrace]
  refine ⟨155689033538558842563605687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103792689025705895042403791 155689033538558842563605687)
  ·
    refine ⟨233533550307838263845408531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155689033538558842563605687 233533550307838263845408531)
    ·
      refine ⟨350300325461757395768112797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233533550307838263845408531 350300325461757395768112797)
      ·
        refine ⟨131362622048159023413042299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350300325461757395768112797 131362622048159023413042299)
        ·
          refine ⟨197043933072238535119563449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131362622048159023413042299 197043933072238535119563449)
          ·
            refine ⟨147782949804178901339672587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197043933072238535119563449 147782949804178901339672587)
            ·
              refine ⟨221674424706268352009508881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147782949804178901339672587 221674424706268352009508881)
              ·
                refine ⟨166255818529701264007131661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221674424706268352009508881 166255818529701264007131661)
                ·
                  refine ⟨62345931948637974002674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166255818529701264007131661 62345931948637974002674373)
                  ·
                    refine ⟨11689862240369620125501445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62345931948637974002674373 11689862240369620125501445)
                    ·
                      refine ⟨2191849170069303773531521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11689862240369620125501445 2191849170069303773531521)
                      ·
                        rfl

theorem cell23_4268611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_4268611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268611 prefixEnd_4268611 := by exact prefixLift 4268611
  have htrace : WordTrace (prefixWord ++ tailWord_4268611) baseStart_4268611 baseEnd_4268611 := by
    simpa [prefixWord, tailWord_4268611, baseEnd_4268611] using wordTrace_append hprefix tailTrace_4268611
  have hstable : (prefixWord ++ tailWord_4268611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268611).length < 2 ^ (prefixWord ++ tailWord_4268611).sum := by decide
  have hdescent : baseEnd_4268611 < baseStart_4268611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268618 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_4268618 : Nat := 118140960795 + 4268618 * 2 ^ 59
def prefixEnd_4268618 : Nat := 4983230072969 + 3 ^ 40 * 4268618 * 2
def baseEnd_4268618 : Nat := 2191852764433885246143989

theorem tailTrace_4268618 : CollatzResearch.WordTrace tailWord_4268618 prefixEnd_4268618 2191852764433885246143989 := by
  unfold tailWord_4268618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38922322212383370689777627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103792859233022321839407005 38922322212383370689777627)
  ·
    refine ⟨58383483318575056034666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38922322212383370689777627 58383483318575056034666441)
    ·
      refine ⟨43787612488931292025999831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58383483318575056034666441 43787612488931292025999831)
      ·
        refine ⟨65681418733396938038999747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43787612488931292025999831 65681418733396938038999747)
        ·
          refine ⟨98522128100095407058499621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65681418733396938038999747 98522128100095407058499621)
          ·
            refine ⟨18472899018767888823468679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98522128100095407058499621 18472899018767888823468679)
            ·
              refine ⟨27709348528151833235203019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18472899018767888823468679 27709348528151833235203019)
              ·
                refine ⟨41564022792227749852804529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27709348528151833235203019 41564022792227749852804529)
                ·
                  refine ⟨31173017094170812389603397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41564022792227749852804529 31173017094170812389603397)
                  ·
                    refine ⟨5844940705157027323050637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31173017094170812389603397 5844940705157027323050637)
                    ·
                      refine ⟨2191852764433885246143989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5844940705157027323050637 2191852764433885246143989)
                      ·
                        rfl

theorem cell23_4268618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_4268618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268618 prefixEnd_4268618 := by exact prefixLift 4268618
  have htrace : WordTrace (prefixWord ++ tailWord_4268618) baseStart_4268618 baseEnd_4268618 := by
    simpa [prefixWord, tailWord_4268618, baseEnd_4268618] using wordTrace_append hprefix tailTrace_4268618
  have hstable : (prefixWord ++ tailWord_4268618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268618).length < 2 ^ (prefixWord ++ tailWord_4268618).sum := by decide
  have hdescent : baseEnd_4268618 < baseStart_4268618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268628 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4268628 : Nat := 118140960795 + 4268628 * 2 ^ 59
def prefixEnd_4268628 : Nat := 4983230072969 + 3 ^ 40 * 4268628 * 2
def baseEnd_4268628 : Nat := 2191857899240430207018943

theorem tailTrace_4268628 : CollatzResearch.WordTrace tailWord_4268628 prefixEnd_4268628 2191857899240430207018943 := by
  unfold tailWord_4268628
  simp only [CollatzResearch.WordTrace]
  refine ⟨77844826789748627233487269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103793102386331502977983025 77844826789748627233487269)
  ·
    refine ⟨14595905023077867606278863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77844826789748627233487269 14595905023077867606278863)
    ·
      refine ⟨21893857534616801409418295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14595905023077867606278863 21893857534616801409418295)
      ·
        refine ⟨32840786301925202114127443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21893857534616801409418295 32840786301925202114127443)
        ·
          refine ⟨49261179452887803171191165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32840786301925202114127443 49261179452887803171191165)
          ·
            refine ⟨18472942294832926189196687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49261179452887803171191165 18472942294832926189196687)
            ·
              refine ⟨27709413442249389283795031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18472942294832926189196687 27709413442249389283795031)
              ·
                refine ⟨41564120163374083925692547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27709413442249389283795031 41564120163374083925692547)
                ·
                  refine ⟨62346180245061125888538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41564120163374083925692547 62346180245061125888538821)
                  ·
                    refine ⟨11689908795948961104101029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62346180245061125888538821 11689908795948961104101029)
                    ·
                      refine ⟨2191857899240430207018943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11689908795948961104101029 2191857899240430207018943)
                      ·
                        rfl

theorem cell23_4268628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4268628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268628 prefixEnd_4268628 := by exact prefixLift 4268628
  have htrace : WordTrace (prefixWord ++ tailWord_4268628) baseStart_4268628 baseEnd_4268628 := by
    simpa [prefixWord, tailWord_4268628, baseEnd_4268628] using wordTrace_append hprefix tailTrace_4268628
  have hstable : (prefixWord ++ tailWord_4268628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268628).length < 2 ^ (prefixWord ++ tailWord_4268628).sum := by decide
  have hdescent : baseEnd_4268628 < baseStart_4268628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268632 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_4268632 : Nat := 118140960795 + 4268632 * 2 ^ 59
def prefixEnd_4268632 : Nat := 4983230072969 + 3 ^ 40 * 4268632 * 2
def baseEnd_4268632 : Nat := 2191859953163048191368925

theorem tailTrace_4268632 : CollatzResearch.WordTrace tailWord_4268632 prefixEnd_4268632 2191859953163048191368925 := by
  unfold tailWord_4268632
  simp only [CollatzResearch.WordTrace]
  refine ⟨77844899735741381575060075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103793199647655175433413433 77844899735741381575060075)
  ·
    refine ⟨116767349603612072362590113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77844899735741381575060075 116767349603612072362590113)
    ·
      refine ⟨87575512202709054271942585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116767349603612072362590113 87575512202709054271942585)
      ·
        refine ⟨65681634152031790703956939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87575512202709054271942585 65681634152031790703956939)
        ·
          refine ⟨98522451228047686055935409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65681634152031790703956939 98522451228047686055935409)
          ·
            refine ⟨73891838421035764541951557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98522451228047686055935409 73891838421035764541951557)
            ·
              refine ⟨13854719703944205851615917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73891838421035764541951557 13854719703944205851615917)
              ·
                refine ⟨5195519888979077194355969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13854719703944205851615917 5195519888979077194355969)
                ·
                  refine ⟨3896639916734307895766977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5195519888979077194355969 3896639916734307895766977)
                  ·
                    refine ⟨2922479937550730921825233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896639916734307895766977 2922479937550730921825233)
                    ·
                      refine ⟨2191859953163048191368925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922479937550730921825233 2191859953163048191368925)
                      ·
                        rfl

theorem cell23_4268632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_4268632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268632 prefixEnd_4268632 := by exact prefixLift 4268632
  have htrace : WordTrace (prefixWord ++ tailWord_4268632) baseStart_4268632 baseEnd_4268632 := by
    simpa [prefixWord, tailWord_4268632, baseEnd_4268632] using wordTrace_append hprefix tailTrace_4268632
  have hstable : (prefixWord ++ tailWord_4268632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268632).length < 2 ^ (prefixWord ++ tailWord_4268632).sum := by decide
  have hdescent : baseEnd_4268632 < baseStart_4268632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268668 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_4268668 : Nat := 118140960795 + 4268668 * 2 ^ 59
def prefixEnd_4268668 : Nat := 4983230072969 + 3 ^ 40 * 4268668 * 2
def baseEnd_4268668 : Nat := 730626146155536683506253

theorem tailTrace_4268668 : CollatzResearch.WordTrace tailWord_4268668 prefixEnd_4268668 730626146155536683506253 := by
  unfold tailWord_4268668
  simp only [CollatzResearch.WordTrace]
  refine ⟨77845556249676170649215329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103794074999568227532287105 77845556249676170649215329)
  ·
    refine ⟨58384167187257127986911497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77845556249676170649215329 58384167187257127986911497)
    ·
      refine ⟨43788125390442845990183623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58384167187257127986911497 43788125390442845990183623)
      ·
        refine ⟨65682188085664268985275435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43788125390442845990183623 65682188085664268985275435)
        ·
          refine ⟨98523282128496403477913153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65682188085664268985275435 98523282128496403477913153)
          ·
            refine ⟨73892461596372302608434865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98523282128496403477913153 73892461596372302608434865)
            ·
              refine ⟨55419346197279226956326149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73892461596372302608434865 55419346197279226956326149)
              ·
                refine ⟨10391127411989855054311153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55419346197279226956326149 10391127411989855054311153)
                ·
                  refine ⟨7793345558992391290733365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10391127411989855054311153 7793345558992391290733365)
                  ·
                    refine ⟨730626146155536683506253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7793345558992391290733365 730626146155536683506253)
                    ·
                      rfl

theorem cell23_4268668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_4268668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268668 prefixEnd_4268668 := by exact prefixLift 4268668
  have htrace : WordTrace (prefixWord ++ tailWord_4268668) baseStart_4268668 baseEnd_4268668 := by
    simpa [prefixWord, tailWord_4268668, baseEnd_4268668] using wordTrace_append hprefix tailTrace_4268668
  have hstable : (prefixWord ++ tailWord_4268668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268668).length < 2 ^ (prefixWord ++ tailWord_4268668).sum := by decide
  have hdescent : baseEnd_4268668 < baseStart_4268668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268815 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_4268815 : Nat := 118140960795 + 4268815 * 2 ^ 59
def prefixEnd_4268815 : Nat := 4983230072969 + 3 ^ 40 * 4268815 * 2
def baseEnd_4268815 : Nat := 2191953920122820975380583

theorem tailTrace_4268815 : CollatzResearch.WordTrace tailWord_4268815 prefixEnd_4268815 2191953920122820975380583 := by
  unfold tailWord_4268815
  simp only [CollatzResearch.WordTrace]
  refine ⟨155696474029819785404031899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103797649353213190269354599 155696474029819785404031899)
  ·
    refine ⟨233544711044729678106047849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155696474029819785404031899 233544711044729678106047849)
    ·
      refine ⟨175158533283547258579535887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233544711044729678106047849 175158533283547258579535887)
      ·
        refine ⟨262737799925320887869303831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175158533283547258579535887 262737799925320887869303831)
        ·
          refine ⟨394106699887981331803955747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262737799925320887869303831 394106699887981331803955747)
          ·
            refine ⟨591160049831971997705933621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394106699887981331803955747 591160049831971997705933621)
            ·
              refine ⟨55421254671747374784931277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 591160049831971997705933621 55421254671747374784931277)
              ·
                refine ⟨20782970501905265544349229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55421254671747374784931277 20782970501905265544349229)
                ·
                  refine ⟨7793613938214474579130961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20782970501905265544349229 7793613938214474579130961)
                  ·
                    refine ⟨5845210453660855934348221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7793613938214474579130961 5845210453660855934348221)
                    ·
                      refine ⟨2191953920122820975380583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5845210453660855934348221 2191953920122820975380583)
                      ·
                        rfl

theorem cell23_4268815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_4268815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268815 prefixEnd_4268815 := by exact prefixLift 4268815
  have htrace : WordTrace (prefixWord ++ tailWord_4268815) baseStart_4268815 baseEnd_4268815 := by
    simpa [prefixWord, tailWord_4268815, baseEnd_4268815] using wordTrace_append hprefix tailTrace_4268815
  have hstable : (prefixWord ++ tailWord_4268815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268815).length < 2 ^ (prefixWord ++ tailWord_4268815).sum := by decide
  have hdescent : baseEnd_4268815 < baseStart_4268815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268846 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4268846 : Nat := 118140960795 + 4268846 * 2 ^ 59
def prefixEnd_4268846 : Nat := 4983230072969 + 3 ^ 40 * 4268846 * 2
def baseEnd_4268846 : Nat := 2191969838023110354092941

theorem tailTrace_4268846 : CollatzResearch.WordTrace tailWord_4268846 prefixEnd_4268846 2191969838023110354092941 := by
  unfold tailWord_4268846
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462200586588434712301299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103798403128471651798940261 19462200586588434712301299)
  ·
    refine ⟨29193300879882652068451949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19462200586588434712301299 29193300879882652068451949)
    ·
      refine ⟨10947487829955994525669481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29193300879882652068451949 10947487829955994525669481)
      ·
        refine ⟨8210615872466995894252111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10947487829955994525669481 8210615872466995894252111)
        ·
          refine ⟨12315923808700493841378167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210615872466995894252111 12315923808700493841378167)
          ·
            refine ⟨18473885713050740762067251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12315923808700493841378167 18473885713050740762067251)
            ·
              refine ⟨27710828569576111143100877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18473885713050740762067251 27710828569576111143100877)
              ·
                refine ⟨10391560713591041678662829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27710828569576111143100877 10391560713591041678662829)
                ·
                  refine ⟨3896835267596640629498561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10391560713591041678662829 3896835267596640629498561)
                  ·
                    refine ⟨2922626450697480472123921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896835267596640629498561 2922626450697480472123921)
                    ·
                      refine ⟨2191969838023110354092941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922626450697480472123921 2191969838023110354092941)
                      ·
                        rfl

theorem cell23_4268846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4268846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268846 prefixEnd_4268846 := by exact prefixLift 4268846
  have htrace : WordTrace (prefixWord ++ tailWord_4268846) baseStart_4268846 baseEnd_4268846 := by
    simpa [prefixWord, tailWord_4268846, baseEnd_4268846] using wordTrace_append hprefix tailTrace_4268846
  have hstable : (prefixWord ++ tailWord_4268846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268846).length < 2 ^ (prefixWord ++ tailWord_4268846).sum := by decide
  have hdescent : baseEnd_4268846 < baseStart_4268846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268848 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_4268848 : Nat := 118140960795 + 4268848 * 2 ^ 59
def prefixEnd_4268848 : Nat := 4983230072969 + 3 ^ 40 * 4268848 * 2
def baseEnd_4268848 : Nat := 730656954994806448755977

theorem tailTrace_4268848 : CollatzResearch.WordTrace tailWord_4268848 prefixEnd_4268848 730656954994806448755977 := by
  unfold tailWord_4268848
  simp only [CollatzResearch.WordTrace]
  refine ⟨77848838819350116019991599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103798451759133488026655465 77848838819350116019991599)
  ·
    refine ⟨116773258229025174029987399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77848838819350116019991599 116773258229025174029987399)
    ·
      refine ⟨175159887343537761044981099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116773258229025174029987399 175159887343537761044981099)
      ·
        refine ⟨262739831015306641567471649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175159887343537761044981099 262739831015306641567471649)
        ·
          refine ⟨197054873261479981175603737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262739831015306641567471649 197054873261479981175603737)
          ·
            refine ⟨147791154946109985881702803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197054873261479981175603737 147791154946109985881702803)
            ·
              refine ⟨221686732419164978822554205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147791154946109985881702803 221686732419164978822554205)
              ·
                refine ⟨83132524657186867058457827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221686732419164978822554205 83132524657186867058457827)
                ·
                  refine ⟨124698786985780300587686741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83132524657186867058457827 124698786985780300587686741)
                  ·
                    refine ⟨730656954994806448755977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124698786985780300587686741 730656954994806448755977)
                    ·
                      rfl

theorem cell23_4268848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_4268848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268848 prefixEnd_4268848 := by exact prefixLift 4268848
  have htrace : WordTrace (prefixWord ++ tailWord_4268848) baseStart_4268848 baseEnd_4268848 := by
    simpa [prefixWord, tailWord_4268848, baseEnd_4268848] using wordTrace_append hprefix tailTrace_4268848
  have hstable : (prefixWord ++ tailWord_4268848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268848).length < 2 ^ (prefixWord ++ tailWord_4268848).sum := by decide
  have hdescent : baseEnd_4268848 < baseStart_4268848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268889 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 1, 3, 2]
def baseStart_4268889 : Nat := 118140960795 + 4268889 * 2 ^ 59
def prefixEnd_4268889 : Nat := 4983230072969 + 3 ^ 40 * 4268889 * 2
def baseEnd_4268889 : Nat := 2191991917691253685855243

theorem tailTrace_4268889 : CollatzResearch.WordTrace tailWord_4268889 prefixEnd_4268889 2191991917691253685855243 := by
  unfold tailWord_4268889
  simp only [CollatzResearch.WordTrace]
  refine ⟨155699173031551696042225721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103799448687701130694817147 155699173031551696042225721)
  ·
    refine ⟨116774379773663772031669291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155699173031551696042225721 116774379773663772031669291)
    ·
      refine ⟨175161569660495658047503937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116774379773663772031669291 175161569660495658047503937)
      ·
        refine ⟨131371177245371743535627953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175161569660495658047503937 131371177245371743535627953)
        ·
          refine ⟨98528382934028807651720965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131371177245371743535627953 98528382934028807651720965)
          ·
            refine ⟨18474071800130401434697681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98528382934028807651720965 18474071800130401434697681)
            ·
              refine ⟨13855553850097801076023261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18474071800130401434697681 13855553850097801076023261)
              ·
                refine ⟨5195832693786675403508723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13855553850097801076023261 5195832693786675403508723)
                ·
                  refine ⟨7793749040680013105263085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195832693786675403508723 7793749040680013105263085)
                  ·
                    refine ⟨2922655890255004914473657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7793749040680013105263085 2922655890255004914473657)
                    ·
                      refine ⟨2191991917691253685855243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922655890255004914473657 2191991917691253685855243)
                      ·
                        rfl

theorem cell23_4268889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_4268889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268889 prefixEnd_4268889 := by exact prefixLift 4268889
  have htrace : WordTrace (prefixWord ++ tailWord_4268889) baseStart_4268889 baseEnd_4268889 := by
    simpa [prefixWord, tailWord_4268889, baseEnd_4268889] using wordTrace_append hprefix tailTrace_4268889
  have hstable : (prefixWord ++ tailWord_4268889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268889).length < 2 ^ (prefixWord ++ tailWord_4268889).sum := by decide
  have hdescent : baseEnd_4268889 < baseStart_4268889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268915 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_4268915 : Nat := 118140960795 + 4268915 * 2 ^ 59
def prefixEnd_4268915 : Nat := 4983230072969 + 3 ^ 40 * 4268915 * 2
def baseEnd_4268915 : Nat := 2192005268188270584130123

theorem tailTrace_4268915 : CollatzResearch.WordTrace tailWord_4268915 prefixEnd_4268915 2192005268188270584130123 := by
  unfold tailWord_4268915
  simp only [CollatzResearch.WordTrace]
  refine ⟨155700121329457502482672199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103800080886305001655114799 155700121329457502482672199)
  ·
    refine ⟨233550181994186253724008299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155700121329457502482672199 233550181994186253724008299)
    ·
      refine ⟨350325272991279380586012449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233550181994186253724008299 350325272991279380586012449)
      ·
        refine ⟨262743954743459535439509337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350325272991279380586012449 262743954743459535439509337)
        ·
          refine ⟨197057966057594651579632003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262743954743459535439509337 197057966057594651579632003)
          ·
            refine ⟨295586949086391977369448005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197057966057594651579632003 295586949086391977369448005)
            ·
              refine ⟨55422552953698495756771501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 295586949086391977369448005 55422552953698495756771501)
              ·
                refine ⟨20783457357636935908789313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55422552953698495756771501 20783457357636935908789313)
                ·
                  refine ⟨15587593018227701931591985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20783457357636935908789313 15587593018227701931591985)
                  ·
                    refine ⟨11690694763670776448693989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15587593018227701931591985 11690694763670776448693989)
                    ·
                      refine ⟨2192005268188270584130123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11690694763670776448693989 2192005268188270584130123)
                      ·
                        rfl

theorem cell23_4268915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_4268915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268915 prefixEnd_4268915 := by exact prefixLift 4268915
  have htrace : WordTrace (prefixWord ++ tailWord_4268915) baseStart_4268915 baseEnd_4268915 := by
    simpa [prefixWord, tailWord_4268915, baseEnd_4268915] using wordTrace_append hprefix tailTrace_4268915
  have hstable : (prefixWord ++ tailWord_4268915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268915).length < 2 ^ (prefixWord ++ tailWord_4268915).sum := by decide
  have hdescent : baseEnd_4268915 < baseStart_4268915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268925 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 7]
def baseStart_4268925 : Nat := 118140960795 + 4268925 * 2 ^ 59
def prefixEnd_4268925 : Nat := 4983230072969 + 3 ^ 40 * 4268925 * 2
def baseEnd_4268925 : Nat := 243556711443868393889453

theorem tailTrace_4268925 : CollatzResearch.WordTrace tailWord_4268925 prefixEnd_4268925 243556711443868393889453 := by
  unfold tailWord_4268925
  simp only [CollatzResearch.WordTrace]
  refine ⟨155700486059421274190536229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103800324039614182793690819 155700486059421274190536229)
  ·
    refine ⟨29193841136141488910725543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155700486059421274190536229 29193841136141488910725543)
    ·
      refine ⟨43790761704212233366088315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29193841136141488910725543 43790761704212233366088315)
      ·
        refine ⟨65686142556318350049132473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43790761704212233366088315 65686142556318350049132473)
        ·
          refine ⟨49264606917238762536849355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65686142556318350049132473 49264606917238762536849355)
          ·
            refine ⟨73896910375858143805274033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49264606917238762536849355 73896910375858143805274033)
            ·
              refine ⟨55422682781893607853955525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73896910375858143805274033 55422682781893607853955525)
              ·
                refine ⟨10391753021605051472616661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55422682781893607853955525 10391753021605051472616661)
                ·
                  refine ⟨243556711443868393889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10391753021605051472616661 243556711443868393889453)
                  ·
                    rfl

theorem cell23_4268925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_4268925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268925 prefixEnd_4268925 := by exact prefixLift 4268925
  have htrace : WordTrace (prefixWord ++ tailWord_4268925) baseStart_4268925 baseEnd_4268925 := by
    simpa [prefixWord, tailWord_4268925, baseEnd_4268925] using wordTrace_append hprefix tailTrace_4268925
  have hstable : (prefixWord ++ tailWord_4268925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268925).length < 2 ^ (prefixWord ++ tailWord_4268925).sum := by decide
  have hdescent : baseEnd_4268925 < baseStart_4268925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268959 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 5]
def baseStart_4268959 : Nat := 118140960795 + 4268959 * 2 ^ 59
def prefixEnd_4268959 : Nat := 4983230072969 + 3 ^ 40 * 4268959 * 2
def baseEnd_4268959 : Nat := 243558651259674267997769

theorem tailTrace_4268959 : CollatzResearch.WordTrace tailWord_4268959 prefixEnd_4268959 243558651259674267997769 := by
  unfold tailWord_4268959
  simp only [CollatzResearch.WordTrace]
  refine ⟨155701726141298097997273931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103801150760865398664849287 155701726141298097997273931)
  ·
    refine ⟨233552589211947146995910897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155701726141298097997273931 233552589211947146995910897)
    ·
      refine ⟨175164441908960360246933173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233552589211947146995910897 175164441908960360246933173)
      ·
        refine ⟨16421666428965033773149985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175164441908960360246933173 16421666428965033773149985)
        ·
          refine ⟨12316249821723775329862489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16421666428965033773149985 12316249821723775329862489)
          ·
            refine ⟨9237187366292831497396867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12316249821723775329862489 9237187366292831497396867)
            ·
              refine ⟨13855781049439247246095301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237187366292831497396867 13855781049439247246095301)
              ·
                refine ⟨2597958946769858858642869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13855781049439247246095301 2597958946769858858642869)
                ·
                  refine ⟨243558651259674267997769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597958946769858858642869 243558651259674267997769)
                  ·
                    rfl

theorem cell23_4268959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 5].length) (baseStart_4268959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268959 prefixEnd_4268959 := by exact prefixLift 4268959
  have htrace : WordTrace (prefixWord ++ tailWord_4268959) baseStart_4268959 baseEnd_4268959 := by
    simpa [prefixWord, tailWord_4268959, baseEnd_4268959] using wordTrace_append hprefix tailTrace_4268959
  have hstable : (prefixWord ++ tailWord_4268959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268959).length < 2 ^ (prefixWord ++ tailWord_4268959).sum := by decide
  have hdescent : baseEnd_4268959 < baseStart_4268959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4268992 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_4268992 : Nat := 118140960795 + 4268992 * 2 ^ 59
def prefixEnd_4268992 : Nat := 4983230072969 + 3 ^ 40 * 4268992 * 2
def baseEnd_4268992 : Nat := 2192044806198666782867269

theorem tailTrace_4268992 : CollatzResearch.WordTrace tailWord_4268992 prefixEnd_4268992 2192044806198666782867269 := by
  unfold tailWord_4268992
  simp only [CollatzResearch.WordTrace]
  refine ⟨77851464875089272316612615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103801953166785696422150153 77851464875089272316612615)
  ·
    refine ⟨116777197312633908474918923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77851464875089272316612615 116777197312633908474918923)
    ·
      refine ⟨175165795968950862712378385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116777197312633908474918923 175165795968950862712378385)
      ·
        refine ⟨131374346976713147034283789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175165795968950862712378385 131374346976713147034283789)
        ·
          refine ⟨49265380116267430137856421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131374346976713147034283789 49265380116267430137856421)
          ·
            refine ⟨9237258771800143150848079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49265380116267430137856421 9237258771800143150848079)
            ·
              refine ⟨13855888157700214726272119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237258771800143150848079 13855888157700214726272119)
              ·
                refine ⟨20783832236550322089408179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13855888157700214726272119 20783832236550322089408179)
                ·
                  refine ⟨31175748354825483134112269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20783832236550322089408179 31175748354825483134112269)
                  ·
                    refine ⟨11690905633059556175292101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31175748354825483134112269 11690905633059556175292101)
                    ·
                      refine ⟨2192044806198666782867269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11690905633059556175292101 2192044806198666782867269)
                      ·
                        rfl

theorem cell23_4268992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_4268992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4268992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4268992 prefixEnd_4268992 := by exact prefixLift 4268992
  have htrace : WordTrace (prefixWord ++ tailWord_4268992) baseStart_4268992 baseEnd_4268992 := by
    simpa [prefixWord, tailWord_4268992, baseEnd_4268992] using wordTrace_append hprefix tailTrace_4268992
  have hstable : (prefixWord ++ tailWord_4268992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4268992).length < 2 ^ (prefixWord ++ tailWord_4268992).sum := by decide
  have hdescent : baseEnd_4268992 < baseStart_4268992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4268992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269002 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_4269002 : Nat := 118140960795 + 4269002 * 2 ^ 59
def prefixEnd_4269002 : Nat := 4983230072969 + 3 ^ 40 * 4269002 * 2
def baseEnd_4269002 : Nat := 730683313668403914580741

theorem tailTrace_4269002 : CollatzResearch.WordTrace tailWord_4269002 prefixEnd_4269002 730683313668403914580741 := by
  unfold tailWord_4269002
  simp only [CollatzResearch.WordTrace]
  refine ⟨38925823620035579085272315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103802196320094877560726173 38925823620035579085272315)
  ·
    refine ⟨58388735430053368627908473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38925823620035579085272315 58388735430053368627908473)
    ·
      refine ⟨43791551572540026470931355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58388735430053368627908473 43791551572540026470931355)
      ·
        refine ⟨65687327358810039706397033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43791551572540026470931355 65687327358810039706397033)
        ·
          refine ⟨49265495519107529779797775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65687327358810039706397033 49265495519107529779797775)
          ·
            refine ⟨73898243278661294669696663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49265495519107529779797775 73898243278661294669696663)
            ·
              refine ⟨110847364917991942004544995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73898243278661294669696663 110847364917991942004544995)
              ·
                refine ⟨166271047376987913006817493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110847364917991942004544995 166271047376987913006817493)
                ·
                  refine ⟨3896977672898154211097285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 166271047376987913006817493 3896977672898154211097285)
                  ·
                    refine ⟨730683313668403914580741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3896977672898154211097285 730683313668403914580741)
                    ·
                      rfl

theorem cell23_4269002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_4269002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269002 prefixEnd_4269002 := by exact prefixLift 4269002
  have htrace : WordTrace (prefixWord ++ tailWord_4269002) baseStart_4269002 baseEnd_4269002 := by
    simpa [prefixWord, tailWord_4269002, baseEnd_4269002] using wordTrace_append hprefix tailTrace_4269002
  have hstable : (prefixWord ++ tailWord_4269002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269002).length < 2 ^ (prefixWord ++ tailWord_4269002).sum := by decide
  have hdescent : baseEnd_4269002 < baseStart_4269002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269032 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 6]
def baseStart_4269032 : Nat := 118140960795 + 4269032 * 2 ^ 59
def prefixEnd_4269032 : Nat := 4983230072969 + 3 ^ 40 * 4269032 * 2
def baseEnd_4269032 : Nat := 243562816158316291818565

theorem tailTrace_4269032 : CollatzResearch.WordTrace tailWord_4269032 prefixEnd_4269032 243562816158316291818565 := by
  unfold tailWord_4269032
  simp only [CollatzResearch.WordTrace]
  refine ⟨77852194335016815732340675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103802925780022420976454233 77852194335016815732340675)
  ·
    refine ⟨116778291502525223598511013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77852194335016815732340675 116778291502525223598511013)
    ·
      refine ⟨21895929656723479424720815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116778291502525223598511013 21895929656723479424720815)
      ·
        refine ⟨32843894485085219137081223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21895929656723479424720815 32843894485085219137081223)
        ·
          refine ⟨49265841727627828705621835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32843894485085219137081223 49265841727627828705621835)
          ·
            refine ⟨73898762591441743058432753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49265841727627828705621835 73898762591441743058432753)
            ·
              refine ⟨55424071943581307293824565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73898762591441743058432753 55424071943581307293824565)
              ·
                refine ⟨5196006744710747558796053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55424071943581307293824565 5196006744710747558796053)
                ·
                  refine ⟨243562816158316291818565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5196006744710747558796053 243562816158316291818565)
                  ·
                    rfl

theorem cell23_4269032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_4269032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269032 prefixEnd_4269032 := by exact prefixLift 4269032
  have htrace : WordTrace (prefixWord ++ tailWord_4269032) baseStart_4269032 baseEnd_4269032 := by
    simpa [prefixWord, tailWord_4269032, baseEnd_4269032] using wordTrace_append hprefix tailTrace_4269032
  have hstable : (prefixWord ++ tailWord_4269032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269032).length < 2 ^ (prefixWord ++ tailWord_4269032).sum := by decide
  have hdescent : baseEnd_4269032 < baseStart_4269032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
