import V185TrunkScan21Chunk081

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_995260 : List Nat := [2, 2, 2, 5, 2, 1, 7]
def baseStart_995260 : Nat := 118140960795 + 995260 * 2 ^ 59
def prefixEnd_995260 : Nat := 4983230072969 + 3 ^ 40 * 995260 * 2
def baseEnd_995260 : Nat := 25236876849080556759155

theorem tailTrace_995260 : CollatzResearch.WordTrace tailWord_995260 prefixEnd_995260 25236876849080556759155 := by
  unfold tailWord_995260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150057187175235860279617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24200076249566981147039489 18150057187175235860279617)
  ·
    refine ⟨13612542890381426895209713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18150057187175235860279617 13612542890381426895209713)
    ·
      refine ⟨10209407167786070171407285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13612542890381426895209713 10209407167786070171407285)
      ·
        refine ⟨957131921979944078569433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10209407167786070171407285 957131921979944078569433)
        ·
          refine ⟨717848941484958058927075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957131921979944078569433 717848941484958058927075)
          ·
            refine ⟨1076773412227437088390613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717848941484958058927075 1076773412227437088390613)
            ·
              refine ⟨25236876849080556759155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1076773412227437088390613 25236876849080556759155)
              ·
                rfl

theorem cell21_995260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 7].length) (baseStart_995260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995260 prefixEnd_995260 := by exact prefixLift 995260
  have htrace : WordTrace (prefixWord ++ tailWord_995260) baseStart_995260 baseEnd_995260 := by
    simpa [prefixWord, tailWord_995260, baseEnd_995260] using wordTrace_append hprefix tailTrace_995260
  have hstable : (prefixWord ++ tailWord_995260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995260).length < 2 ^ (prefixWord ++ tailWord_995260).sum := by decide
  have hdescent : baseEnd_995260 < baseStart_995260 := by decide
  rcases family_descends (prefixWord ++ tailWord_995260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995271 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_995271 : Nat := 118140960795 + 995271 * 2 ^ 59
def prefixEnd_995271 : Nat := 4983230072969 + 3 ^ 40 * 995271 * 2
def baseEnd_995271 : Nat := 227134401991591436149039

theorem tailTrace_995271 : CollatzResearch.WordTrace tailWord_995271 prefixEnd_995271 227134401991591436149039 := by
  unfold tailWord_995271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36300515577310620599209667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24200343718207080399473111 36300515577310620599209667)
  ·
    refine ⟨54450773365965930898814501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36300515577310620599209667 54450773365965930898814501)
    ·
      refine ⟨10209520006118612043527719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54450773365965930898814501 10209520006118612043527719)
      ·
        refine ⟨15314280009177918065291579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209520006118612043527719 15314280009177918065291579)
        ·
          refine ⟨22971420013766877097937369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15314280009177918065291579 22971420013766877097937369)
          ·
            refine ⟨17228565010325157823453027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22971420013766877097937369 17228565010325157823453027)
            ·
              refine ⟨25842847515487736735179541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228565010325157823453027 25842847515487736735179541)
              ·
                refine ⟨1211383477288487659461541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25842847515487736735179541 1211383477288487659461541)
                ·
                  refine ⟨227134401991591436149039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211383477288487659461541 227134401991591436149039)
                  ·
                    rfl

theorem cell21_995271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_995271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995271 prefixEnd_995271 := by exact prefixLift 995271
  have htrace : WordTrace (prefixWord ++ tailWord_995271) baseStart_995271 baseEnd_995271 := by
    simpa [prefixWord, tailWord_995271, baseEnd_995271] using wordTrace_append hprefix tailTrace_995271
  have hstable : (prefixWord ++ tailWord_995271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995271).length < 2 ^ (prefixWord ++ tailWord_995271).sum := by decide
  have hdescent : baseEnd_995271 < baseStart_995271 := by decide
  rcases family_descends (prefixWord ++ tailWord_995271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995347 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_995347 : Nat := 118140960795 + 995347 * 2 ^ 59
def prefixEnd_995347 : Nat := 4983230072969 + 3 ^ 40 * 995347 * 2
def baseEnd_995347 : Nat := 227151746227032192882217

theorem tailTrace_995347 : CollatzResearch.WordTrace tailWord_995347 prefixEnd_995347 227151746227032192882217 := by
  unfold tailWord_995347
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303287525035285578976295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24202191683356857052650863 36303287525035285578976295)
  ·
    refine ⟨54454931287552928368464443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303287525035285578976295 54454931287552928368464443)
    ·
      refine ⟨81682396931329392552696665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54454931287552928368464443 81682396931329392552696665)
      ·
        refine ⟨61261797698497044414522499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81682396931329392552696665 61261797698497044414522499)
        ·
          refine ⟨91892696547745566621783749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61261797698497044414522499 91892696547745566621783749)
          ·
            refine ⟨17229880602702293741584453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91892696547745566621783749 17229880602702293741584453)
            ·
              refine ⟨3230602613006680076547085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17229880602702293741584453 3230602613006680076547085)
              ·
                refine ⟨1211475979877505028705157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230602613006680076547085 1211475979877505028705157)
                ·
                  refine ⟨227151746227032192882217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211475979877505028705157 227151746227032192882217)
                  ·
                    rfl

theorem cell21_995347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_995347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995347 prefixEnd_995347 := by exact prefixLift 995347
  have htrace : WordTrace (prefixWord ++ tailWord_995347) baseStart_995347 baseEnd_995347 := by
    simpa [prefixWord, tailWord_995347, baseEnd_995347] using wordTrace_append hprefix tailTrace_995347
  have hstable : (prefixWord ++ tailWord_995347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995347).length < 2 ^ (prefixWord ++ tailWord_995347).sum := by decide
  have hdescent : baseEnd_995347 < baseStart_995347 := by decide
  rcases family_descends (prefixWord ++ tailWord_995347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995392 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_995392 : Nat := 118140960795 + 995392 * 2 ^ 59
def prefixEnd_995392 : Nat := 4983230072969 + 3 ^ 40 * 995392 * 2
def baseEnd_995392 : Nat := 227162015840122114632125

theorem tailTrace_995392 : CollatzResearch.WordTrace tailWord_995392 prefixEnd_995392 227162015840122114632125 := by
  unfold tailWord_995392
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152464404936129132182215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24203285873248172176242953 18152464404936129132182215)
  ·
    refine ⟨27228696607404193698273323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18152464404936129132182215 27228696607404193698273323)
    ·
      refine ⟨40843044911106290547409985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27228696607404193698273323 40843044911106290547409985)
      ·
        refine ⟨30632283683329717910557489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40843044911106290547409985 30632283683329717910557489)
        ·
          refine ⟨22974212762497288432918117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30632283683329717910557489 22974212762497288432918117)
          ·
            refine ⟨4307664892968241581172147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22974212762497288432918117 4307664892968241581172147)
            ·
              refine ⟨6461497339452362371758221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307664892968241581172147 6461497339452362371758221)
              ·
                refine ⟨2423061502294635889409333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6461497339452362371758221 2423061502294635889409333)
                ·
                  refine ⟨227162015840122114632125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423061502294635889409333 227162015840122114632125)
                  ·
                    rfl

theorem cell21_995392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_995392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995392 prefixEnd_995392 := by exact prefixLift 995392
  have htrace : WordTrace (prefixWord ++ tailWord_995392) baseStart_995392 baseEnd_995392 := by
    simpa [prefixWord, tailWord_995392, baseEnd_995392] using wordTrace_append hprefix tailTrace_995392
  have hstable : (prefixWord ++ tailWord_995392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995392).length < 2 ^ (prefixWord ++ tailWord_995392).sum := by decide
  have hdescent : baseEnd_995392 < baseStart_995392 := by decide
  rcases family_descends (prefixWord ++ tailWord_995392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995398 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_995398 : Nat := 118140960795 + 995398 * 2 ^ 59
def prefixEnd_995398 : Nat := 4983230072969 + 3 ^ 40 * 995398 * 2
def baseEnd_995398 : Nat := 227163385121867437532113

theorem tailTrace_995398 : CollatzResearch.WordTrace tailWord_995398 prefixEnd_995398 227163385121867437532113 := by
  unfold tailWord_995398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134535863995328790283839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24203431765233680859388565 1134535863995328790283839)
  ·
    refine ⟨1701803795992993185425759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134535863995328790283839 1701803795992993185425759)
    ·
      refine ⟨2552705693989489778138639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701803795992993185425759 2552705693989489778138639)
      ·
        refine ⟨3829058540984234667207959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552705693989489778138639 3829058540984234667207959)
        ·
          refine ⟨5743587811476352000811939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829058540984234667207959 5743587811476352000811939)
          ·
            refine ⟨8615381717214528001217909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743587811476352000811939 8615381717214528001217909)
            ·
              refine ⟨807692035988862000114179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8615381717214528001217909 807692035988862000114179)
              ·
                refine ⟨1211538053983293000171269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807692035988862000114179 1211538053983293000171269)
                ·
                  refine ⟨227163385121867437532113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211538053983293000171269 227163385121867437532113)
                  ·
                    rfl

theorem cell21_995398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_995398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995398 prefixEnd_995398 := by exact prefixLift 995398
  have htrace : WordTrace (prefixWord ++ tailWord_995398) baseStart_995398 baseEnd_995398 := by
    simpa [prefixWord, tailWord_995398, baseEnd_995398] using wordTrace_append hprefix tailTrace_995398
  have hstable : (prefixWord ++ tailWord_995398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995398).length < 2 ^ (prefixWord ++ tailWord_995398).sum := by decide
  have hdescent : baseEnd_995398 < baseStart_995398 := by decide
  rcases family_descends (prefixWord ++ tailWord_995398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995530 : List Nat := [3, 1, 2, 1, 3, 1, 5, 5]
def baseStart_995530 : Nat := 118140960795 + 995530 * 2 ^ 59
def prefixEnd_995530 : Nat := 4983230072969 + 3 ^ 40 * 995530 * 2
def baseEnd_995530 : Nat := 75731169773421513777281

theorem tailTrace_995530 : CollatzResearch.WordTrace tailWord_995530 prefixEnd_995530 75731169773421513777281 := by
  unfold tailWord_995530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077490520843076958222011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24206641388914871888592029 9077490520843076958222011)
  ·
    refine ⟨13616235781264615437333017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077490520843076958222011 13616235781264615437333017)
    ·
      refine ⟨10212176835948461577999763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13616235781264615437333017 10212176835948461577999763)
      ·
        refine ⟨15318265253922692366999645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212176835948461577999763 15318265253922692366999645)
        ·
          refine ⟨5744349470221009637624867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15318265253922692366999645 5744349470221009637624867)
          ·
            refine ⟨8616524205331514456437301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744349470221009637624867 8616524205331514456437301)
            ·
              refine ⟨807799144249829480290997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8616524205331514456437301 807799144249829480290997)
              ·
                refine ⟨75731169773421513777281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 807799144249829480290997 75731169773421513777281)
                ·
                  rfl

theorem cell21_995530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_995530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995530 prefixEnd_995530 := by exact prefixLift 995530
  have htrace : WordTrace (prefixWord ++ tailWord_995530) baseStart_995530 baseEnd_995530 := by
    simpa [prefixWord, tailWord_995530, baseEnd_995530] using wordTrace_append hprefix tailTrace_995530
  have hstable : (prefixWord ++ tailWord_995530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995530).length < 2 ^ (prefixWord ++ tailWord_995530).sum := by decide
  have hdescent : baseEnd_995530 < baseStart_995530 := by decide
  rcases family_descends (prefixWord ++ tailWord_995530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995603 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_995603 : Nat := 118140960795 + 995603 * 2 ^ 59
def prefixEnd_995603 : Nat := 4983230072969 + 3 ^ 40 * 995603 * 2
def baseEnd_995603 : Nat := 227210168914832636615027

theorem tailTrace_995603 : CollatzResearch.WordTrace tailWord_995603 prefixEnd_995603 227210168914832636615027 := by
  unfold tailWord_995603
  simp only [CollatzResearch.WordTrace]
  refine ⟨36312624612107841300295463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24208416408071894200196975 36312624612107841300295463)
  ·
    refine ⟨54468936918161761950443195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36312624612107841300295463 54468936918161761950443195)
    ·
      refine ⟨81703405377242642925664793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54468936918161761950443195 81703405377242642925664793)
      ·
        refine ⟨61277554032931982194248595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81703405377242642925664793 61277554032931982194248595)
        ·
          refine ⟨91916331049397973291372893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61277554032931982194248595 91916331049397973291372893)
          ·
            refine ⟨34468624143524239984264835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91916331049397973291372893 34468624143524239984264835)
            ·
              refine ⟨51702936215286359976397253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34468624143524239984264835 51702936215286359976397253)
              ·
                refine ⟨9694300540366192495574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51702936215286359976397253 9694300540366192495574485)
                ·
                  refine ⟨227210168914832636615027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9694300540366192495574485 227210168914832636615027)
                  ·
                    rfl

theorem cell21_995603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_995603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995603 prefixEnd_995603 := by exact prefixLift 995603
  have htrace : WordTrace (prefixWord ++ tailWord_995603) baseStart_995603 baseEnd_995603 := by
    simpa [prefixWord, tailWord_995603, baseEnd_995603] using wordTrace_append hprefix tailTrace_995603
  have hstable : (prefixWord ++ tailWord_995603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995603).length < 2 ^ (prefixWord ++ tailWord_995603).sum := by decide
  have hdescent : baseEnd_995603 < baseStart_995603 := by decide
  rcases family_descends (prefixWord ++ tailWord_995603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995626 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_995626 : Nat := 118140960795 + 995626 * 2 ^ 59
def prefixEnd_995626 : Nat := 4983230072969 + 3 ^ 40 * 995626 * 2
def baseEnd_995626 : Nat := 227215417828189707731647

theorem tailTrace_995626 : CollatzResearch.WordTrace tailWord_995626 prefixEnd_995626 227215417828189707731647 := by
  unfold tailWord_995626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078365872756129057095683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24208975660683010818921821 9078365872756129057095683)
  ·
    refine ⟨13617548809134193585643525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9078365872756129057095683 13617548809134193585643525)
    ·
      refine ⟨2553290401712661297308161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13617548809134193585643525 2553290401712661297308161)
      ·
        refine ⟨1914967801284495972981121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553290401712661297308161 1914967801284495972981121)
        ·
          refine ⟨1436225850963371979735841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914967801284495972981121 1436225850963371979735841)
          ·
            refine ⟨1077169388222528984801881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436225850963371979735841 1077169388222528984801881)
            ·
              refine ⟨807877041166896738601411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077169388222528984801881 807877041166896738601411)
              ·
                refine ⟨1211815561750345107902117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807877041166896738601411 1211815561750345107902117)
                ·
                  refine ⟨227215417828189707731647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211815561750345107902117 227215417828189707731647)
                  ·
                    rfl

theorem cell21_995626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_995626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995626 prefixEnd_995626 := by exact prefixLift 995626
  have htrace : WordTrace (prefixWord ++ tailWord_995626) baseStart_995626 baseEnd_995626 := by
    simpa [prefixWord, tailWord_995626, baseEnd_995626] using wordTrace_append hprefix tailTrace_995626
  have hstable : (prefixWord ++ tailWord_995626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995626).length < 2 ^ (prefixWord ++ tailWord_995626).sum := by decide
  have hdescent : baseEnd_995626 < baseStart_995626 := by decide
  rcases family_descends (prefixWord ++ tailWord_995626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995668 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_995668 : Nat := 118140960795 + 995668 * 2 ^ 59
def prefixEnd_995668 : Nat := 4983230072969 + 3 ^ 40 * 995668 * 2
def baseEnd_995668 : Nat := 227225002800406968031561

theorem tailTrace_995668 : CollatzResearch.WordTrace tailWord_995668 prefixEnd_995668 227225002800406968031561 := by
  unfold tailWord_995668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157497678436178700705829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24209996904581571600941105 18157497678436178700705829)
  ·
    refine ⟨3404530814706783506382343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18157497678436178700705829 3404530814706783506382343)
    ·
      refine ⟨5106796222060175259573515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404530814706783506382343 5106796222060175259573515)
      ·
        refine ⟨7660194333090262889360273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106796222060175259573515 7660194333090262889360273)
        ·
          refine ⟨5745145749817697167020205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660194333090262889360273 5745145749817697167020205)
          ·
            refine ⟨2154429656181636437632577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5745145749817697167020205 2154429656181636437632577)
            ·
              refine ⟨1615822242136227328224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154429656181636437632577 1615822242136227328224433)
              ·
                refine ⟨1211866681602170496168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615822242136227328224433 1211866681602170496168325)
                ·
                  refine ⟨227225002800406968031561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211866681602170496168325 227225002800406968031561)
                  ·
                    rfl

theorem cell21_995668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_995668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995668 prefixEnd_995668 := by exact prefixLift 995668
  have htrace : WordTrace (prefixWord ++ tailWord_995668) baseStart_995668 baseEnd_995668 := by
    simpa [prefixWord, tailWord_995668, baseEnd_995668] using wordTrace_append hprefix tailTrace_995668
  have hstable : (prefixWord ++ tailWord_995668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995668).length < 2 ^ (prefixWord ++ tailWord_995668).sum := by decide
  have hdescent : baseEnd_995668 < baseStart_995668 := by decide
  rcases family_descends (prefixWord ++ tailWord_995668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995682 : List Nat := [3, 3, 2, 1, 1, 2, 3, 6]
def baseStart_995682 : Nat := 118140960795 + 995682 * 2 ^ 59
def prefixEnd_995682 : Nat := 4983230072969 + 3 ^ 40 * 995682 * 2
def baseEnd_995682 : Nat := 75742732597048684932733

theorem tailTrace_995682 : CollatzResearch.WordTrace tailWord_995682 prefixEnd_995682 75742732597048684932733 := by
  unfold tailWord_995682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078876494705409448105325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24210337319214425194947533 9078876494705409448105325)
  ·
    refine ⟨3404578685514528543039497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9078876494705409448105325 3404578685514528543039497)
    ·
      refine ⟨2553434014135896407279623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3404578685514528543039497 2553434014135896407279623)
      ·
        refine ⟨3830151021203844610919435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553434014135896407279623 3830151021203844610919435)
        ·
          refine ⟨5745226531805766916379153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830151021203844610919435 5745226531805766916379153)
          ·
            refine ⟨4308919898854325187284365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5745226531805766916379153 4308919898854325187284365)
            ·
              refine ⟨1615844962070371945231637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4308919898854325187284365 1615844962070371945231637)
              ·
                refine ⟨75742732597048684932733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1615844962070371945231637 75742732597048684932733)
                ·
                  rfl

theorem cell21_995682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_995682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995682 prefixEnd_995682 := by exact prefixLift 995682
  have htrace : WordTrace (prefixWord ++ tailWord_995682) baseStart_995682 baseEnd_995682 := by
    simpa [prefixWord, tailWord_995682, baseEnd_995682] using wordTrace_append hprefix tailTrace_995682
  have hstable : (prefixWord ++ tailWord_995682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995682).length < 2 ^ (prefixWord ++ tailWord_995682).sum := by decide
  have hdescent : baseEnd_995682 < baseStart_995682 := by decide
  rcases family_descends (prefixWord ++ tailWord_995682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995696 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_995696 : Nat := 118140960795 + 995696 * 2 ^ 59
def prefixEnd_995696 : Nat := 4983230072969 + 3 ^ 40 * 995696 * 2
def baseEnd_995696 : Nat := 227231392781885141564837

theorem tailTrace_995696 : CollatzResearch.WordTrace tailWord_995696 prefixEnd_995696 227231392781885141564837 := by
  unfold tailWord_995696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158008300385459091715471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24210677733847278788953961 18158008300385459091715471)
  ·
    refine ⟨27237012450578188637573207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18158008300385459091715471 27237012450578188637573207)
    ·
      refine ⟨40855518675867282956359811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27237012450578188637573207 40855518675867282956359811)
      ·
        refine ⟨61283278013800924434539717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40855518675867282956359811 61283278013800924434539717)
        ·
          refine ⟨11490614627587673331476197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61283278013800924434539717 11490614627587673331476197)
          ·
            refine ⟨2154490242672688749651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11490614627587673331476197 2154490242672688749651787)
            ·
              refine ⟨3231735364009033124477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154490242672688749651787 3231735364009033124477681)
              ·
                refine ⟨2423801523006774843358261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231735364009033124477681 2423801523006774843358261)
                ·
                  refine ⟨227231392781885141564837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423801523006774843358261 227231392781885141564837)
                  ·
                    rfl

theorem cell21_995696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_995696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995696 prefixEnd_995696 := by exact prefixLift 995696
  have htrace : WordTrace (prefixWord ++ tailWord_995696) baseStart_995696 baseEnd_995696 := by
    simpa [prefixWord, tailWord_995696, baseEnd_995696] using wordTrace_append hprefix tailTrace_995696
  have hstable : (prefixWord ++ tailWord_995696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995696).length < 2 ^ (prefixWord ++ tailWord_995696).sum := by decide
  have hdescent : baseEnd_995696 < baseStart_995696 := by decide
  rcases family_descends (prefixWord ++ tailWord_995696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995744 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_995744 : Nat := 118140960795 + 995744 * 2 ^ 59
def prefixEnd_995744 : Nat := 4983230072969 + 3 ^ 40 * 995744 * 2
def baseEnd_995744 : Nat := 227242347035847724764739

theorem tailTrace_995744 : CollatzResearch.WordTrace tailWord_995744 prefixEnd_995744 227242347035847724764739 := by
  unfold tailWord_995744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158883652298511190589143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24211844869731348254118857 18158883652298511190589143)
  ·
    refine ⟨27238325478447766785883715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18158883652298511190589143 27238325478447766785883715)
    ·
      refine ⟨40857488217671650178825573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238325478447766785883715 40857488217671650178825573)
      ·
        refine ⟨7660779040813434408529795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40857488217671650178825573 7660779040813434408529795)
        ·
          refine ⟨11491168561220151612794693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660779040813434408529795 11491168561220151612794693)
          ·
            refine ⟨2154594105228778427399005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11491168561220151612794693 2154594105228778427399005)
            ·
              refine ⟨807972789460791910274627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2154594105228778427399005 807972789460791910274627)
              ·
                refine ⟨1211959184191187865411941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807972789460791910274627 1211959184191187865411941)
                ·
                  refine ⟨227242347035847724764739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211959184191187865411941 227242347035847724764739)
                  ·
                    rfl

theorem cell21_995744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_995744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995744 prefixEnd_995744 := by exact prefixLift 995744
  have htrace : WordTrace (prefixWord ++ tailWord_995744) baseStart_995744 baseEnd_995744 := by
    simpa [prefixWord, tailWord_995744, baseEnd_995744] using wordTrace_append hprefix tailTrace_995744
  have hstable : (prefixWord ++ tailWord_995744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995744).length < 2 ^ (prefixWord ++ tailWord_995744).sum := by decide
  have hdescent : baseEnd_995744 < baseStart_995744 := by decide
  rcases family_descends (prefixWord ++ tailWord_995744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995786 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_995786 : Nat := 118140960795 + 995786 * 2 ^ 59
def prefixEnd_995786 : Nat := 4983230072969 + 3 ^ 40 * 995786 * 2
def baseEnd_995786 : Nat := 227251932008064985064653

theorem tailTrace_995786 : CollatzResearch.WordTrace tailWord_995786 prefixEnd_995786 227251932008064985064653 := by
  unfold tailWord_995786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079824792611215888551803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24212866113629909036138141 9079824792611215888551803)
  ·
    refine ⟨13619737188916823832827705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079824792611215888551803 13619737188916823832827705)
    ·
      refine ⟨10214802891687617874620779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13619737188916823832827705 10214802891687617874620779)
      ·
        refine ⟨15322204337531426811931169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214802891687617874620779 15322204337531426811931169)
        ·
          refine ⟨11491653253148570108948377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15322204337531426811931169 11491653253148570108948377)
          ·
            refine ⟨8618739939861427581711283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11491653253148570108948377 8618739939861427581711283)
            ·
              refine ⟨12928109909792141372566925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618739939861427581711283 12928109909792141372566925)
              ·
                refine ⟨4848041216172053014712597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12928109909792141372566925 4848041216172053014712597)
                ·
                  refine ⟨227251932008064985064653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4848041216172053014712597 227251932008064985064653)
                  ·
                    rfl

theorem cell21_995786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_995786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995786 prefixEnd_995786 := by exact prefixLift 995786
  have htrace : WordTrace (prefixWord ++ tailWord_995786) baseStart_995786 baseEnd_995786 := by
    simpa [prefixWord, tailWord_995786, baseEnd_995786] using wordTrace_append hprefix tailTrace_995786
  have hstable : (prefixWord ++ tailWord_995786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995786).length < 2 ^ (prefixWord ++ tailWord_995786).sum := by decide
  have hdescent : baseEnd_995786 < baseStart_995786 := by decide
  rcases family_descends (prefixWord ++ tailWord_995786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995882 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_995882 : Nat := 118140960795 + 995882 * 2 ^ 59
def prefixEnd_995882 : Nat := 4983230072969 + 3 ^ 40 * 995882 * 2
def baseEnd_995882 : Nat := 227273840515990151464457

theorem tailTrace_995882 : CollatzResearch.WordTrace tailWord_995882 prefixEnd_995882 227273840515990151464457 := by
  unfold tailWord_995882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080700144524267987425475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24215200385398047966467933 9080700144524267987425475)
  ·
    refine ⟨13621050216786401981138213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080700144524267987425475 13621050216786401981138213)
    ·
      refine ⟨2553946915647450371463415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13621050216786401981138213 2553946915647450371463415)
      ·
        refine ⟨3830920373471175557195123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553946915647450371463415 3830920373471175557195123)
        ·
          refine ⟨5746380560206763335792685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830920373471175557195123 5746380560206763335792685)
          ·
            refine ⟨2154892710077536250922257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5746380560206763335792685 2154892710077536250922257)
            ·
              refine ⟨1616169532558152188191693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154892710077536250922257 1616169532558152188191693)
              ·
                refine ⟨606063574709307070571885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616169532558152188191693 606063574709307070571885)
                ·
                  refine ⟨227273840515990151464457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606063574709307070571885 227273840515990151464457)
                  ·
                    rfl

theorem cell21_995882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_995882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995882 prefixEnd_995882 := by exact prefixLift 995882
  have htrace : WordTrace (prefixWord ++ tailWord_995882) baseStart_995882 baseEnd_995882 := by
    simpa [prefixWord, tailWord_995882, baseEnd_995882] using wordTrace_append hprefix tailTrace_995882
  have hstable : (prefixWord ++ tailWord_995882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995882).length < 2 ^ (prefixWord ++ tailWord_995882).sum := by decide
  have hdescent : baseEnd_995882 < baseStart_995882 := by decide
  rcases family_descends (prefixWord ++ tailWord_995882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995924 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_995924 : Nat := 118140960795 + 995924 * 2 ^ 59
def prefixEnd_995924 : Nat := 4983230072969 + 3 ^ 40 * 995924 * 2
def baseEnd_995924 : Nat := 227283425488207411764371

theorem tailTrace_995924 : CollatzResearch.WordTrace tailWord_995924 prefixEnd_995924 227283425488207411764371 := by
  unfold tailWord_995924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162166221972456561365413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24216221629296608748487217 18162166221972456561365413)
  ·
    refine ⟨3405406166619835605256015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18162166221972456561365413 3405406166619835605256015)
    ·
      refine ⟨5108109249929753407884023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405406166619835605256015 5108109249929753407884023)
      ·
        refine ⟨7662163874894630111826035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108109249929753407884023 7662163874894630111826035)
        ·
          refine ⟨11493245812341945167739053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662163874894630111826035 11493245812341945167739053)
          ·
            refine ⟨4309967179628229437902145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11493245812341945167739053 4309967179628229437902145)
            ·
              refine ⟨3232475384721172078426609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309967179628229437902145 3232475384721172078426609)
              ·
                refine ⟨2424356538540879058819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3232475384721172078426609 2424356538540879058819957)
                ·
                  refine ⟨227283425488207411764371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2424356538540879058819957 227283425488207411764371)
                  ·
                    rfl

theorem cell21_995924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_995924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995924 prefixEnd_995924 := by exact prefixLift 995924
  have htrace : WordTrace (prefixWord ++ tailWord_995924) baseStart_995924 baseEnd_995924 := by
    simpa [prefixWord, tailWord_995924, baseEnd_995924] using wordTrace_append hprefix tailTrace_995924
  have hstable : (prefixWord ++ tailWord_995924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995924).length < 2 ^ (prefixWord ++ tailWord_995924).sum := by decide
  have hdescent : baseEnd_995924 < baseStart_995924 := by decide
  rcases family_descends (prefixWord ++ tailWord_995924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995958 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_995958 : Nat := 118140960795 + 995958 * 2 ^ 59
def prefixEnd_995958 : Nat := 4983230072969 + 3 ^ 40 * 995958 * 2
def baseEnd_995958 : Nat := 227291184751430908197635

theorem tailTrace_995958 : CollatzResearch.WordTrace tailWord_995958 prefixEnd_995958 227291184751430908197635 := by
  unfold tailWord_995958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270348282863858558091783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24217048350547824619645685 2270348282863858558091783)
  ·
    refine ⟨3405522424295787837137675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270348282863858558091783 3405522424295787837137675)
    ·
      refine ⟨5108283636443681755706513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405522424295787837137675 5108283636443681755706513)
      ·
        refine ⟨3831212727332761316779885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5108283636443681755706513 3831212727332761316779885)
        ·
          refine ⟨1436704772749785493792457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3831212727332761316779885 1436704772749785493792457)
          ·
            refine ⟨1077528579562339120344343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436704772749785493792457 1077528579562339120344343)
            ·
              refine ⟨1616292869343508680516515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077528579562339120344343 1616292869343508680516515)
              ·
                refine ⟨2424439304015263020774773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616292869343508680516515 2424439304015263020774773)
                ·
                  refine ⟨227291184751430908197635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2424439304015263020774773 227291184751430908197635)
                  ·
                    rfl

theorem cell21_995958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_995958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995958 prefixEnd_995958 := by exact prefixLift 995958
  have htrace : WordTrace (prefixWord ++ tailWord_995958) baseStart_995958 baseEnd_995958 := by
    simpa [prefixWord, tailWord_995958, baseEnd_995958] using wordTrace_append hprefix tailTrace_995958
  have hstable : (prefixWord ++ tailWord_995958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995958).length < 2 ^ (prefixWord ++ tailWord_995958).sum := by decide
  have hdescent : baseEnd_995958 < baseStart_995958 := by decide
  rcases family_descends (prefixWord ++ tailWord_995958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995969 : List Nat := [1, 2, 4, 2, 1, 1, 4, 6]
def baseStart_995969 : Nat := 118140960795 + 995969 * 2 ^ 59
def prefixEnd_995969 : Nat := 4983230072969 + 3 ^ 40 * 995969 * 2
def baseEnd_995969 : Nat := 75764565033765777838093

theorem tailTrace_995969 : CollatzResearch.WordTrace tailWord_995969 prefixEnd_995969 75764565033765777838093 := by
  unfold tailWord_995969
  simp only [CollatzResearch.WordTrace]
  refine ⟨36325973728781885808118961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217315819187923872079307 36325973728781885808118961)
  ·
    refine ⟨27244480296586414356089221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36325973728781885808118961 27244480296586414356089221)
    ·
      refine ⟨5108340055609952691766729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27244480296586414356089221 5108340055609952691766729)
      ·
        refine ⟨3831255041707464518825047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5108340055609952691766729 3831255041707464518825047)
        ·
          refine ⟨5746882562561196778237571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831255041707464518825047 5746882562561196778237571)
          ·
            refine ⟨8620323843841795167356357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746882562561196778237571 8620323843841795167356357)
            ·
              refine ⟨1616310720720336593879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8620323843841795167356357 1616310720720336593879317)
              ·
                refine ⟨75764565033765777838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1616310720720336593879317 75764565033765777838093)
                ·
                  rfl

theorem cell21_995969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_995969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995969 prefixEnd_995969 := by exact prefixLift 995969
  have htrace : WordTrace (prefixWord ++ tailWord_995969) baseStart_995969 baseEnd_995969 := by
    simpa [prefixWord, tailWord_995969, baseEnd_995969] using wordTrace_append hprefix tailTrace_995969
  have hstable : (prefixWord ++ tailWord_995969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995969).length < 2 ^ (prefixWord ++ tailWord_995969).sum := by decide
  have hdescent : baseEnd_995969 < baseStart_995969 := by decide
  rcases family_descends (prefixWord ++ tailWord_995969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995972 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_995972 : Nat := 118140960795 + 995972 * 2 ^ 59
def prefixEnd_995972 : Nat := 4983230072969 + 3 ^ 40 * 995972 * 2
def baseEnd_995972 : Nat := 227294379742169994964273

theorem tailTrace_995972 : CollatzResearch.WordTrace tailWord_995972 prefixEnd_995972 227294379742169994964273 := by
  unfold tailWord_995972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163041573885508660239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24217388765180678213652113 18163041573885508660239085)
  ·
    refine ⟨6811140590207065747589657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18163041573885508660239085 6811140590207065747589657)
    ·
      refine ⟨5108355442655299310692243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6811140590207065747589657 5108355442655299310692243)
      ·
        refine ⟨7662533163982948966038365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108355442655299310692243 7662533163982948966038365)
        ·
          refine ⟨2873449936493605862264387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7662533163982948966038365 2873449936493605862264387)
          ·
            refine ⟨4310174904740408793396581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873449936493605862264387 4310174904740408793396581)
            ·
              refine ⟨808157794638826648761859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4310174904740408793396581 808157794638826648761859)
              ·
                refine ⟨1212236691958239973142789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808157794638826648761859 1212236691958239973142789)
                ·
                  refine ⟨227294379742169994964273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212236691958239973142789 227294379742169994964273)
                  ·
                    rfl

theorem cell21_995972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_995972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995972 prefixEnd_995972 := by exact prefixLift 995972
  have htrace : WordTrace (prefixWord ++ tailWord_995972) baseStart_995972 baseEnd_995972 := by
    simpa [prefixWord, tailWord_995972, baseEnd_995972] using wordTrace_append hprefix tailTrace_995972
  have hstable : (prefixWord ++ tailWord_995972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995972).length < 2 ^ (prefixWord ++ tailWord_995972).sum := by decide
  have hdescent : baseEnd_995972 < baseStart_995972 := by decide
  rcases family_descends (prefixWord ++ tailWord_995972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996090 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_996090 : Nat := 118140960795 + 996090 * 2 ^ 59
def prefixEnd_996090 : Nat := 4983230072969 + 3 ^ 40 * 996090 * 2
def baseEnd_996090 : Nat := 227321308949828011997365

theorem tailTrace_996090 : CollatzResearch.WordTrace tailWord_996090 prefixEnd_996090 227321308949828011997365 := by
  unfold tailWord_996090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082596740335880868318431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24220257974229015648849149 9082596740335880868318431)
  ·
    refine ⟨13623895110503821302477647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9082596740335880868318431 13623895110503821302477647)
    ·
      refine ⟨20435842665755731953716471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13623895110503821302477647 20435842665755731953716471)
      ·
        refine ⟨30653763998633597930574707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435842665755731953716471 30653763998633597930574707)
        ·
          refine ⟨45980645997950396895862061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30653763998633597930574707 45980645997950396895862061)
          ·
            refine ⟨17242742249231398835948273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45980645997950396895862061 17242742249231398835948273)
            ·
              refine ⟨12932056686923549126961205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17242742249231398835948273 12932056686923549126961205)
              ·
                refine ⟨1212380314399082730652613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12932056686923549126961205 1212380314399082730652613)
                ·
                  refine ⟨227321308949828011997365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212380314399082730652613 227321308949828011997365)
                  ·
                    rfl

theorem cell21_996090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_996090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996090 prefixEnd_996090 := by exact prefixLift 996090
  have htrace : WordTrace (prefixWord ++ tailWord_996090) baseStart_996090 baseEnd_996090 := by
    simpa [prefixWord, tailWord_996090, baseEnd_996090] using wordTrace_append hprefix tailTrace_996090
  have hstable : (prefixWord ++ tailWord_996090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996090).length < 2 ^ (prefixWord ++ tailWord_996090).sum := by decide
  have hdescent : baseEnd_996090 < baseStart_996090 := by decide
  rcases family_descends (prefixWord ++ tailWord_996090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996141 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_996141 : Nat := 118140960795 + 996141 * 2 ^ 59
def prefixEnd_996141 : Nat := 4983230072969 + 3 ^ 40 * 996141 * 2
def baseEnd_996141 : Nat := 227332947844663256647261

theorem tailTrace_996141 : CollatzResearch.WordTrace tailWord_996141 prefixEnd_996141 227332947844663256647261 := by
  unfold tailWord_996141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36332247084158759183380277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24221498056105839455586851 36332247084158759183380277)
  ·
    refine ⟨3406148164139883673441901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36332247084158759183380277 3406148164139883673441901)
    ·
      refine ⟨1277305561552456377540713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3406148164139883673441901 1277305561552456377540713)
      ·
        refine ⟨957979171164342283155535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277305561552456377540713 957979171164342283155535)
        ·
          refine ⟨1436968756746513424733303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957979171164342283155535 1436968756746513424733303)
          ·
            refine ⟨2155453135119770137099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436968756746513424733303 2155453135119770137099955)
            ·
              refine ⟨3233179702679655205649933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155453135119770137099955 3233179702679655205649933)
              ·
                refine ⟨1212442388504870702118725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3233179702679655205649933 1212442388504870702118725)
                ·
                  refine ⟨227332947844663256647261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212442388504870702118725 227332947844663256647261)
                  ·
                    rfl

theorem cell21_996141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_996141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996141 prefixEnd_996141 := by exact prefixLift 996141
  have htrace : WordTrace (prefixWord ++ tailWord_996141) baseStart_996141 baseEnd_996141 := by
    simpa [prefixWord, tailWord_996141, baseEnd_996141] using wordTrace_append hprefix tailTrace_996141
  have hstable : (prefixWord ++ tailWord_996141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996141).length < 2 ^ (prefixWord ++ tailWord_996141).sum := by decide
  have hdescent : baseEnd_996141 < baseStart_996141 := by decide
  rcases family_descends (prefixWord ++ tailWord_996141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996180 : List Nat := [2, 4, 1, 1, 13]
def baseStart_996180 : Nat := 118140960795 + 996180 * 2 ^ 59
def prefixEnd_996180 : Nat := 4983230072969 + 3 ^ 40 * 996180 * 2
def baseEnd_996180 : Nat := 2806689483654417969101

theorem tailTrace_996180 : CollatzResearch.WordTrace tailWord_996180 prefixEnd_996180 2806689483654417969101 := by
  unfold tailWord_996180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166834765508734422024997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24222446354011645896033329 18166834765508734422024997)
  ·
    refine ⟨3406281518532887704129687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18166834765508734422024997 3406281518532887704129687)
    ·
      refine ⟨5109422277799331556194531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406281518532887704129687 5109422277799331556194531)
      ·
        refine ⟨7664133416698997334291797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109422277799331556194531 7664133416698997334291797)
        ·
          refine ⟨2806689483654417969101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7664133416698997334291797 2806689483654417969101)
          ·
            rfl

theorem cell21_996180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 13].length) (baseStart_996180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996180 prefixEnd_996180 := by exact prefixLift 996180
  have htrace : WordTrace (prefixWord ++ tailWord_996180) baseStart_996180 baseEnd_996180 := by
    simpa [prefixWord, tailWord_996180, baseEnd_996180] using wordTrace_append hprefix tailTrace_996180
  have hstable : (prefixWord ++ tailWord_996180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996180).length < 2 ^ (prefixWord ++ tailWord_996180).sum := by decide
  have hdescent : baseEnd_996180 < baseStart_996180 := by decide
  rcases family_descends (prefixWord ++ tailWord_996180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996183 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_996183 : Nat := 118140960795 + 996183 * 2 ^ 59
def prefixEnd_996183 : Nat := 4983230072969 + 3 ^ 40 * 996183 * 2
def baseEnd_996183 : Nat := 227342532816880516947175

theorem tailTrace_996183 : CollatzResearch.WordTrace tailWord_996183 prefixEnd_996183 227342532816880516947175 := by
  unfold tailWord_996183
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333778950006600356409203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24222519300004400237606135 36333778950006600356409203)
  ·
    refine ⟨54500668425009900534613805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36333778950006600356409203 54500668425009900534613805)
    ·
      refine ⟨20437750659378712700480177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54500668425009900534613805 20437750659378712700480177)
      ·
        refine ⟨15328312994534034525360133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20437750659378712700480177 15328312994534034525360133)
        ·
          refine ⟨2874058686475131473505025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15328312994534034525360133 2874058686475131473505025)
          ·
            refine ⟨2155544014856348605128769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874058686475131473505025 2155544014856348605128769)
            ·
              refine ⟨1616658011142261453846577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155544014856348605128769 1616658011142261453846577)
              ·
                refine ⟨1212493508356696090384933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616658011142261453846577 1212493508356696090384933)
                ·
                  refine ⟨227342532816880516947175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212493508356696090384933 227342532816880516947175)
                  ·
                    rfl

theorem cell21_996183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_996183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996183 prefixEnd_996183 := by exact prefixLift 996183
  have htrace : WordTrace (prefixWord ++ tailWord_996183) baseStart_996183 baseEnd_996183 := by
    simpa [prefixWord, tailWord_996183, baseEnd_996183] using wordTrace_append hprefix tailTrace_996183
  have hstable : (prefixWord ++ tailWord_996183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996183).length < 2 ^ (prefixWord ++ tailWord_996183).sum := by decide
  have hdescent : baseEnd_996183 < baseStart_996183 := by decide
  rcases family_descends (prefixWord ++ tailWord_996183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996186 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_996186 : Nat := 118140960795 + 996186 * 2 ^ 59
def prefixEnd_996186 : Nat := 4983230072969 + 3 ^ 40 * 996186 * 2
def baseEnd_996186 : Nat := 227343217457753178397169

theorem tailTrace_996186 : CollatzResearch.WordTrace tailWord_996186 prefixEnd_996186 227343217457753178397169 := by
  unfold tailWord_996186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9083472092248932967192103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24222592245997154579178941 9083472092248932967192103)
  ·
    refine ⟨13625208138373399450788155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9083472092248932967192103 13625208138373399450788155)
    ·
      refine ⟨20437812207560099176182233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625208138373399450788155 20437812207560099176182233)
      ·
        refine ⟨15328359155670074382136675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20437812207560099176182233 15328359155670074382136675)
        ·
          refine ⟨22992538733505111573205013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15328359155670074382136675 22992538733505111573205013)
          ·
            refine ⟨1077775253133052104993985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22992538733505111573205013 1077775253133052104993985)
            ·
              refine ⟨808331439849789078745489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077775253133052104993985 808331439849789078745489)
              ·
                refine ⟨606248579887341809059117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808331439849789078745489 606248579887341809059117)
                ·
                  refine ⟨227343217457753178397169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606248579887341809059117 227343217457753178397169)
                  ·
                    rfl

theorem cell21_996186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_996186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996186 prefixEnd_996186 := by exact prefixLift 996186
  have htrace : WordTrace (prefixWord ++ tailWord_996186) baseStart_996186 baseEnd_996186 := by
    simpa [prefixWord, tailWord_996186, baseEnd_996186] using wordTrace_append hprefix tailTrace_996186
  have hstable : (prefixWord ++ tailWord_996186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996186).length < 2 ^ (prefixWord ++ tailWord_996186).sum := by decide
  have hdescent : baseEnd_996186 < baseStart_996186 := by decide
  rcases family_descends (prefixWord ++ tailWord_996186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996273 : List Nat := [1, 2, 2, 4, 3, 1, 1, 7]
def baseStart_996273 : Nat := 118140960795 + 996273 * 2 ^ 59
def prefixEnd_996273 : Nat := 4983230072969 + 3 ^ 40 * 996273 * 2
def baseEnd_996273 : Nat := 75787690681020120148997

theorem tailTrace_996273 : CollatzResearch.WordTrace tailWord_996273 prefixEnd_996273 75787690681020120148997 := by
  unfold tailWord_996273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337061519680545727185473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24224707679787030484790315 36337061519680545727185473)
  ·
    refine ⟨27252796139760409295389105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36337061519680545727185473 27252796139760409295389105)
    ·
      refine ⟨20439597104820306971541829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27252796139760409295389105 20439597104820306971541829)
      ·
        refine ⟨3832424457153807557164093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20439597104820306971541829 3832424457153807557164093)
        ·
          refine ⟨1437159171432677833936535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3832424457153807557164093 1437159171432677833936535)
          ·
            refine ⟨2155738757149016750904803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437159171432677833936535 2155738757149016750904803)
            ·
              refine ⟨3233608135723525126357205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155738757149016750904803 3233608135723525126357205)
              ·
                refine ⟨75787690681020120148997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3233608135723525126357205 75787690681020120148997)
                ·
                  rfl

theorem cell21_996273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_996273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996273 prefixEnd_996273 := by exact prefixLift 996273
  have htrace : WordTrace (prefixWord ++ tailWord_996273) baseStart_996273 baseEnd_996273 := by
    simpa [prefixWord, tailWord_996273, baseEnd_996273] using wordTrace_append hprefix tailTrace_996273
  have hstable : (prefixWord ++ tailWord_996273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996273).length < 2 ^ (prefixWord ++ tailWord_996273).sum := by decide
  have hdescent : baseEnd_996273 < baseStart_996273 := by decide
  rcases family_descends (prefixWord ++ tailWord_996273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996380 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_996380 : Nat := 118140960795 + 996380 * 2 ^ 59
def prefixEnd_996380 : Nat := 4983230072969 + 3 ^ 40 * 996380 * 2
def baseEnd_996380 : Nat := 227387490900851952163439

theorem tailTrace_996380 : CollatzResearch.WordTrace tailWord_996380 prefixEnd_996380 227387490900851952163439 := by
  unfold tailWord_996380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18170482065146451500665297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24227309420195268667553729 18170482065146451500665297)
  ·
    refine ⟨13627861548859838625498973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18170482065146451500665297 13627861548859838625498973)
    ·
      refine ⟨5110448080822439484562115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13627861548859838625498973 5110448080822439484562115)
      ·
        refine ⟨7665672121233659226843173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110448080822439484562115 7665672121233659226843173)
        ·
          refine ⟨1437313522731311105033095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7665672121233659226843173 1437313522731311105033095)
          ·
            refine ⟨2155970284096966657549643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437313522731311105033095 2155970284096966657549643)
            ·
              refine ⟨3233955426145449986324465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155970284096966657549643 3233955426145449986324465)
              ·
                refine ⟨2425466569609087489743349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233955426145449986324465 2425466569609087489743349)
                ·
                  refine ⟨227387490900851952163439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425466569609087489743349 227387490900851952163439)
                  ·
                    rfl

theorem cell21_996380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_996380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996380 prefixEnd_996380 := by exact prefixLift 996380
  have htrace : WordTrace (prefixWord ++ tailWord_996380) baseStart_996380 baseEnd_996380 := by
    simpa [prefixWord, tailWord_996380, baseEnd_996380] using wordTrace_append hprefix tailTrace_996380
  have hstable : (prefixWord ++ tailWord_996380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996380).length < 2 ^ (prefixWord ++ tailWord_996380).sum := by decide
  have hdescent : baseEnd_996380 < baseStart_996380 := by decide
  rcases family_descends (prefixWord ++ tailWord_996380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996408 : List Nat := [2, 1, 2, 1, 5, 2, 8]
def baseStart_996408 : Nat := 118140960795 + 996408 * 2 ^ 59
def prefixEnd_996408 : Nat := 4983230072969 + 3 ^ 40 * 996408 * 2
def baseEnd_996408 : Nat := 25265986764703347299635

theorem tailTrace_996408 : CollatzResearch.WordTrace tailWord_996408 prefixEnd_996408 25265986764703347299635 := by
  unfold tailWord_996408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18170992687095731891674939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24227990249460975855566585 18170992687095731891674939)
  ·
    refine ⟨27256489030643597837512409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18170992687095731891674939 27256489030643597837512409)
    ·
      refine ⟨20442366772982698378134307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27256489030643597837512409 20442366772982698378134307)
      ·
        refine ⟨30663550159474047567201461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442366772982698378134307 30663550159474047567201461)
        ·
          refine ⟨2874707827450691959425137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30663550159474047567201461 2874707827450691959425137)
          ·
            refine ⟨2156030870588018969568853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874707827450691959425137 2156030870588018969568853)
            ·
              refine ⟨25265986764703347299635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2156030870588018969568853 25265986764703347299635)
              ·
                rfl

theorem cell21_996408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 8].length) (baseStart_996408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996408 prefixEnd_996408 := by exact prefixLift 996408
  have htrace : WordTrace (prefixWord ++ tailWord_996408) baseStart_996408 baseEnd_996408 := by
    simpa [prefixWord, tailWord_996408, baseEnd_996408] using wordTrace_append hprefix tailTrace_996408
  have hstable : (prefixWord ++ tailWord_996408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996408).length < 2 ^ (prefixWord ++ tailWord_996408).sum := by decide
  have hdescent : baseEnd_996408 < baseStart_996408 := by decide
  rcases family_descends (prefixWord ++ tailWord_996408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996453 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_996453 : Nat := 118140960795 + 996453 * 2 ^ 59
def prefixEnd_996453 : Nat := 4983230072969 + 3 ^ 40 * 996453 * 2
def baseEnd_996453 : Nat := 227404150495420047446623

theorem tailTrace_996453 : CollatzResearch.WordTrace tailWord_996453 prefixEnd_996453 227404150495420047446623 := by
  unfold tailWord_996453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36343626659028436468738013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24229084439352290979158675 36343626659028436468738013)
  ·
    refine ⟨13628859997135663675776755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36343626659028436468738013 13628859997135663675776755)
    ·
      refine ⟨20443289995703495513665133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628859997135663675776755 20443289995703495513665133)
      ·
        refine ⟨7666233748388810817624425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20443289995703495513665133 7666233748388810817624425)
        ·
          refine ⟨5749675311291608113218319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7666233748388810817624425 5749675311291608113218319)
          ·
            refine ⟨8624512966937412169827479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749675311291608113218319 8624512966937412169827479)
            ·
              refine ⟨12936769450406118254741219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624512966937412169827479 12936769450406118254741219)
              ·
                refine ⟨19405154175609177382111829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12936769450406118254741219 19405154175609177382111829)
                ·
                  refine ⟨227404150495420047446623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19405154175609177382111829 227404150495420047446623)
                  ·
                    rfl

theorem cell21_996453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_996453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996453 prefixEnd_996453 := by exact prefixLift 996453
  have htrace : WordTrace (prefixWord ++ tailWord_996453) baseStart_996453 baseEnd_996453 := by
    simpa [prefixWord, tailWord_996453, baseEnd_996453] using wordTrace_append hprefix tailTrace_996453
  have hstable : (prefixWord ++ tailWord_996453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996453).length < 2 ^ (prefixWord ++ tailWord_996453).sum := by decide
  have hdescent : baseEnd_996453 < baseStart_996453 := by decide
  rcases family_descends (prefixWord ++ tailWord_996453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996470 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_996470 : Nat := 118140960795 + 996470 * 2 ^ 59
def prefixEnd_996470 : Nat := 4983230072969 + 3 ^ 40 * 996470 * 2
def baseEnd_996470 : Nat := 227408030127031795663255

theorem tailTrace_996470 : CollatzResearch.WordTrace tailWord_996470 prefixEnd_996470 227408030127031795663255 := by
  unfold tailWord_996470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271515418747928023256679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24229497799977898914737909 2271515418747928023256679)
  ·
    refine ⟨3407273128121892034885019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271515418747928023256679 3407273128121892034885019)
    ·
      refine ⟨5110909692182838052327529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407273128121892034885019 5110909692182838052327529)
      ·
        refine ⟨3833182269137128539245647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110909692182838052327529 3833182269137128539245647)
        ·
          refine ⟨5749773403705692808868471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833182269137128539245647 5749773403705692808868471)
          ·
            refine ⟨8624660105558539213302707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749773403705692808868471 8624660105558539213302707)
            ·
              refine ⟨12936990158337808819954061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624660105558539213302707 12936990158337808819954061)
              ·
                refine ⟨4851371309376678307482773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12936990158337808819954061 4851371309376678307482773)
                ·
                  refine ⟨227408030127031795663255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4851371309376678307482773 227408030127031795663255)
                  ·
                    rfl

theorem cell21_996470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_996470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996470 prefixEnd_996470 := by exact prefixLift 996470
  have htrace : WordTrace (prefixWord ++ tailWord_996470) baseStart_996470 baseEnd_996470 := by
    simpa [prefixWord, tailWord_996470, baseEnd_996470] using wordTrace_append hprefix tailTrace_996470
  have hstable : (prefixWord ++ tailWord_996470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996470).length < 2 ^ (prefixWord ++ tailWord_996470).sum := by decide
  have hdescent : baseEnd_996470 < baseStart_996470 := by decide
  rcases family_descends (prefixWord ++ tailWord_996470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996473 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 5]
def baseStart_996473 : Nat := 118140960795 + 996473 * 2 ^ 59
def prefixEnd_996473 : Nat := 4983230072969 + 3 ^ 40 * 996473 * 2
def baseEnd_996473 : Nat := 227408714767904457113249

theorem tailTrace_996473 : CollatzResearch.WordTrace tailWord_996473 prefixEnd_996473 227408714767904457113249 := by
  unfold tailWord_996473
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344356118955979884466073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24229570745970653256310715 36344356118955979884466073)
  ·
    refine ⟨27258267089216984913349555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36344356118955979884466073 27258267089216984913349555)
    ·
      refine ⟨40887400633825477370024333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27258267089216984913349555 40887400633825477370024333)
      ·
        refine ⟨15332775237684554013759125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40887400633825477370024333 15332775237684554013759125)
        ·
          refine ⟨718723839266463469394959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15332775237684554013759125 718723839266463469394959)
          ·
            refine ⟨1078085758899695204092439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718723839266463469394959 1078085758899695204092439)
            ·
              refine ⟨1617128638349542806138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078085758899695204092439 1617128638349542806138659)
              ·
                refine ⟨2425692957524314209207989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617128638349542806138659 2425692957524314209207989)
                ·
                  refine ⟨227408714767904457113249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425692957524314209207989 227408714767904457113249)
                  ·
                    rfl

theorem cell21_996473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_996473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996473 prefixEnd_996473 := by exact prefixLift 996473
  have htrace : WordTrace (prefixWord ++ tailWord_996473) baseStart_996473 baseEnd_996473 := by
    simpa [prefixWord, tailWord_996473, baseEnd_996473] using wordTrace_append hprefix tailTrace_996473
  have hstable : (prefixWord ++ tailWord_996473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996473).length < 2 ^ (prefixWord ++ tailWord_996473).sum := by decide
  have hdescent : baseEnd_996473 < baseStart_996473 := by decide
  rcases family_descends (prefixWord ++ tailWord_996473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996484 : List Nat := [2, 3, 2, 1, 2, 2, 1, 8]
def baseStart_996484 : Nat := 118140960795 + 996484 * 2 ^ 59
def prefixEnd_996484 : Nat := 4983230072969 + 3 ^ 40 * 996484 * 2
def baseEnd_996484 : Nat := 75803741705923627476631

theorem tailTrace_996484 : CollatzResearch.WordTrace tailWord_996484 prefixEnd_996484 75803741705923627476631 := by
  unfold tailWord_996484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172378660958064381558253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24229838214610752508744337 18172378660958064381558253)
  ·
    refine ⟨6814641997859274143084345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18172378660958064381558253 6814641997859274143084345)
    ·
      refine ⟨5110981498394455607313259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6814641997859274143084345 5110981498394455607313259)
      ·
        refine ⟨7666472247591683410969889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110981498394455607313259 7666472247591683410969889)
        ·
          refine ⟨5749854185693762558227417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7666472247591683410969889 5749854185693762558227417)
          ·
            refine ⟨4312390639270321918670563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5749854185693762558227417 4312390639270321918670563)
            ·
              refine ⟨6468585958905482878005845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312390639270321918670563 6468585958905482878005845)
              ·
                refine ⟨75803741705923627476631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6468585958905482878005845 75803741705923627476631)
                ·
                  rfl

theorem cell21_996484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_996484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996484 prefixEnd_996484 := by exact prefixLift 996484
  have htrace : WordTrace (prefixWord ++ tailWord_996484) baseStart_996484 baseEnd_996484 := by
    simpa [prefixWord, tailWord_996484, baseEnd_996484] using wordTrace_append hprefix tailTrace_996484
  have hstable : (prefixWord ++ tailWord_996484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996484).length < 2 ^ (prefixWord ++ tailWord_996484).sum := by decide
  have hdescent : baseEnd_996484 < baseStart_996484 := by decide
  rcases family_descends (prefixWord ++ tailWord_996484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996642 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_996642 : Nat := 118140960795 + 996642 * 2 ^ 59
def prefixEnd_996642 : Nat := 4983230072969 + 3 ^ 40 * 996642 * 2
def baseEnd_996642 : Nat := 227447282870397718796237

theorem tailTrace_996642 : CollatzResearch.WordTrace tailWord_996642 prefixEnd_996642 227447282870397718796237 := by
  unfold tailWord_996642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087630013835930436842045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24233680036895814498245453 9087630013835930436842045)
  ·
    refine ⟨3407861255188473913815767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9087630013835930436842045 3407861255188473913815767)
    ·
      refine ⟨5111791882782710870723651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407861255188473913815767 5111791882782710870723651)
      ·
        refine ⟨7667687824174066306085477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111791882782710870723651 7667687824174066306085477)
        ·
          refine ⟨1437691467032637432391027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7667687824174066306085477 1437691467032637432391027)
          ·
            refine ⟨2156537200548956148586541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437691467032637432391027 2156537200548956148586541)
            ·
              refine ⟨808701450205858555719953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156537200548956148586541 808701450205858555719953)
              ·
                refine ⟨606526087654393916789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808701450205858555719953 606526087654393916789965)
                ·
                  refine ⟨227447282870397718796237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606526087654393916789965 227447282870397718796237)
                  ·
                    rfl

theorem cell21_996642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_996642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996642 prefixEnd_996642 := by exact prefixLift 996642
  have htrace : WordTrace (prefixWord ++ tailWord_996642) baseStart_996642 baseEnd_996642 := by
    simpa [prefixWord, tailWord_996642, baseEnd_996642] using wordTrace_append hprefix tailTrace_996642
  have hstable : (prefixWord ++ tailWord_996642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996642).length < 2 ^ (prefixWord ++ tailWord_996642).sum := by decide
  have hdescent : baseEnd_996642 < baseStart_996642 := by decide
  rcases family_descends (prefixWord ++ tailWord_996642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996653 : List Nat := [1, 5, 3, 1, 1, 1, 1, 8]
def baseStart_996653 : Nat := 118140960795 + 996653 * 2 ^ 59
def prefixEnd_996653 : Nat := 4983230072969 + 3 ^ 40 * 996653 * 2
def baseEnd_996653 : Nat := 75816597740088048037627

theorem tailTrace_996653 : CollatzResearch.WordTrace tailWord_996653 prefixEnd_996653 75816597740088048037627 := by
  unfold tailWord_996653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36350921258303870626018613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24233947505535913750679075 36350921258303870626018613)
  ·
    refine ⟨3407898867965987871189245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36350921258303870626018613 3407898867965987871189245)
    ·
      refine ⟨1277962075487245451695967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3407898867965987871189245 1277962075487245451695967)
      ·
        refine ⟨1916943113230868177543951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277962075487245451695967 1916943113230868177543951)
        ·
          refine ⟨2875414669846302266315927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916943113230868177543951 2875414669846302266315927)
          ·
            refine ⟨4313122004769453399473891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875414669846302266315927 4313122004769453399473891)
            ·
              refine ⟨6469683007154180099210837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313122004769453399473891 6469683007154180099210837)
              ·
                refine ⟨75816597740088048037627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6469683007154180099210837 75816597740088048037627)
                ·
                  rfl

theorem cell21_996653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_996653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996653 prefixEnd_996653 := by exact prefixLift 996653
  have htrace : WordTrace (prefixWord ++ tailWord_996653) baseStart_996653 baseEnd_996653 := by
    simpa [prefixWord, tailWord_996653, baseEnd_996653] using wordTrace_append hprefix tailTrace_996653
  have hstable : (prefixWord ++ tailWord_996653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996653).length < 2 ^ (prefixWord ++ tailWord_996653).sum := by decide
  have hdescent : baseEnd_996653 < baseStart_996653 := by decide
  rcases family_descends (prefixWord ++ tailWord_996653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996695 : List Nat := [1, 1, 3, 2, 3, 11]
def baseStart_996695 : Nat := 118140960795 + 996695 * 2 ^ 59
def prefixEnd_996695 : Nat := 4983230072969 + 3 ^ 40 * 996695 * 2
def baseEnd_996695 : Nat := 8424421414536348311585

theorem tailTrace_996695 : CollatzResearch.WordTrace tailWord_996695 prefixEnd_996695 8424421414536348311585 := by
  unfold tailWord_996695
  simp only [CollatzResearch.WordTrace]
  refine ⟨36352453124151711799047539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24234968749434474532698359 36352453124151711799047539)
  ·
    refine ⟨54528679686227567698571309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36352453124151711799047539 54528679686227567698571309)
    ·
      refine ⟨20448254882335337886964241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54528679686227567698571309 20448254882335337886964241)
      ·
        refine ⟨15336191161751503415223181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20448254882335337886964241 15336191161751503415223181)
        ·
          refine ⟨5751071685656813780708693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15336191161751503415223181 5751071685656813780708693)
          ·
            refine ⟨8424421414536348311585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5751071685656813780708693 8424421414536348311585)
            ·
              rfl

theorem cell21_996695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 11].length) (baseStart_996695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996695 prefixEnd_996695 := by exact prefixLift 996695
  have htrace : WordTrace (prefixWord ++ tailWord_996695) baseStart_996695 baseEnd_996695 := by
    simpa [prefixWord, tailWord_996695, baseEnd_996695] using wordTrace_append hprefix tailTrace_996695
  have hstable : (prefixWord ++ tailWord_996695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996695).length < 2 ^ (prefixWord ++ tailWord_996695).sum := by decide
  have hdescent : baseEnd_996695 < baseStart_996695 := by decide
  rcases family_descends (prefixWord ++ tailWord_996695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996760 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_996760 : Nat := 118140960795 + 996760 * 2 ^ 59
def prefixEnd_996760 : Nat := 4983230072969 + 3 ^ 40 * 996760 * 2
def baseEnd_996760 : Nat := 227474212078055735829329

theorem tailTrace_996760 : CollatzResearch.WordTrace tailWord_996760 prefixEnd_996760 227474212078055735829329 := by
  unfold tailWord_996760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177411934458113950081867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24236549245944151933442489 18177411934458113950081867)
  ·
    refine ⟨27266117901687170925122801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18177411934458113950081867 27266117901687170925122801)
    ·
      refine ⟨20449588426265378193842101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27266117901687170925122801 20449588426265378193842101)
      ·
        refine ⟨1917148914962379205672697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20449588426265378193842101 1917148914962379205672697)
        ·
          refine ⟨1437861686221784404254523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917148914962379205672697 1437861686221784404254523)
          ·
            refine ⟨2156792529332676606381785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437861686221784404254523 2156792529332676606381785)
            ·
              refine ⟨1617594396999507454786339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156792529332676606381785 1617594396999507454786339)
              ·
                refine ⟨2426391595499261182179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617594396999507454786339 2426391595499261182179509)
                ·
                  refine ⟨227474212078055735829329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426391595499261182179509 227474212078055735829329)
                  ·
                    rfl

theorem cell21_996760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_996760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996760 prefixEnd_996760 := by exact prefixLift 996760
  have htrace : WordTrace (prefixWord ++ tailWord_996760) baseStart_996760 baseEnd_996760 := by
    simpa [prefixWord, tailWord_996760, baseEnd_996760] using wordTrace_append hprefix tailTrace_996760
  have hstable : (prefixWord ++ tailWord_996760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996760).length < 2 ^ (prefixWord ++ tailWord_996760).sum := by decide
  have hdescent : baseEnd_996760 < baseStart_996760 := by decide
  rcases family_descends (prefixWord ++ tailWord_996760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996771 : List Nat := [1, 1, 1, 4, 1, 3, 2, 8]
def baseStart_996771 : Nat := 118140960795 + 996771 * 2 ^ 59
def prefixEnd_996771 : Nat := 4983230072969 + 3 ^ 40 * 996771 * 2
def baseEnd_996771 : Nat := 75825574142640720381991

theorem tailTrace_996771 : CollatzResearch.WordTrace tailWord_996771 prefixEnd_996771 75825574142640720381991 := by
  unfold tailWord_996771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36355225071876376778814167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24236816714584251185876111 36355225071876376778814167)
  ·
    refine ⟨54532837607814565168221251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36355225071876376778814167 54532837607814565168221251)
    ·
      refine ⟨81799256411721847752331877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54532837607814565168221251 81799256411721847752331877)
      ·
        refine ⟨15337360577197846453562227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81799256411721847752331877 15337360577197846453562227)
        ·
          refine ⟨23006040865796769680343341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337360577197846453562227 23006040865796769680343341)
          ·
            refine ⟨8627265324673788630128753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23006040865796769680343341 8627265324673788630128753)
            ·
              refine ⟨6470448993505341472596565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8627265324673788630128753 6470448993505341472596565)
              ·
                refine ⟨75825574142640720381991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6470448993505341472596565 75825574142640720381991)
                ·
                  rfl

theorem cell21_996771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_996771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996771 prefixEnd_996771 := by exact prefixLift 996771
  have htrace : WordTrace (prefixWord ++ tailWord_996771) baseStart_996771 baseEnd_996771 := by
    simpa [prefixWord, tailWord_996771, baseEnd_996771] using wordTrace_append hprefix tailTrace_996771
  have hstable : (prefixWord ++ tailWord_996771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996771).length < 2 ^ (prefixWord ++ tailWord_996771).sum := by decide
  have hdescent : baseEnd_996771 < baseStart_996771 := by decide
  rcases family_descends (prefixWord ++ tailWord_996771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996847 : List Nat := [1, 1, 2, 1, 4, 1, 4, 7]
def baseStart_996847 : Nat := 118140960795 + 996847 * 2 ^ 59
def prefixEnd_996847 : Nat := 4983230072969 + 3 ^ 40 * 996847 * 2
def baseEnd_996847 : Nat := 75831355554454305959717

theorem tailTrace_996847 : CollatzResearch.WordTrace tailWord_996847 prefixEnd_996847 75831355554454305959717 := by
  unfold tailWord_996847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357997019601041758580795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24238664679734027839053863 36357997019601041758580795)
  ·
    refine ⟨54536995529401562637871193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36357997019601041758580795 54536995529401562637871193)
    ·
      refine ⟨40902746647051171978403395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54536995529401562637871193 40902746647051171978403395)
      ·
        refine ⟨61354119970576757967605093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40902746647051171978403395 61354119970576757967605093)
        ·
          refine ⟨11503897494483142118925955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61354119970576757967605093 11503897494483142118925955)
          ·
            refine ⟨17255846241724713178388933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503897494483142118925955 17255846241724713178388933)
            ·
              refine ⟨3235471170323383720947925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17255846241724713178388933 3235471170323383720947925)
              ·
                refine ⟨75831355554454305959717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3235471170323383720947925 75831355554454305959717)
                ·
                  rfl

theorem cell21_996847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_996847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996847 prefixEnd_996847 := by exact prefixLift 996847
  have htrace : WordTrace (prefixWord ++ tailWord_996847) baseStart_996847 baseEnd_996847 := by
    simpa [prefixWord, tailWord_996847, baseEnd_996847] using wordTrace_append hprefix tailTrace_996847
  have hstable : (prefixWord ++ tailWord_996847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996847).length < 2 ^ (prefixWord ++ tailWord_996847).sum := by decide
  have hdescent : baseEnd_996847 < baseStart_996847 := by decide
  rcases family_descends (prefixWord ++ tailWord_996847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996985 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_996985 : Nat := 118140960795 + 996985 * 2 ^ 59
def prefixEnd_996985 : Nat := 4983230072969 + 3 ^ 40 * 996985 * 2
def baseEnd_996985 : Nat := 227525560143505344578869

theorem tailTrace_996985 : CollatzResearch.WordTrace tailWord_996985 prefixEnd_996985 227525560143505344578869 := by
  unfold tailWord_996985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363030293101091327104409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24242020195400727551402939 36363030293101091327104409)
  ·
    refine ⟨27272272719825818495328307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36363030293101091327104409 27272272719825818495328307)
    ·
      refine ⟨40908409079738727742992461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27272272719825818495328307 40908409079738727742992461)
      ·
        refine ⟨15340653404902022903622173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40908409079738727742992461 15340653404902022903622173)
        ·
          refine ⟨5752745026838258588858315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15340653404902022903622173 5752745026838258588858315)
          ·
            refine ⟨8629117540257387883287473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752745026838258588858315 8629117540257387883287473)
            ·
              refine ⟨6471838155193040912465605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8629117540257387883287473 6471838155193040912465605)
              ·
                refine ⟨1213469654098695171087301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6471838155193040912465605 1213469654098695171087301)
                ·
                  refine ⟨227525560143505344578869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213469654098695171087301 227525560143505344578869)
                  ·
                    rfl

theorem cell21_996985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_996985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996985 prefixEnd_996985 := by exact prefixLift 996985
  have htrace : WordTrace (prefixWord ++ tailWord_996985) baseStart_996985 baseEnd_996985 := by
    simpa [prefixWord, tailWord_996985, baseEnd_996985] using wordTrace_append hprefix tailTrace_996985
  have hstable : (prefixWord ++ tailWord_996985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996985).length < 2 ^ (prefixWord ++ tailWord_996985).sum := by decide
  have hdescent : baseEnd_996985 < baseStart_996985 := by decide
  rcases family_descends (prefixWord ++ tailWord_996985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996999 : List Nat := [1, 1, 4, 2, 1, 3, 1, 8]
def baseStart_996999 : Nat := 118140960795 + 996999 * 2 ^ 59
def prefixEnd_996999 : Nat := 4983230072969 + 3 ^ 40 * 996999 * 2
def baseEnd_996999 : Nat := 75842918378081477115169

theorem tailTrace_996999 : CollatzResearch.WordTrace tailWord_996999 prefixEnd_996999 75842918378081477115169 := by
  unfold tailWord_996999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363540915050371718114051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24242360610033581145409367 36363540915050371718114051)
  ·
    refine ⟨54545311372575557577171077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36363540915050371718114051 54545311372575557577171077)
    ·
      refine ⟨10227245882357917045719577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54545311372575557577171077 10227245882357917045719577)
      ·
        refine ⟨7670434411768437784289683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10227245882357917045719577 7670434411768437784289683)
        ·
          refine ⟨11505651617652656676434525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670434411768437784289683 11505651617652656676434525)
          ·
            refine ⟨4314619356619746253662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11505651617652656676434525 4314619356619746253662947)
            ·
              refine ⟨6471929034929619380494421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314619356619746253662947 6471929034929619380494421)
              ·
                refine ⟨75842918378081477115169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6471929034929619380494421 75842918378081477115169)
                ·
                  rfl

theorem cell21_996999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_996999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_996999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_996999 prefixEnd_996999 := by exact prefixLift 996999
  have htrace : WordTrace (prefixWord ++ tailWord_996999) baseStart_996999 baseEnd_996999 := by
    simpa [prefixWord, tailWord_996999, baseEnd_996999] using wordTrace_append hprefix tailTrace_996999
  have hstable : (prefixWord ++ tailWord_996999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996999).length < 2 ^ (prefixWord ++ tailWord_996999).sum := by decide
  have hdescent : baseEnd_996999 < baseStart_996999 := by decide
  rcases family_descends (prefixWord ++ tailWord_996999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997002 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_997002 : Nat := 118140960795 + 997002 * 2 ^ 59
def prefixEnd_997002 : Nat := 4983230072969 + 3 ^ 40 * 997002 * 2
def baseEnd_997002 : Nat := 227529439775117092795501

theorem tailTrace_997002 : CollatzResearch.WordTrace tailWord_997002 prefixEnd_997002 227529439775117092795501 := by
  unfold tailWord_997002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090912583509875807618315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24242433556026335486982173 9090912583509875807618315)
  ·
    refine ⟨13636368875264813711427473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9090912583509875807618315 13636368875264813711427473)
    ·
      refine ⟨10227276656448610283570605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13636368875264813711427473 10227276656448610283570605)
      ·
        refine ⟨3835228746168228856338977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10227276656448610283570605 3835228746168228856338977)
        ·
          refine ⟨2876421559626171642254233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3835228746168228856338977 2876421559626171642254233)
          ·
            refine ⟨2157316169719628731690675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876421559626171642254233 2157316169719628731690675)
            ·
              refine ⟨3235974254579443097536013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157316169719628731690675 3235974254579443097536013)
              ·
                refine ⟨1213490345467291161576005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3235974254579443097536013 1213490345467291161576005)
                ·
                  refine ⟨227529439775117092795501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213490345467291161576005 227529439775117092795501)
                  ·
                    rfl

theorem cell21_997002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_997002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997002 prefixEnd_997002 := by exact prefixLift 997002
  have htrace : WordTrace (prefixWord ++ tailWord_997002) baseStart_997002 baseEnd_997002 := by
    simpa [prefixWord, tailWord_997002, baseEnd_997002] using wordTrace_append hprefix tailTrace_997002
  have hstable : (prefixWord ++ tailWord_997002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997002).length < 2 ^ (prefixWord ++ tailWord_997002).sum := by decide
  have hdescent : baseEnd_997002 < baseStart_997002 := by decide
  rcases family_descends (prefixWord ++ tailWord_997002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997171 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 4]
def baseStart_997171 : Nat := 118140960795 + 997171 * 2 ^ 59
def prefixEnd_997171 : Nat := 4983230072969 + 3 ^ 40 * 997171 * 2
def baseEnd_997171 : Nat := 227568007877610354478489

theorem tailTrace_997171 : CollatzResearch.WordTrace tailWord_997171 prefixEnd_997171 227568007877610354478489 := by
  unfold tailWord_997171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369814270427245093375367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24246542846951496728916911 36369814270427245093375367)
  ·
    refine ⟨54554721405640867640063051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36369814270427245093375367 54554721405640867640063051)
    ·
      refine ⟨81832082108461301460094577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54554721405640867640063051 81832082108461301460094577)
      ·
        refine ⟨61374061581345976095070933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81832082108461301460094577 61374061581345976095070933)
        ·
          refine ⟨1438454568312796314728225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61374061581345976095070933 1438454568312796314728225)
          ·
            refine ⟨1078840926234597236046169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438454568312796314728225 1078840926234597236046169)
            ·
              refine ⟨809130694675947927034627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078840926234597236046169 809130694675947927034627)
              ·
                refine ⟨1213696042013921890551941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809130694675947927034627 1213696042013921890551941)
                ·
                  refine ⟨227568007877610354478489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213696042013921890551941 227568007877610354478489)
                  ·
                    rfl

theorem cell21_997171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_997171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997171 prefixEnd_997171 := by exact prefixLift 997171
  have htrace : WordTrace (prefixWord ++ tailWord_997171) baseStart_997171 baseEnd_997171 := by
    simpa [prefixWord, tailWord_997171, baseEnd_997171] using wordTrace_append hprefix tailTrace_997171
  have hstable : (prefixWord ++ tailWord_997171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997171).length < 2 ^ (prefixWord ++ tailWord_997171).sum := by decide
  have hdescent : baseEnd_997171 < baseStart_997171 := by decide
  rcases family_descends (prefixWord ++ tailWord_997171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997216 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_997216 : Nat := 118140960795 + 997216 * 2 ^ 59
def prefixEnd_997216 : Nat := 4983230072969 + 3 ^ 40 * 997216 * 2
def baseEnd_997216 : Nat := 227578277490700276228397

theorem tailTrace_997216 : CollatzResearch.WordTrace tailWord_997216 prefixEnd_997216 227578277490700276228397 := by
  unfold tailWord_997216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185727777632108889381751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24247637036842811852509001 18185727777632108889381751)
  ·
    refine ⟨27278591666448163334072627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185727777632108889381751 27278591666448163334072627)
    ·
      refine ⟨40917887499672245001108941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27278591666448163334072627 40917887499672245001108941)
      ·
        refine ⟨15344207812377091875415853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40917887499672245001108941 15344207812377091875415853)
        ·
          refine ⟨5754077929641409453280945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15344207812377091875415853 5754077929641409453280945)
          ·
            refine ⟨4315558447231057089960709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5754077929641409453280945 4315558447231057089960709)
            ·
              refine ⟨809167208855823204367633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4315558447231057089960709 809167208855823204367633)
              ·
                refine ⟨606875406641867403275725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809167208855823204367633 606875406641867403275725)
                ·
                  refine ⟨227578277490700276228397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606875406641867403275725 227578277490700276228397)
                  ·
                    rfl

theorem cell21_997216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_997216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997216 prefixEnd_997216 := by exact prefixLift 997216
  have htrace : WordTrace (prefixWord ++ tailWord_997216) baseStart_997216 baseEnd_997216 := by
    simpa [prefixWord, tailWord_997216, baseEnd_997216] using wordTrace_append hprefix tailTrace_997216
  have hstable : (prefixWord ++ tailWord_997216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997216).length < 2 ^ (prefixWord ++ tailWord_997216).sum := by decide
  have hdescent : baseEnd_997216 < baseStart_997216 := by decide
  rcases family_descends (prefixWord ++ tailWord_997216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997230 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_997230 : Nat := 118140960795 + 997230 * 2 ^ 59
def prefixEnd_997230 : Nat := 4983230072969 + 3 ^ 40 * 997230 * 2
def baseEnd_997230 : Nat := 227581472481439362995035

theorem tailTrace_997230 : CollatzResearch.WordTrace tailWord_997230 prefixEnd_997230 227581472481439362995035 := by
  unfold tailWord_997230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546495772151687271221643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24247977451475665446515429 4546495772151687271221643)
  ·
    refine ⟨6819743658227530906832465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546495772151687271221643 6819743658227530906832465)
    ·
      refine ⟨5114807743670648180124349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6819743658227530906832465 5114807743670648180124349)
      ·
        refine ⟨1918052903876493067546631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5114807743670648180124349 1918052903876493067546631)
        ·
          refine ⟨2877079355814739601319947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918052903876493067546631 2877079355814739601319947)
          ·
            refine ⟨4315619033722109401979921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877079355814739601319947 4315619033722109401979921)
            ·
              refine ⟨3236714275291582051484941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315619033722109401979921 3236714275291582051484941)
              ·
                refine ⟨1213767853234343269306853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236714275291582051484941 1213767853234343269306853)
                ·
                  refine ⟨227581472481439362995035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213767853234343269306853 227581472481439362995035)
                  ·
                    rfl

theorem cell21_997230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_997230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997230 prefixEnd_997230 := by exact prefixLift 997230
  have htrace : WordTrace (prefixWord ++ tailWord_997230) baseStart_997230 baseEnd_997230 := by
    simpa [prefixWord, tailWord_997230, baseEnd_997230] using wordTrace_append hprefix tailTrace_997230
  have hstable : (prefixWord ++ tailWord_997230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997230).length < 2 ^ (prefixWord ++ tailWord_997230).sum := by decide
  have hdescent : baseEnd_997230 < baseStart_997230 := by decide
  rcases family_descends (prefixWord ++ tailWord_997230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997340 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_997340 : Nat := 118140960795 + 997340 * 2 ^ 59
def prefixEnd_997340 : Nat := 4983230072969 + 3 ^ 40 * 997340 * 2
def baseEnd_997340 : Nat := 227606575980103616161477

theorem tailTrace_997340 : CollatzResearch.WordTrace tailWord_997340 prefixEnd_997340 227606575980103616161477 := by
  unfold tailWord_997340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187989103407493478138737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24250652137876657970851649 18187989103407493478138737)
  ·
    refine ⟨13640991827555620108604053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18187989103407493478138737 13640991827555620108604053)
    ·
      refine ⟨639421491916669692590815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13640991827555620108604053 639421491916669692590815)
      ·
        refine ⟨959132237875004538886223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639421491916669692590815 959132237875004538886223)
        ·
          refine ⟨1438698356812506808329335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959132237875004538886223 1438698356812506808329335)
          ·
            refine ⟨2158047535218760212494003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438698356812506808329335 2158047535218760212494003)
            ·
              refine ⟨3237071302828140318741005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158047535218760212494003 3237071302828140318741005)
              ·
                refine ⟨1213901738560552619527877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237071302828140318741005 1213901738560552619527877)
                ·
                  refine ⟨227606575980103616161477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213901738560552619527877 227606575980103616161477)
                  ·
                    rfl

theorem cell21_997340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_997340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997340 prefixEnd_997340 := by exact prefixLift 997340
  have htrace : WordTrace (prefixWord ++ tailWord_997340) baseStart_997340 baseEnd_997340 := by
    simpa [prefixWord, tailWord_997340, baseEnd_997340] using wordTrace_append hprefix tailTrace_997340
  have hstable : (prefixWord ++ tailWord_997340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997340).length < 2 ^ (prefixWord ++ tailWord_997340).sum := by decide
  have hdescent : baseEnd_997340 < baseStart_997340 := by decide
  rcases family_descends (prefixWord ++ tailWord_997340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997410 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_997410 : Nat := 118140960795 + 997410 * 2 ^ 59
def prefixEnd_997410 : Nat := 4983230072969 + 3 ^ 40 * 997410 * 2
def baseEnd_997410 : Nat := 227622550933799049994667

theorem tailTrace_997410 : CollatzResearch.WordTrace tailWord_997410 prefixEnd_997410 227622550933799049994667 := by
  unfold tailWord_997410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094632829140347227831421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24252354211040925940883789 9094632829140347227831421)
  ·
    refine ⟨3410487310927630210436783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9094632829140347227831421 3410487310927630210436783)
    ·
      refine ⟨5115730966391445315655175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3410487310927630210436783 5115730966391445315655175)
      ·
        refine ⟨7673596449587167973482763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115730966391445315655175 7673596449587167973482763)
        ·
          refine ⟨11510394674380751960224145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673596449587167973482763 11510394674380751960224145)
          ·
            refine ⟨8632796005785563970168109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11510394674380751960224145 8632796005785563970168109)
            ·
              refine ⟨3237298502169586488813041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632796005785563970168109 3237298502169586488813041)
              ·
                refine ⟨2427973876627189866609781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237298502169586488813041 2427973876627189866609781)
                ·
                  refine ⟨227622550933799049994667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2427973876627189866609781 227622550933799049994667)
                  ·
                    rfl

theorem cell21_997410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_997410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997410 prefixEnd_997410 := by exact prefixLift 997410
  have htrace : WordTrace (prefixWord ++ tailWord_997410) baseStart_997410 baseEnd_997410 := by
    simpa [prefixWord, tailWord_997410, baseEnd_997410] using wordTrace_append hprefix tailTrace_997410
  have hstable : (prefixWord ++ tailWord_997410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997410).length < 2 ^ (prefixWord ++ tailWord_997410).sum := by decide
  have hdescent : baseEnd_997410 < baseStart_997410 := by decide
  rcases family_descends (prefixWord ++ tailWord_997410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997441 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_997441 : Nat := 118140960795 + 997441 * 2 ^ 59
def prefixEnd_997441 : Nat := 4983230072969 + 3 ^ 40 * 997441 * 2
def baseEnd_997441 : Nat := 227629625556149884977937

theorem tailTrace_997441 : CollatzResearch.WordTrace tailWord_997441 prefixEnd_997441 227629625556149884977937 := by
  unfold tailWord_997441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379661979449081205704177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253107986299387470469451 36379661979449081205704177)
  ·
    refine ⟨27284746484586810904278133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36379661979449081205704177 27284746484586810904278133)
    ·
      refine ⟨2557944982930013522276075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27284746484586810904278133 2557944982930013522276075)
      ·
        refine ⟨3836917474395020283414113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557944982930013522276075 3836917474395020283414113)
        ·
          refine ⟨2877688105796265212560585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3836917474395020283414113 2877688105796265212560585)
          ·
            refine ⟨2158266079347198909420439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877688105796265212560585 2158266079347198909420439)
            ·
              refine ⟨3237399119020798364130659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158266079347198909420439 3237399119020798364130659)
              ·
                refine ⟨4856098678531197546195989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237399119020798364130659 4856098678531197546195989)
                ·
                  refine ⟨227629625556149884977937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4856098678531197546195989 227629625556149884977937)
                  ·
                    rfl

theorem cell21_997441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_997441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997441 prefixEnd_997441 := by exact prefixLift 997441
  have htrace : WordTrace (prefixWord ++ tailWord_997441) baseStart_997441 baseEnd_997441 := by
    simpa [prefixWord, tailWord_997441, baseEnd_997441] using wordTrace_append hprefix tailTrace_997441
  have hstable : (prefixWord ++ tailWord_997441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997441).length < 2 ^ (prefixWord ++ tailWord_997441).sum := by decide
  have hdescent : baseEnd_997441 < baseStart_997441 := by decide
  rcases family_descends (prefixWord ++ tailWord_997441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997472 : List Nat := [2, 1, 1, 3, 2, 5, 2, 5]
def baseStart_997472 : Nat := 118140960795 + 997472 * 2 ^ 59
def prefixEnd_997472 : Nat := 4983230072969 + 3 ^ 40 * 997472 * 2
def baseEnd_997472 : Nat := 75878900059500239987069

theorem tailTrace_997472 : CollatzResearch.WordTrace tailWord_997472 prefixEnd_997472 75878900059500239987069 := by
  unfold tailWord_997472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190396321168386750041335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24253861761557849000055113 18190396321168386750041335)
  ·
    refine ⟨27285594481752580125062003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190396321168386750041335 27285594481752580125062003)
    ·
      refine ⟨40928391722628870187593005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27285594481752580125062003 40928391722628870187593005)
      ·
        refine ⟨15348146895985826320347377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40928391722628870187593005 15348146895985826320347377)
        ·
          refine ⟨11511110171989369740260533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15348146895985826320347377 11511110171989369740260533)
          ·
            refine ⟨1079166578624003413149425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11511110171989369740260533 1079166578624003413149425)
            ·
              refine ⟨809374933968002559862069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079166578624003413149425 809374933968002559862069)
              ·
                refine ⟨75878900059500239987069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809374933968002559862069 75878900059500239987069)
                ·
                  rfl

theorem cell21_997472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_997472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997472 prefixEnd_997472 := by exact prefixLift 997472
  have htrace : WordTrace (prefixWord ++ tailWord_997472) baseStart_997472 baseEnd_997472 := by
    simpa [prefixWord, tailWord_997472, baseEnd_997472] using wordTrace_append hprefix tailTrace_997472
  have hstable : (prefixWord ++ tailWord_997472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997472).length < 2 ^ (prefixWord ++ tailWord_997472).sum := by decide
  have hdescent : baseEnd_997472 < baseStart_997472 := by decide
  rcases family_descends (prefixWord ++ tailWord_997472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997500 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_997500 : Nat := 118140960795 + 997500 * 2 ^ 59
def prefixEnd_997500 : Nat := 4983230072969 + 3 ^ 40 * 997500 * 2
def baseEnd_997500 : Nat := 227643090159978893494483

theorem tailTrace_997500 : CollatzResearch.WordTrace tailWord_997500 prefixEnd_997500 227643090159978893494483 := by
  unfold tailWord_997500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190906943117667141050977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24254542590823556188067969 18190906943117667141050977)
  ·
    refine ⟨13643180207338250355788233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18190906943117667141050977 13643180207338250355788233)
    ·
      refine ⟨10232385155503687766841175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13643180207338250355788233 10232385155503687766841175)
      ·
        refine ⟨15348577733255531650261763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232385155503687766841175 15348577733255531650261763)
        ·
          refine ⟨23022866599883297475392645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348577733255531650261763 23022866599883297475392645)
          ·
            refine ⟨4316787487478118276636121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23022866599883297475392645 4316787487478118276636121)
            ·
              refine ⟨3237590615608588707477091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316787487478118276636121 3237590615608588707477091)
              ·
                refine ⟨4856385923412883061215637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237590615608588707477091 4856385923412883061215637)
                ·
                  refine ⟨227643090159978893494483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4856385923412883061215637 227643090159978893494483)
                  ·
                    rfl

theorem cell21_997500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_997500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997500 prefixEnd_997500 := by exact prefixLift 997500
  have htrace : WordTrace (prefixWord ++ tailWord_997500) baseStart_997500 baseEnd_997500 := by
    simpa [prefixWord, tailWord_997500, baseEnd_997500] using wordTrace_append hprefix tailTrace_997500
  have hstable : (prefixWord ++ tailWord_997500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997500).length < 2 ^ (prefixWord ++ tailWord_997500).sum := by decide
  have hdescent : baseEnd_997500 < baseStart_997500 := by decide
  rcases family_descends (prefixWord ++ tailWord_997500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997607 : List Nat := [1, 1, 5, 3, 1, 2, 8]
def baseStart_997607 : Nat := 118140960795 + 997607 * 2 ^ 59
def prefixEnd_997607 : Nat := 4983230072969 + 3 ^ 40 * 997607 * 2
def baseEnd_997607 : Nat := 25296389890863387245659

theorem tailTrace_997607 : CollatzResearch.WordTrace tailWord_997607 prefixEnd_997607 25296389890863387245659 := by
  unfold tailWord_997607
  simp only [CollatzResearch.WordTrace]
  refine ⟨36385716496847691556247075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24257144331231794370831383 36385716496847691556247075)
  ·
    refine ⟨54578574745271537334370613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36385716496847691556247075 54578574745271537334370613)
    ·
      refine ⟨5116741382369206625097245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54578574745271537334370613 5116741382369206625097245)
      ·
        refine ⟨1918778018388452484411467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5116741382369206625097245 1918778018388452484411467)
        ·
          refine ⟨2878167027582678726617201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918778018388452484411467 2878167027582678726617201)
          ·
            refine ⟨2158625270687009044962901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878167027582678726617201 2158625270687009044962901)
            ·
              refine ⟨25296389890863387245659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2158625270687009044962901 25296389890863387245659)
              ·
                rfl

theorem cell21_997607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_997607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997607 prefixEnd_997607 := by exact prefixLift 997607
  have htrace : WordTrace (prefixWord ++ tailWord_997607) baseStart_997607 baseEnd_997607 := by
    simpa [prefixWord, tailWord_997607, baseEnd_997607] using wordTrace_append hprefix tailTrace_997607
  have hstable : (prefixWord ++ tailWord_997607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997607).length < 2 ^ (prefixWord ++ tailWord_997607).sum := by decide
  have hdescent : baseEnd_997607 < baseStart_997607 := by decide
  rcases family_descends (prefixWord ++ tailWord_997607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997655 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 3]
def baseStart_997655 : Nat := 118140960795 + 997655 * 2 ^ 59
def prefixEnd_997655 : Nat := 4983230072969 + 3 ^ 40 * 997655 * 2
def baseEnd_997655 : Nat := 227678463271733068410833

theorem tailTrace_997655 : CollatzResearch.WordTrace tailWord_997655 prefixEnd_997655 227678463271733068410833 := by
  unfold tailWord_997655
  simp only [CollatzResearch.WordTrace]
  refine ⟨36387467200673795753994419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24258311467115863835996279 36387467200673795753994419)
  ·
    refine ⟨54581200801010693630991629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36387467200673795753994419 54581200801010693630991629)
    ·
      refine ⟨20467950300379010111621861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54581200801010693630991629 20467950300379010111621861)
      ·
        refine ⟨3837740681321064395929099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20467950300379010111621861 3837740681321064395929099)
        ·
          refine ⟨5756611021981596593893649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837740681321064395929099 5756611021981596593893649)
          ·
            refine ⟨4317458266486197445420237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756611021981596593893649 4317458266486197445420237)
            ·
              refine ⟨1619046849932324042032589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4317458266486197445420237 1619046849932324042032589)
              ·
                refine ⟨607142568724621515762221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619046849932324042032589 607142568724621515762221)
                ·
                  refine ⟨227678463271733068410833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607142568724621515762221 227678463271733068410833)
                  ·
                    rfl

theorem cell21_997655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].length) (baseStart_997655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997655 prefixEnd_997655 := by exact prefixLift 997655
  have htrace : WordTrace (prefixWord ++ tailWord_997655) baseStart_997655 baseEnd_997655 := by
    simpa [prefixWord, tailWord_997655, baseEnd_997655] using wordTrace_append hprefix tailTrace_997655
  have hstable : (prefixWord ++ tailWord_997655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997655).length < 2 ^ (prefixWord ++ tailWord_997655).sum := by decide
  have hdescent : baseEnd_997655 < baseStart_997655 := by decide
  rcases family_descends (prefixWord ++ tailWord_997655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997672 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_997672 : Nat := 118140960795 + 997672 * 2 ^ 59
def prefixEnd_997672 : Nat := 4983230072969 + 3 ^ 40 * 997672 * 2
def baseEnd_997672 : Nat := 227682342903344816627465

theorem tailTrace_997672 : CollatzResearch.WordTrace tailWord_997672 prefixEnd_997672 227682342903344816627465 := by
  unfold tailWord_997672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194043620806103828681635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24258724827741471771575513 18194043620806103828681635)
  ·
    refine ⟨27291065431209155743022453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18194043620806103828681635 27291065431209155743022453)
    ·
      refine ⟨2558537384175858350908355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27291065431209155743022453 2558537384175858350908355)
      ·
        refine ⟨3837806076263787526362533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558537384175858350908355 3837806076263787526362533)
        ·
          refine ⟨719588639299460161192975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3837806076263787526362533 719588639299460161192975)
          ·
            refine ⟨1079382958949190241789463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719588639299460161192975 1079382958949190241789463)
            ·
              refine ⟨1619074438423785362684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079382958949190241789463 1619074438423785362684195)
              ·
                refine ⟨2428611657635678044026293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619074438423785362684195 2428611657635678044026293)
                ·
                  refine ⟨227682342903344816627465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2428611657635678044026293 227682342903344816627465)
                  ·
                    rfl

theorem cell21_997672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_997672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997672 prefixEnd_997672 := by exact prefixLift 997672
  have htrace : WordTrace (prefixWord ++ tailWord_997672) baseStart_997672 baseEnd_997672 := by
    simpa [prefixWord, tailWord_997672, baseEnd_997672] using wordTrace_append hprefix tailTrace_997672
  have hstable : (prefixWord ++ tailWord_997672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997672).length < 2 ^ (prefixWord ++ tailWord_997672).sum := by decide
  have hdescent : baseEnd_997672 < baseStart_997672 := by decide
  rcases family_descends (prefixWord ++ tailWord_997672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997711 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_997711 : Nat := 118140960795 + 997711 * 2 ^ 59
def prefixEnd_997711 : Nat := 4983230072969 + 3 ^ 40 * 997711 * 2
def baseEnd_997711 : Nat := 227691243234689415477385

theorem tailTrace_997711 : CollatzResearch.WordTrace tailWord_997711 prefixEnd_997711 227691243234689415477385 := by
  unfold tailWord_997711
  simp only [CollatzResearch.WordTrace]
  refine ⟨36389509688470917318032987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24259673125647278212021991 36389509688470917318032987)
  ·
    refine ⟨54584264532706375977049481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36389509688470917318032987 54584264532706375977049481)
    ·
      refine ⟨40938198399529781982787111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54584264532706375977049481 40938198399529781982787111)
      ·
        refine ⟨61407297599294672974180667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40938198399529781982787111 61407297599294672974180667)
        ·
          refine ⟨92110946398942009461271001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61407297599294672974180667 92110946398942009461271001)
          ·
            refine ⟨69083209799206507095953251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92110946398942009461271001 69083209799206507095953251)
            ·
              refine ⟨103624814698809760643929877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69083209799206507095953251 103624814698809760643929877)
              ·
                refine ⟨4857413189006707530184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103624814698809760643929877 4857413189006707530184213)
                ·
                  refine ⟨227691243234689415477385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4857413189006707530184213 227691243234689415477385)
                  ·
                    rfl

theorem cell21_997711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_997711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997711 prefixEnd_997711 := by exact prefixLift 997711
  have htrace : WordTrace (prefixWord ++ tailWord_997711) baseStart_997711 baseEnd_997711 := by
    simpa [prefixWord, tailWord_997711, baseEnd_997711] using wordTrace_append hprefix tailTrace_997711
  have hstable : (prefixWord ++ tailWord_997711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997711).length < 2 ^ (prefixWord ++ tailWord_997711).sum := by decide
  have hdescent : baseEnd_997711 < baseStart_997711 := by decide
  rcases family_descends (prefixWord ++ tailWord_997711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997900 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_997900 : Nat := 118140960795 + 997900 * 2 ^ 59
def prefixEnd_997900 : Nat := 4983230072969 + 3 ^ 40 * 997900 * 2
def baseEnd_997900 : Nat := 227734375609667086826999

theorem tailTrace_997900 : CollatzResearch.WordTrace tailWord_997900 prefixEnd_997900 227734375609667086826999 := by
  unfold tailWord_997900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198201542393101298331577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24264268723190801731108769 18198201542393101298331577)
  ·
    refine ⟨13648651156794825973748683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18198201542393101298331577 13648651156794825973748683)
    ·
      refine ⟨20472976735192238960623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648651156794825973748683 20472976735192238960623025)
      ·
        refine ⟨15354732551394179220467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20472976735192238960623025 15354732551394179220467269)
        ·
          refine ⟨2879012353386408603837613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15354732551394179220467269 2879012353386408603837613)
          ·
            refine ⟨1079629632519903226439105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2879012353386408603837613 1079629632519903226439105)
            ·
              refine ⟨809722224389927419829329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079629632519903226439105 809722224389927419829329)
              ·
                refine ⟨607291668292445564871997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809722224389927419829329 607291668292445564871997)
                ·
                  refine ⟨227734375609667086826999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607291668292445564871997 227734375609667086826999)
                  ·
                    rfl

theorem cell21_997900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_997900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997900 prefixEnd_997900 := by exact prefixLift 997900
  have htrace : WordTrace (prefixWord ++ tailWord_997900) baseStart_997900 baseEnd_997900 := by
    simpa [prefixWord, tailWord_997900, baseEnd_997900] using wordTrace_append hprefix tailTrace_997900
  have hstable : (prefixWord ++ tailWord_997900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997900).length < 2 ^ (prefixWord ++ tailWord_997900).sum := by decide
  have hdescent : baseEnd_997900 < baseStart_997900 := by decide
  rcases family_descends (prefixWord ++ tailWord_997900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997928 : List Nat := [2, 1, 5, 2, 1, 2, 3, 5]
def baseStart_997928 : Nat := 118140960795 + 997928 * 2 ^ 59
def prefixEnd_997928 : Nat := 4983230072969 + 3 ^ 40 * 997928 * 2
def baseEnd_997928 : Nat := 75913588530381753453425

theorem tailTrace_997928 : CollatzResearch.WordTrace tailWord_997928 prefixEnd_997928 75913588530381753453425 := by
  unfold tailWord_997928
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198712164342381689341219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24264949552456508919121625 18198712164342381689341219)
  ·
    refine ⟨27298068246513572534011829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18198712164342381689341219 27298068246513572534011829)
    ·
      refine ⟨2559193898110647425063609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27298068246513572534011829 2559193898110647425063609)
      ·
        refine ⟨1919395423582985568797707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2559193898110647425063609 1919395423582985568797707)
        ·
          refine ⟨2879093135374478353196561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919395423582985568797707 2879093135374478353196561)
          ·
            refine ⟨2159319851530858764897421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879093135374478353196561 2159319851530858764897421)
            ·
              refine ⟨809744944324072036836533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2159319851530858764897421 809744944324072036836533)
              ·
                refine ⟨75913588530381753453425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809744944324072036836533 75913588530381753453425)
                ·
                  rfl

theorem cell21_997928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_997928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997928 prefixEnd_997928 := by exact prefixLift 997928
  have htrace : WordTrace (prefixWord ++ tailWord_997928) baseStart_997928 baseEnd_997928 := by
    simpa [prefixWord, tailWord_997928, baseEnd_997928] using wordTrace_append hprefix tailTrace_997928
  have hstable : (prefixWord ++ tailWord_997928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997928).length < 2 ^ (prefixWord ++ tailWord_997928).sum := by decide
  have hdescent : baseEnd_997928 < baseStart_997928 := by decide
  rcases family_descends (prefixWord ++ tailWord_997928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997939 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_997939 : Nat := 118140960795 + 997939 * 2 ^ 59
def prefixEnd_997939 : Nat := 4983230072969 + 3 ^ 40 * 997939 * 2
def baseEnd_997939 : Nat := 227743275941011685676919

theorem tailTrace_997939 : CollatzResearch.WordTrace tailWord_997939 prefixEnd_997939 227743275941011685676919 := by
  unfold tailWord_997939
  simp only [CollatzResearch.WordTrace]
  refine ⟨36397825531644912257332871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24265217021096608171555247 36397825531644912257332871)
  ·
    refine ⟨54596738297467368385999307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36397825531644912257332871 54596738297467368385999307)
    ·
      refine ⟨81895107446201052578998961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54596738297467368385999307 81895107446201052578998961)
      ·
        refine ⟨61421330584650789434249221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81895107446201052578998961 61421330584650789434249221)
        ·
          refine ⟨11516499484622023018921729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61421330584650789434249221 11516499484622023018921729)
          ·
            refine ⟨8637374613466517264191297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11516499484622023018921729 8637374613466517264191297)
            ·
              refine ⟨6478030960099887948143473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637374613466517264191297 6478030960099887948143473)
              ·
                refine ⟨4858523220074915961107605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478030960099887948143473 4858523220074915961107605)
                ·
                  refine ⟨227743275941011685676919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4858523220074915961107605 227743275941011685676919)
                  ·
                    rfl

theorem cell21_997939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_997939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997939 prefixEnd_997939 := by exact prefixLift 997939
  have htrace : WordTrace (prefixWord ++ tailWord_997939) baseStart_997939 baseEnd_997939 := by
    simpa [prefixWord, tailWord_997939, baseEnd_997939] using wordTrace_append hprefix tailTrace_997939
  have hstable : (prefixWord ++ tailWord_997939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997939).length < 2 ^ (prefixWord ++ tailWord_997939).sum := by decide
  have hdescent : baseEnd_997939 < baseStart_997939 := by decide
  rcases family_descends (prefixWord ++ tailWord_997939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997970 : List Nat := [3, 2, 2, 1, 2, 1, 2, 8]
def baseStart_997970 : Nat := 118140960795 + 997970 * 2 ^ 59
def prefixEnd_997970 : Nat := 4983230072969 + 3 ^ 40 * 997970 * 2
def baseEnd_997970 : Nat := 75916783521120840220063

theorem tailTrace_997970 : CollatzResearch.WordTrace tailWord_997970 prefixEnd_997970 75916783521120840220063 := by
  unfold tailWord_997970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099739048633151137927841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24265970796355069701140909 9099739048633151137927841)
  ·
    refine ⟨6824804286474863353445881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9099739048633151137927841 6824804286474863353445881)
    ·
      refine ⟨5118603214856147515084411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6824804286474863353445881 5118603214856147515084411)
      ·
        refine ⟨7677904822284221272626617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118603214856147515084411 7677904822284221272626617)
        ·
          refine ⟨5758428616713165954469963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7677904822284221272626617 5758428616713165954469963)
          ·
            refine ⟨8637642925069748931704945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758428616713165954469963 8637642925069748931704945)
            ·
              refine ⟨6478232193802311698778709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637642925069748931704945 6478232193802311698778709)
              ·
                refine ⟨75916783521120840220063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6478232193802311698778709 75916783521120840220063)
                ·
                  rfl

theorem cell21_997970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_997970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_997970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_997970 prefixEnd_997970 := by exact prefixLift 997970
  have htrace : WordTrace (prefixWord ++ tailWord_997970) baseStart_997970 baseEnd_997970 := by
    simpa [prefixWord, tailWord_997970, baseEnd_997970] using wordTrace_append hprefix tailTrace_997970
  have hstable : (prefixWord ++ tailWord_997970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997970).length < 2 ^ (prefixWord ++ tailWord_997970).sum := by decide
  have hdescent : baseEnd_997970 < baseStart_997970 := by decide
  rcases family_descends (prefixWord ++ tailWord_997970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998142 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_998142 : Nat := 118140960795 + 998142 * 2 ^ 59
def prefixEnd_998142 : Nat := 4983230072969 + 3 ^ 40 * 998142 * 2
def baseEnd_998142 : Nat := 227789603306728443793171

theorem tailTrace_998142 : CollatzResearch.WordTrace tailWord_998142 prefixEnd_998142 227789603306728443793171 := by
  unfold tailWord_998142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550653693738684740871585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24270153033272985284648453 4550653693738684740871585)
  ·
    refine ⟨3412990270304013555653689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4550653693738684740871585 3412990270304013555653689)
    ·
      refine ⟨2559742702728010166740267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3412990270304013555653689 2559742702728010166740267)
      ·
        refine ⟨3839614054092015250110401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559742702728010166740267 3839614054092015250110401)
        ·
          refine ⟨2879710540569011437582801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839614054092015250110401 2879710540569011437582801)
          ·
            refine ⟨2159782905426758578187101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879710540569011437582801 2159782905426758578187101)
            ·
              refine ⟨809918589535034466820163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2159782905426758578187101 809918589535034466820163)
              ·
                refine ⟨1214877884302551700230245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809918589535034466820163 1214877884302551700230245)
                ·
                  refine ⟨227789603306728443793171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214877884302551700230245 227789603306728443793171)
                  ·
                    rfl

theorem cell21_998142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_998142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998142 prefixEnd_998142 := by exact prefixLift 998142
  have htrace : WordTrace (prefixWord ++ tailWord_998142) baseStart_998142 baseEnd_998142 := by
    simpa [prefixWord, tailWord_998142, baseEnd_998142] using wordTrace_append hprefix tailTrace_998142
  have hstable : (prefixWord ++ tailWord_998142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998142).length < 2 ^ (prefixWord ++ tailWord_998142).sum := by decide
  have hdescent : baseEnd_998142 < baseStart_998142 := by decide
  rcases family_descends (prefixWord ++ tailWord_998142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998184 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_998184 : Nat := 118140960795 + 998184 * 2 ^ 59
def prefixEnd_998184 : Nat := 4983230072969 + 3 ^ 40 * 998184 * 2
def baseEnd_998184 : Nat := 227799188278945704093085

theorem tailTrace_998184 : CollatzResearch.WordTrace tailWord_998184 prefixEnd_998184 227799188278945704093085 := by
  unfold tailWord_998184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203380707878659550000803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24271174277171546066667737 18203380707878659550000803)
  ·
    refine ⟨27305071061817989325001205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18203380707878659550000803 27305071061817989325001205)
    ·
      refine ⟨2559850412045436499218863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27305071061817989325001205 2559850412045436499218863)
      ·
        refine ⟨3839775618068154748828295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559850412045436499218863 3839775618068154748828295)
        ·
          refine ⟨5759663427102232123242443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839775618068154748828295 5759663427102232123242443)
          ·
            refine ⟨8639495140653348184863665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759663427102232123242443 8639495140653348184863665)
            ·
              refine ⟨6479621355490011138647749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639495140653348184863665 6479621355490011138647749)
              ·
                refine ⟨1214929004154377088496453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6479621355490011138647749 1214929004154377088496453)
                ·
                  refine ⟨227799188278945704093085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214929004154377088496453 227799188278945704093085)
                  ·
                    rfl

theorem cell21_998184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_998184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998184 prefixEnd_998184 := by exact prefixLift 998184
  have htrace : WordTrace (prefixWord ++ tailWord_998184) baseStart_998184 baseEnd_998184 := by
    simpa [prefixWord, tailWord_998184, baseEnd_998184] using wordTrace_append hprefix tailTrace_998184
  have hstable : (prefixWord ++ tailWord_998184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998184).length < 2 ^ (prefixWord ++ tailWord_998184).sum := by decide
  have hdescent : baseEnd_998184 < baseStart_998184 := by decide
  rcases family_descends (prefixWord ++ tailWord_998184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998294 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_998294 : Nat := 118140960795 + 998294 * 2 ^ 59
def prefixEnd_998294 : Nat := 4983230072969 + 3 ^ 40 * 998294 * 2
def baseEnd_998294 : Nat := 227824291777609957259527

theorem tailTrace_998294 : CollatzResearch.WordTrace tailWord_998294 prefixEnd_998294 227824291777609957259527 := by
  unfold tailWord_998294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275673340334925492906621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24273848963572538591003957 2275673340334925492906621)
  ·
    refine ⟨853377502625597059839983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2275673340334925492906621 853377502625597059839983)
    ·
      refine ⟨1280066253938395589759975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853377502625597059839983 1280066253938395589759975)
      ·
        refine ⟨1920099380907593384639963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280066253938395589759975 1920099380907593384639963)
        ·
          refine ⟨2880149071361390076959945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920099380907593384639963 2880149071361390076959945)
          ·
            refine ⟨2160111803521042557719959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880149071361390076959945 2160111803521042557719959)
            ·
              refine ⟨3240167705281563836579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160111803521042557719959 3240167705281563836579939)
              ·
                refine ⟨4860251557922345754869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240167705281563836579939 4860251557922345754869909)
                ·
                  refine ⟨227824291777609957259527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860251557922345754869909 227824291777609957259527)
                  ·
                    rfl

theorem cell21_998294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_998294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998294 prefixEnd_998294 := by exact prefixLift 998294
  have htrace : WordTrace (prefixWord ++ tailWord_998294) baseStart_998294 baseEnd_998294 := by
    simpa [prefixWord, tailWord_998294, baseEnd_998294] using wordTrace_append hprefix tailTrace_998294
  have hstable : (prefixWord ++ tailWord_998294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998294).length < 2 ^ (prefixWord ++ tailWord_998294).sum := by decide
  have hdescent : baseEnd_998294 < baseStart_998294 := by decide
  rcases family_descends (prefixWord ++ tailWord_998294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998305 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_998305 : Nat := 118140960795 + 998305 * 2 ^ 59
def prefixEnd_998305 : Nat := 4983230072969 + 3 ^ 40 * 998305 * 2
def baseEnd_998305 : Nat := 227826802127476382576171

theorem tailTrace_998305 : CollatzResearch.WordTrace tailWord_998305 prefixEnd_998305 227826802127476382576171 := by
  unfold tailWord_998305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411174648318956765156369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274116432212637843437579 36411174648318956765156369)
  ·
    refine ⟨27308380986239217573867277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36411174648318956765156369 27308380986239217573867277)
    ·
      refine ⟨10240642869839706590200229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27308380986239217573867277 10240642869839706590200229)
      ·
        refine ⟨1920120538094944985662543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10240642869839706590200229 1920120538094944985662543)
        ·
          refine ⟨2880180807142417478493815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920120538094944985662543 2880180807142417478493815)
          ·
            refine ⟨4320271210713626217740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880180807142417478493815 4320271210713626217740723)
            ·
              refine ⟨6480406816070439326611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320271210713626217740723 6480406816070439326611085)
              ·
                refine ⟨2430152556026414747479157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480406816070439326611085 2430152556026414747479157)
                ·
                  refine ⟨227826802127476382576171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2430152556026414747479157 227826802127476382576171)
                  ·
                    rfl

theorem cell21_998305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_998305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998305 prefixEnd_998305 := by exact prefixLift 998305
  have htrace : WordTrace (prefixWord ++ tailWord_998305) baseStart_998305 baseEnd_998305 := by
    simpa [prefixWord, tailWord_998305, baseEnd_998305] using wordTrace_append hprefix tailTrace_998305
  have hstable : (prefixWord ++ tailWord_998305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998305).length < 2 ^ (prefixWord ++ tailWord_998305).sum := by decide
  have hdescent : baseEnd_998305 < baseStart_998305 := by decide
  rcases family_descends (prefixWord ++ tailWord_998305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998342 : List Nat := [6, 1, 3, 1, 1, 2, 7]
def baseStart_998342 : Nat := 118140960795 + 998342 * 2 ^ 59
def prefixEnd_998342 : Nat := 4983230072969 + 3 ^ 40 * 998342 * 2
def baseEnd_998342 : Nat := 25315027336841393384381

theorem tailTrace_998342 : CollatzResearch.WordTrace tailWord_998342 prefixEnd_998342 25315027336841393384381 := by
  unfold tailWord_998342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137891379662028502632915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24275016099456608056168853 1137891379662028502632915)
  ·
    refine ⟨1706837069493042753949373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1137891379662028502632915 1706837069493042753949373)
    ·
      refine ⟨640063901059891032731015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1706837069493042753949373 640063901059891032731015)
      ·
        refine ⟨960095851589836549096523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640063901059891032731015 960095851589836549096523)
        ·
          refine ⟨1440143777384754823644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960095851589836549096523 1440143777384754823644785)
          ·
            refine ⟨1080107833038566117733589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440143777384754823644785 1080107833038566117733589)
            ·
              refine ⟨25315027336841393384381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1080107833038566117733589 25315027336841393384381)
              ·
                rfl

theorem cell21_998342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 7].length) (baseStart_998342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998342 prefixEnd_998342 := by exact prefixLift 998342
  have htrace : WordTrace (prefixWord ++ tailWord_998342) baseStart_998342 baseEnd_998342 := by
    simpa [prefixWord, tailWord_998342, baseEnd_998342] using wordTrace_append hprefix tailTrace_998342
  have hstable : (prefixWord ++ tailWord_998342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998342).length < 2 ^ (prefixWord ++ tailWord_998342).sum := by decide
  have hdescent : baseEnd_998342 < baseStart_998342 := by decide
  rcases family_descends (prefixWord ++ tailWord_998342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998350 : List Nat := [4, 1, 1, 1, 2, 5, 7]
def baseStart_998350 : Nat := 118140960795 + 998350 * 2 ^ 59
def prefixEnd_998350 : Nat := 4983230072969 + 3 ^ 40 * 998350 * 2
def baseEnd_998350 : Nat := 25315230193396256036231

theorem tailTrace_998350 : CollatzResearch.WordTrace tailWord_998350 prefixEnd_998350 25315230193396256036231 := by
  unfold tailWord_998350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551601991644491181318063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24275210622103952967029669 4551601991644491181318063)
  ·
    refine ⟨6827402987466736771977095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551601991644491181318063 6827402987466736771977095)
    ·
      refine ⟨10241104481200105157965643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6827402987466736771977095 10241104481200105157965643)
      ·
        refine ⟨15361656721800157736948465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241104481200105157965643 15361656721800157736948465)
        ·
          refine ⟨11521242541350118302711349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15361656721800157736948465 11521242541350118302711349)
          ·
            refine ⟨1080116488251573590879189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11521242541350118302711349 1080116488251573590879189)
            ·
              refine ⟨25315230193396256036231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1080116488251573590879189 25315230193396256036231)
              ·
                rfl

theorem cell21_998350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 7].length) (baseStart_998350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998350 prefixEnd_998350 := by exact prefixLift 998350
  have htrace : WordTrace (prefixWord ++ tailWord_998350) baseStart_998350 baseEnd_998350 := by
    simpa [prefixWord, tailWord_998350, baseEnd_998350] using wordTrace_append hprefix tailTrace_998350
  have hstable : (prefixWord ++ tailWord_998350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998350).length < 2 ^ (prefixWord ++ tailWord_998350).sum := by decide
  have hdescent : baseEnd_998350 < baseStart_998350 := by decide
  rcases family_descends (prefixWord ++ tailWord_998350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998370 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_998370 : Nat := 118140960795 + 998370 * 2 ^ 59
def prefixEnd_998370 : Nat := 4983230072969 + 3 ^ 40 * 998370 * 2
def baseEnd_998370 : Nat := 227841636013050713992705

theorem tailTrace_998370 : CollatzResearch.WordTrace tailWord_998370 prefixEnd_998370 227841636013050713992705 := by
  unfold tailWord_998370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103386348270868216568141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24275696928722315244181709 9103386348270868216568141)
  ·
    refine ⟨3413769880601575581213053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9103386348270868216568141 3413769880601575581213053)
    ·
      refine ⟨1280163705225590842954895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3413769880601575581213053 1280163705225590842954895)
      ·
        refine ⟨1920245557838386264432343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280163705225590842954895 1920245557838386264432343)
        ·
          refine ⟨2880368336757579396648515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920245557838386264432343 2880368336757579396648515)
          ·
            refine ⟨4320552505136369094972773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880368336757579396648515 4320552505136369094972773)
            ·
              refine ⟨810103594713069205307395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4320552505136369094972773 810103594713069205307395)
              ·
                refine ⟨1215155392069603807961093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810103594713069205307395 1215155392069603807961093)
                ·
                  refine ⟨227841636013050713992705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215155392069603807961093 227841636013050713992705)
                  ·
                    rfl

theorem cell21_998370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_998370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998370 prefixEnd_998370 := by exact prefixLift 998370
  have htrace : WordTrace (prefixWord ++ tailWord_998370) baseStart_998370 baseEnd_998370 := by
    simpa [prefixWord, tailWord_998370, baseEnd_998370] using wordTrace_append hprefix tailTrace_998370
  have hstable : (prefixWord ++ tailWord_998370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998370).length < 2 ^ (prefixWord ++ tailWord_998370).sum := by decide
  have hdescent : baseEnd_998370 < baseStart_998370 := by decide
  rcases family_descends (prefixWord ++ tailWord_998370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998412 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_998412 : Nat := 118140960795 + 998412 * 2 ^ 59
def prefixEnd_998412 : Nat := 4983230072969 + 3 ^ 40 * 998412 * 2
def baseEnd_998412 : Nat := 227851220985267974292619

theorem tailTrace_998412 : CollatzResearch.WordTrace tailWord_998412 prefixEnd_998412 227851220985267974292619 := by
  unfold tailWord_998412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18207538629465657019650745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24276718172620876026200993 18207538629465657019650745)
  ·
    refine ⟨13655653972099242764738059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18207538629465657019650745 13655653972099242764738059)
    ·
      refine ⟨20483480958148864147107089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13655653972099242764738059 20483480958148864147107089)
      ·
        refine ⟨15362610718611648110330317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20483480958148864147107089 15362610718611648110330317)
        ·
          refine ⟨5760979019479368041373869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15362610718611648110330317 5760979019479368041373869)
          ·
            refine ⟨2160367132304763015515201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5760979019479368041373869 2160367132304763015515201)
            ·
              refine ⟨1620275349228572261636401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160367132304763015515201 1620275349228572261636401)
              ·
                refine ⟨1215206511921429196227301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620275349228572261636401 1215206511921429196227301)
                ·
                  refine ⟨227851220985267974292619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215206511921429196227301 227851220985267974292619)
                  ·
                    rfl

theorem cell21_998412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_998412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998412 prefixEnd_998412 := by exact prefixLift 998412
  have htrace : WordTrace (prefixWord ++ tailWord_998412) baseStart_998412 baseEnd_998412 := by
    simpa [prefixWord, tailWord_998412, baseEnd_998412] using wordTrace_append hprefix tailTrace_998412
  have hstable : (prefixWord ++ tailWord_998412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998412).length < 2 ^ (prefixWord ++ tailWord_998412).sum := by decide
  have hdescent : baseEnd_998412 < baseStart_998412 := by decide
  rcases family_descends (prefixWord ++ tailWord_998412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998418 : List Nat := [3, 2, 5, 1, 2, 1, 1, 6]
def baseStart_998418 : Nat := 118140960795 + 998418 * 2 ^ 59
def prefixEnd_998418 : Nat := 4983230072969 + 3 ^ 40 * 998418 * 2
def baseEnd_998418 : Nat := 75950863422337765730869

theorem tailTrace_998418 : CollatzResearch.WordTrace tailWord_998418 prefixEnd_998418 75950863422337765730869 := by
  unfold tailWord_998418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103824024227394266004977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24276864064606384709346605 9103824024227394266004977)
  ·
    refine ⟨6827868018170545699503733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9103824024227394266004977 6827868018170545699503733)
    ·
      refine ⟨640112626703488659328475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6827868018170545699503733 640112626703488659328475)
      ·
        refine ⟨960168940055232988992713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640112626703488659328475 960168940055232988992713)
        ·
          refine ⟨720126705041424741744535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960168940055232988992713 720126705041424741744535)
          ·
            refine ⟨1080190057562137112616803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720126705041424741744535 1080190057562137112616803)
            ·
              refine ⟨1620285086343205668925205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080190057562137112616803 1620285086343205668925205)
              ·
                refine ⟨75950863422337765730869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1620285086343205668925205 75950863422337765730869)
                ·
                  rfl

theorem cell21_998418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_998418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998418 prefixEnd_998418 := by exact prefixLift 998418
  have htrace : WordTrace (prefixWord ++ tailWord_998418) baseStart_998418 baseEnd_998418 := by
    simpa [prefixWord, tailWord_998418, baseEnd_998418] using wordTrace_append hprefix tailTrace_998418
  have hstable : (prefixWord ++ tailWord_998418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998418).length < 2 ^ (prefixWord ++ tailWord_998418).sum := by decide
  have hdescent : baseEnd_998418 < baseStart_998418 := by decide
  rcases family_descends (prefixWord ++ tailWord_998418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998471 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_998471 : Nat := 118140960795 + 998471 * 2 ^ 59
def prefixEnd_998471 : Nat := 4983230072969 + 3 ^ 40 * 998471 * 2
def baseEnd_998471 : Nat := 227864685589096982809165

theorem tailTrace_998471 : CollatzResearch.WordTrace tailWord_998471 prefixEnd_998471 227864685589096982809165 := by
  unfold tailWord_998471
  simp only [CollatzResearch.WordTrace]
  refine ⟨36417229165717567115699267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24278152777145044743799511 36417229165717567115699267)
  ·
    refine ⟨54625843748576350673548901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36417229165717567115699267 54625843748576350673548901)
    ·
      refine ⟨10242345702858065751290419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54625843748576350673548901 10242345702858065751290419)
      ·
        refine ⟨15363518554287098626935629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242345702858065751290419 15363518554287098626935629)
        ·
          refine ⟨5761319457857661985100861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15363518554287098626935629 5761319457857661985100861)
          ·
            refine ⟨2160494796696623244412823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5761319457857661985100861 2160494796696623244412823)
            ·
              refine ⟨3240742195044934866619235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160494796696623244412823 3240742195044934866619235)
              ·
                refine ⟨4861113292567402299928853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240742195044934866619235 4861113292567402299928853)
                ·
                  refine ⟨227864685589096982809165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4861113292567402299928853 227864685589096982809165)
                  ·
                    rfl

theorem cell21_998471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_998471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998471 prefixEnd_998471 := by exact prefixLift 998471
  have htrace : WordTrace (prefixWord ++ tailWord_998471) baseStart_998471 baseEnd_998471 := by
    simpa [prefixWord, tailWord_998471, baseEnd_998471] using wordTrace_append hprefix tailTrace_998471
  have hstable : (prefixWord ++ tailWord_998471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998471).length < 2 ^ (prefixWord ++ tailWord_998471).sum := by decide
  have hdescent : baseEnd_998471 < baseStart_998471 := by decide
  rcases family_descends (prefixWord ++ tailWord_998471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998485 : List Nat := [1, 3, 2, 2, 1, 2, 2, 8]
def baseStart_998485 : Nat := 118140960795 + 998485 * 2 ^ 59
def prefixEnd_998485 : Nat := 4983230072969 + 3 ^ 40 * 998485 * 2
def baseEnd_998485 : Nat := 75955960193278689858601

theorem tailTrace_998485 : CollatzResearch.WordTrace tailWord_998485 prefixEnd_998485 75955960193278689858601 := by
  unfold tailWord_998485
  simp only [CollatzResearch.WordTrace]
  refine ⟨36417739787666847506708909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24278493191777898337805939 36417739787666847506708909)
  ·
    refine ⟨13656652420375067815015841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36417739787666847506708909 13656652420375067815015841)
    ·
      refine ⟨10242489315281300861261881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13656652420375067815015841 10242489315281300861261881)
      ·
        refine ⟨7681866986460975645946411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10242489315281300861261881 7681866986460975645946411)
        ·
          refine ⟨11522800479691463468919617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681866986460975645946411 11522800479691463468919617)
          ·
            refine ⟨8642100359768597601689713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522800479691463468919617 8642100359768597601689713)
            ·
              refine ⟨6481575269826448201267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642100359768597601689713 6481575269826448201267285)
              ·
                refine ⟨75955960193278689858601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6481575269826448201267285 75955960193278689858601)
                ·
                  rfl

theorem cell21_998485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_998485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998485 prefixEnd_998485 := by exact prefixLift 998485
  have htrace : WordTrace (prefixWord ++ tailWord_998485) baseStart_998485 baseEnd_998485 := by
    simpa [prefixWord, tailWord_998485, baseEnd_998485] using wordTrace_append hprefix tailTrace_998485
  have hstable : (prefixWord ++ tailWord_998485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998485).length < 2 ^ (prefixWord ++ tailWord_998485).sum := by decide
  have hdescent : baseEnd_998485 < baseStart_998485 := by decide
  rcases family_descends (prefixWord ++ tailWord_998485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998488 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_998488 : Nat := 118140960795 + 998488 * 2 ^ 59
def prefixEnd_998488 : Nat := 4983230072969 + 3 ^ 40 * 998488 * 2
def baseEnd_998488 : Nat := 227868565220708731025797

theorem tailTrace_998488 : CollatzResearch.WordTrace tailWord_998488 prefixEnd_998488 227868565220708731025797 := by
  unfold tailWord_998488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208924603327989509534059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24278566137770652679378745 18208924603327989509534059)
  ·
    refine ⟨27313386904991984264301089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18208924603327989509534059 27313386904991984264301089)
    ·
      refine ⟨20485040178743988198225817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27313386904991984264301089 20485040178743988198225817)
      ·
        refine ⟨15363780134057991148669363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20485040178743988198225817 15363780134057991148669363)
        ·
          refine ⟨23045670201086986723004045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363780134057991148669363 23045670201086986723004045)
          ·
            refine ⟨8642126325407620021126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23045670201086986723004045 8642126325407620021126517)
            ·
              refine ⟨810199343006964376980611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8642126325407620021126517 810199343006964376980611)
              ·
                refine ⟨1215299014510446565470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810199343006964376980611 1215299014510446565470917)
                ·
                  refine ⟨227868565220708731025797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215299014510446565470917 227868565220708731025797)
                  ·
                    rfl

theorem cell21_998488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_998488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998488 prefixEnd_998488 := by exact prefixLift 998488
  have htrace : WordTrace (prefixWord ++ tailWord_998488) baseStart_998488 baseEnd_998488 := by
    simpa [prefixWord, tailWord_998488, baseEnd_998488] using wordTrace_append hprefix tailTrace_998488
  have hstable : (prefixWord ++ tailWord_998488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998488).length < 2 ^ (prefixWord ++ tailWord_998488).sum := by decide
  have hdescent : baseEnd_998488 < baseStart_998488 := by decide
  rcases family_descends (prefixWord ++ tailWord_998488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998561 : List Nat := [1, 2, 3, 3, 1, 1, 1, 9]
def baseStart_998561 : Nat := 118140960795 + 998561 * 2 ^ 59
def prefixEnd_998561 : Nat := 4983230072969 + 3 ^ 40 * 998561 * 2
def baseEnd_998561 : Nat := 75961741605092275436327

theorem tailTrace_998561 : CollatzResearch.WordTrace tailWord_998561 prefixEnd_998561 75961741605092275436327 := by
  unfold tailWord_998561
  simp only [CollatzResearch.WordTrace]
  refine ⟨36420511735391512486475537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24280341156927674990983691 36420511735391512486475537)
  ·
    refine ⟨27315383801543634364856653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36420511735391512486475537 27315383801543634364856653)
    ·
      refine ⟨10243268925578862886821245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27315383801543634364856653 10243268925578862886821245)
      ·
        refine ⟨3841225847092073582557967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10243268925578862886821245 3841225847092073582557967)
        ·
          refine ⟨5761838770638110373836951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841225847092073582557967 5761838770638110373836951)
          ·
            refine ⟨8642758155957165560755427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761838770638110373836951 8642758155957165560755427)
            ·
              refine ⟨12964137233935748341133141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642758155957165560755427 12964137233935748341133141)
              ·
                refine ⟨75961741605092275436327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12964137233935748341133141 75961741605092275436327)
                ·
                  rfl

theorem cell21_998561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_998561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998561 prefixEnd_998561 := by exact prefixLift 998561
  have htrace : WordTrace (prefixWord ++ tailWord_998561) baseStart_998561 baseEnd_998561 := by
    simpa [prefixWord, tailWord_998561, baseEnd_998561] using wordTrace_append hprefix tailTrace_998561
  have hstable : (prefixWord ++ tailWord_998561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998561).length < 2 ^ (prefixWord ++ tailWord_998561).sum := by decide
  have hdescent : baseEnd_998561 < baseStart_998561 := by decide
  rcases family_descends (prefixWord ++ tailWord_998561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998612 : List Nat := [2, 4, 1, 4, 1, 1, 3, 5]
def baseStart_998612 : Nat := 118140960795 + 998612 * 2 ^ 59
def prefixEnd_998612 : Nat := 4983230072969 + 3 ^ 40 * 998612 * 2
def baseEnd_998612 : Nat := 75965621236704023652959

theorem tailTrace_998612 : CollatzResearch.WordTrace tailWord_998612 prefixEnd_998612 75965621236704023652959 := by
  unfold tailWord_998612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211185929103374098291045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24281581238804498797721393 18211185929103374098291045)
  ·
    refine ⟨3414597361706882643429571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18211185929103374098291045 3414597361706882643429571)
    ·
      refine ⟨5121896042560323965144357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414597361706882643429571 5121896042560323965144357)
      ·
        refine ⟨960355507980060743464567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5121896042560323965144357 960355507980060743464567)
        ·
          refine ⟨1440533261970091115196851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960355507980060743464567 1440533261970091115196851)
          ·
            refine ⟨2160799892955136672795277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440533261970091115196851 2160799892955136672795277)
            ·
              refine ⟨810299959858176252298229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160799892955136672795277 810299959858176252298229)
              ·
                refine ⟨75965621236704023652959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 810299959858176252298229 75965621236704023652959)
                ·
                  rfl

theorem cell21_998612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_998612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998612 prefixEnd_998612 := by exact prefixLift 998612
  have htrace : WordTrace (prefixWord ++ tailWord_998612) baseStart_998612 baseEnd_998612 := by
    simpa [prefixWord, tailWord_998612, baseEnd_998612] using wordTrace_append hprefix tailTrace_998612
  have hstable : (prefixWord ++ tailWord_998612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998612).length < 2 ^ (prefixWord ++ tailWord_998612).sum := by decide
  have hdescent : baseEnd_998612 < baseStart_998612 := by decide
  rcases family_descends (prefixWord ++ tailWord_998612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998668 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_998668 : Nat := 118140960795 + 998668 * 2 ^ 59
def prefixEnd_998668 : Nat := 4983230072969 + 3 ^ 40 * 998668 * 2
def baseEnd_998668 : Nat := 227909643673068418025429

theorem tailTrace_998668 : CollatzResearch.WordTrace tailWord_998668 prefixEnd_998668 227909643673068418025429 := by
  unfold tailWord_998668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212207173001934880310329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24282942897335913173747105 18212207173001934880310329)
  ·
    refine ⟨13659155379751451160232747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18212207173001934880310329 13659155379751451160232747)
    ·
      refine ⟨20488733069627176740349121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659155379751451160232747 20488733069627176740349121)
      ·
        refine ⟨15366549802220382555261841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20488733069627176740349121 15366549802220382555261841)
        ·
          refine ⟨11524912351665286916446381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15366549802220382555261841 11524912351665286916446381)
          ·
            refine ⟨4321842131874482593667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11524912351665286916446381 4321842131874482593667393)
            ·
              refine ⟨3241381598905861945250545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321842131874482593667393 3241381598905861945250545)
              ·
                refine ⟨2431036199179396458937909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241381598905861945250545 2431036199179396458937909)
                ·
                  refine ⟨227909643673068418025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431036199179396458937909 227909643673068418025429)
                  ·
                    rfl

theorem cell21_998668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_998668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998668 prefixEnd_998668 := by exact prefixLift 998668
  have htrace : WordTrace (prefixWord ++ tailWord_998668) baseStart_998668 baseEnd_998668 := by
    simpa [prefixWord, tailWord_998668, baseEnd_998668] using wordTrace_append hprefix tailTrace_998668
  have hstable : (prefixWord ++ tailWord_998668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998668).length < 2 ^ (prefixWord ++ tailWord_998668).sum := by decide
  have hdescent : baseEnd_998668 < baseStart_998668 := by decide
  rcases family_descends (prefixWord ++ tailWord_998668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998716 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_998716 : Nat := 118140960795 + 998716 * 2 ^ 59
def prefixEnd_998716 : Nat := 4983230072969 + 3 ^ 40 * 998716 * 2
def baseEnd_998716 : Nat := 227920597927031001225331

theorem tailTrace_998716 : CollatzResearch.WordTrace tailWord_998716 prefixEnd_998716 227920597927031001225331 := by
  unfold tailWord_998716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213082524914986979184001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24284110033219982638912001 18213082524914986979184001)
  ·
    refine ⟨13659811893686240234388001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18213082524914986979184001 13659811893686240234388001)
    ·
      refine ⟨10244858920264680175791001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13659811893686240234388001 10244858920264680175791001)
      ·
        refine ⟨7683644190198510131843251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10244858920264680175791001 7683644190198510131843251)
        ·
          refine ⟨11525466285297765197764877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683644190198510131843251 11525466285297765197764877)
          ·
            refine ⟨4322049856986661949161829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11525466285297765197764877 4322049856986661949161829)
            ·
              refine ⟨810384348184999115467843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4322049856986661949161829 810384348184999115467843)
              ·
                refine ⟨1215576522277498673201765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810384348184999115467843 1215576522277498673201765)
                ·
                  refine ⟨227920597927031001225331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215576522277498673201765 227920597927031001225331)
                  ·
                    rfl

theorem cell21_998716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_998716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998716 prefixEnd_998716 := by exact prefixLift 998716
  have htrace : WordTrace (prefixWord ++ tailWord_998716) baseStart_998716 baseEnd_998716 := by
    simpa [prefixWord, tailWord_998716, baseEnd_998716] using wordTrace_append hprefix tailTrace_998716
  have hstable : (prefixWord ++ tailWord_998716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998716).length < 2 ^ (prefixWord ++ tailWord_998716).sum := by decide
  have hdescent : baseEnd_998716 < baseStart_998716 := by decide
  rcases family_descends (prefixWord ++ tailWord_998716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998885 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 4]
def baseStart_998885 : Nat := 118140960795 + 998885 * 2 ^ 59
def prefixEnd_998885 : Nat := 4983230072969 + 3 ^ 40 * 998885 * 2
def baseEnd_998885 : Nat := 227959166029524262908319

theorem tailTrace_998885 : CollatzResearch.WordTrace tailWord_998885 prefixEnd_998885 227959166029524262908319 := by
  unfold tailWord_998885
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432328986217715821270109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24288219324145143880846739 36432328986217715821270109)
  ·
    refine ⟨13662123369831643432976291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36432328986217715821270109 13662123369831643432976291)
    ·
      refine ⟨20493185054747465149464437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13662123369831643432976291 20493185054747465149464437)
      ·
        refine ⟨1921236098882574857762291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20493185054747465149464437 1921236098882574857762291)
        ·
          refine ⟨2881854148323862286643437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921236098882574857762291 2881854148323862286643437)
          ·
            refine ⟨1080695305621448357491289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2881854148323862286643437 1080695305621448357491289)
            ·
              refine ⟨810521479216086268118467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080695305621448357491289 810521479216086268118467)
              ·
                refine ⟨1215782218824129402177701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810521479216086268118467 1215782218824129402177701)
                ·
                  refine ⟨227959166029524262908319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215782218824129402177701 227959166029524262908319)
                  ·
                    rfl

theorem cell21_998885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_998885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998885 prefixEnd_998885 := by exact prefixLift 998885
  have htrace : WordTrace (prefixWord ++ tailWord_998885) baseStart_998885 baseEnd_998885 := by
    simpa [prefixWord, tailWord_998885, baseEnd_998885] using wordTrace_append hprefix tailTrace_998885
  have hstable : (prefixWord ++ tailWord_998885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998885).length < 2 ^ (prefixWord ++ tailWord_998885).sum := by decide
  have hdescent : baseEnd_998885 < baseStart_998885 := by decide
  rcases family_descends (prefixWord ++ tailWord_998885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998924 : List Nat := [2, 2, 1, 2, 14]
def baseStart_998924 : Nat := 118140960795 + 998924 * 2 ^ 59
def prefixEnd_998924 : Nat := 4983230072969 + 3 ^ 40 * 998924 * 2
def baseEnd_998924 : Nat := 2814420572356405700719

theorem tailTrace_998924 : CollatzResearch.WordTrace tailWord_998924 prefixEnd_998924 2814420572356405700719 := by
  unfold tailWord_998924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216875716538212740969913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24289167622050950321293217 18216875716538212740969913)
  ·
    refine ⟨13662656787403659555727435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18216875716538212740969913 13662656787403659555727435)
    ·
      refine ⟨20493985181105489333591153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13662656787403659555727435 20493985181105489333591153)
      ·
        refine ⟨15370488885829117000193365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20493985181105489333591153 15370488885829117000193365)
        ·
          refine ⟨2814420572356405700719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15370488885829117000193365 2814420572356405700719)
          ·
            rfl

theorem cell21_998924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 14].length) (baseStart_998924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998924 prefixEnd_998924 := by exact prefixLift 998924
  have htrace : WordTrace (prefixWord ++ tailWord_998924) baseStart_998924 baseEnd_998924 := by
    simpa [prefixWord, tailWord_998924, baseEnd_998924] using wordTrace_append hprefix tailTrace_998924
  have hstable : (prefixWord ++ tailWord_998924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998924).length < 2 ^ (prefixWord ++ tailWord_998924).sum := by decide
  have hdescent : baseEnd_998924 < baseStart_998924 := by decide
  rcases family_descends (prefixWord ++ tailWord_998924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998986 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_998986 : Nat := 118140960795 + 998986 * 2 ^ 59
def prefixEnd_998986 : Nat := 4983230072969 + 3 ^ 40 * 998986 * 2
def baseEnd_998986 : Nat := 227982215605570531724779

theorem tailTrace_998986 : CollatzResearch.WordTrace tailWord_998986 prefixEnd_998986 227982215605570531724779 := by
  unfold tailWord_998986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109003189712952517674203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24290675172567873380464541 9109003189712952517674203)
  ·
    refine ⟨13663504784569428776511305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9109003189712952517674203 13663504784569428776511305)
    ·
      refine ⟨10247628588427071582383479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13663504784569428776511305 10247628588427071582383479)
      ·
        refine ⟨15371442882640607373575219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247628588427071582383479 15371442882640607373575219)
        ·
          refine ⟨23057164323960911060362829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371442882640607373575219 23057164323960911060362829)
          ·
            refine ⟨8646436621485341647636061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23057164323960911060362829 8646436621485341647636061)
            ·
              refine ⟨3242413733057003117863523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8646436621485341647636061 3242413733057003117863523)
              ·
                refine ⟨4863620599585504676795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242413733057003117863523 4863620599585504676795285)
                ·
                  refine ⟨227982215605570531724779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4863620599585504676795285 227982215605570531724779)
                  ·
                    rfl

theorem cell21_998986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_998986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_998986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_998986 prefixEnd_998986 := by exact prefixLift 998986
  have htrace : WordTrace (prefixWord ++ tailWord_998986) baseStart_998986 baseEnd_998986 := by
    simpa [prefixWord, tailWord_998986, baseEnd_998986] using wordTrace_append hprefix tailTrace_998986
  have hstable : (prefixWord ++ tailWord_998986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998986).length < 2 ^ (prefixWord ++ tailWord_998986).sum := by decide
  have hdescent : baseEnd_998986 < baseStart_998986 := by decide
  rcases family_descends (prefixWord ++ tailWord_998986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999000 : List Nat := [2, 1, 2, 2, 1, 2, 1, 10]
def baseStart_999000 : Nat := 118140960795 + 999000 * 2 ^ 59
def prefixEnd_999000 : Nat := 4983230072969 + 3 ^ 40 * 999000 * 2
def baseEnd_999000 : Nat := 75995136865436539497139

theorem tailTrace_999000 : CollatzResearch.WordTrace tailWord_999000 prefixEnd_999000 75995136865436539497139 := by
  unfold tailWord_999000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18218261690400545230853227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24291015587200726974470969 18218261690400545230853227)
  ·
    refine ⟨27327392535600817846279841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18218261690400545230853227 27327392535600817846279841)
    ·
      refine ⟨20495544401700613384709881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27327392535600817846279841 20495544401700613384709881)
      ·
        refine ⟨15371658301275460038532411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20495544401700613384709881 15371658301275460038532411)
        ·
          refine ⟨23057487451913190057798617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371658301275460038532411 23057487451913190057798617)
          ·
            refine ⟨17293115588934892543348963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23057487451913190057798617 17293115588934892543348963)
            ·
              refine ⟨25939673383402338815023445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17293115588934892543348963 25939673383402338815023445)
              ·
                refine ⟨75995136865436539497139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25939673383402338815023445 75995136865436539497139)
                ·
                  rfl

theorem cell21_999000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_999000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999000 prefixEnd_999000 := by exact prefixLift 999000
  have htrace : WordTrace (prefixWord ++ tailWord_999000) baseStart_999000 baseEnd_999000 := by
    simpa [prefixWord, tailWord_999000, baseEnd_999000] using wordTrace_append hprefix tailTrace_999000
  have hstable : (prefixWord ++ tailWord_999000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999000).length < 2 ^ (prefixWord ++ tailWord_999000).sum := by decide
  have hdescent : baseEnd_999000 < baseStart_999000 := by decide
  rcases family_descends (prefixWord ++ tailWord_999000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999017 : List Nat := [1, 2, 1, 1, 1, 4, 6, 5]
def baseStart_999017 : Nat := 118140960795 + 999017 * 2 ^ 59
def prefixEnd_999017 : Nat := 4983230072969 + 3 ^ 40 * 999017 * 2
def baseEnd_999017 : Nat := 75996430075973788902683

theorem tailTrace_999017 : CollatzResearch.WordTrace tailWord_999017 prefixEnd_999017 75996430075973788902683 := by
  unfold tailWord_999017
  simp only [CollatzResearch.WordTrace]
  refine ⟨36437143421739502365075305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24291428947826334910050203 36437143421739502365075305)
  ·
    refine ⟨27327857566304626773806479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36437143421739502365075305 27327857566304626773806479)
    ·
      refine ⟨40991786349456940160709719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27327857566304626773806479 40991786349456940160709719)
      ·
        refine ⟨61487679524185410241064579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40991786349456940160709719 61487679524185410241064579)
        ·
          refine ⟨92231519286278115361596869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61487679524185410241064579 92231519286278115361596869)
          ·
            refine ⟨17293409866177146630299413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92231519286278115361596869 17293409866177146630299413)
            ·
              refine ⟨810628587477053748295285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17293409866177146630299413 810628587477053748295285)
              ·
                refine ⟨75996430075973788902683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 810628587477053748295285 75996430075973788902683)
                ·
                  rfl

theorem cell21_999017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].length) (baseStart_999017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999017 prefixEnd_999017 := by exact prefixLift 999017
  have htrace : WordTrace (prefixWord ++ tailWord_999017) baseStart_999017 baseEnd_999017 := by
    simpa [prefixWord, tailWord_999017, baseEnd_999017] using wordTrace_append hprefix tailTrace_999017
  have hstable : (prefixWord ++ tailWord_999017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999017).length < 2 ^ (prefixWord ++ tailWord_999017).sum := by decide
  have hdescent : baseEnd_999017 < baseStart_999017 := by decide
  rcases family_descends (prefixWord ++ tailWord_999017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999093 : List Nat := [1, 3, 3, 3, 2, 9]
def baseStart_999093 : Nat := 118140960795 + 999093 * 2 ^ 59
def prefixEnd_999093 : Nat := 4983230072969 + 3 ^ 40 * 999093 * 2
def baseEnd_999093 : Nat := 8444690165309708275601

theorem tailTrace_999093 : CollatzResearch.WordTrace tailWord_999093 prefixEnd_999093 8444690165309708275601 := by
  unfold tailWord_999093
  simp only [CollatzResearch.WordTrace]
  refine ⟨36439915369464167344841933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24293276912976111563227955 36439915369464167344841933)
  ·
    refine ⟨13664968263549062754315725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36439915369464167344841933 13664968263549062754315725)
    ·
      refine ⟨5124363098830898532868397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13664968263549062754315725 5124363098830898532868397)
      ·
        refine ⟨1921636162061586949825649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5124363098830898532868397 1921636162061586949825649)
        ·
          refine ⟨1441227121546190212369237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921636162061586949825649 1441227121546190212369237)
          ·
            refine ⟨8444690165309708275601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1441227121546190212369237 8444690165309708275601)
            ·
              rfl

theorem cell21_999093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 9].length) (baseStart_999093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999093 prefixEnd_999093 := by exact prefixLift 999093
  have htrace : WordTrace (prefixWord ++ tailWord_999093) baseStart_999093 baseEnd_999093 := by
    simpa [prefixWord, tailWord_999093, baseEnd_999093] using wordTrace_append hprefix tailTrace_999093
  have hstable : (prefixWord ++ tailWord_999093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999093).length < 2 ^ (prefixWord ++ tailWord_999093).sum := by decide
  have hdescent : baseEnd_999093 < baseStart_999093 := by decide
  rcases family_descends (prefixWord ++ tailWord_999093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999124 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_999124 : Nat := 118140960795 + 999124 * 2 ^ 59
def prefixEnd_999124 : Nat := 4983230072969 + 3 ^ 40 * 999124 * 2
def baseEnd_999124 : Nat := 228013709085712958424497

theorem tailTrace_999124 : CollatzResearch.WordTrace tailWord_999124 prefixEnd_999124 228013709085712958424497 := by
  unfold tailWord_999124
  simp only [CollatzResearch.WordTrace]
  refine ⟨18220523016175929819610213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24294030688234573092813617 18220523016175929819610213)
  ·
    refine ⟨3416348065532986841176915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18220523016175929819610213 3416348065532986841176915)
    ·
      refine ⟨5124522098299480261765373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416348065532986841176915 5124522098299480261765373)
      ·
        refine ⟨1921695786862305098162015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5124522098299480261765373 1921695786862305098162015)
        ·
          refine ⟨2882543680293457647243023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921695786862305098162015 2882543680293457647243023)
          ·
            refine ⟨4323815520440186470864535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882543680293457647243023 4323815520440186470864535)
            ·
              refine ⟨6485723280660279706296803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323815520440186470864535 6485723280660279706296803)
              ·
                refine ⟨9728584920990419559445205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485723280660279706296803 9728584920990419559445205)
                ·
                  refine ⟨228013709085712958424497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9728584920990419559445205 228013709085712958424497)
                  ·
                    rfl

theorem cell21_999124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_999124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999124 prefixEnd_999124 := by exact prefixLift 999124
  have htrace : WordTrace (prefixWord ++ tailWord_999124) baseStart_999124 baseEnd_999124 := by
    simpa [prefixWord, tailWord_999124, baseEnd_999124] using wordTrace_append hprefix tailTrace_999124
  have hstable : (prefixWord ++ tailWord_999124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999124).length < 2 ^ (prefixWord ++ tailWord_999124).sum := by decide
  have hdescent : baseEnd_999124 < baseStart_999124 := by decide
  rcases family_descends (prefixWord ++ tailWord_999124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999141 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 3]
def baseStart_999141 : Nat := 118140960795 + 999141 * 2 ^ 59
def prefixEnd_999141 : Nat := 4983230072969 + 3 ^ 40 * 999141 * 2
def baseEnd_999141 : Nat := 228017588717324706641129

theorem tailTrace_999141 : CollatzResearch.WordTrace tailWord_999141 prefixEnd_999141 228017588717324706641129 := by
  unfold tailWord_999141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441666073290271542589277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24294444048860181028392851 36441666073290271542589277)
  ·
    refine ⟨13665624777483851828470979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36441666073290271542589277 13665624777483851828470979)
    ·
      refine ⟨20498437166225777742706469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665624777483851828470979 20498437166225777742706469)
      ·
        refine ⟨3843456968667333326757463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20498437166225777742706469 3843456968667333326757463)
        ·
          refine ⟨5765185453000999990136195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843456968667333326757463 5765185453000999990136195)
          ·
            refine ⟨8647778179501499985204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765185453000999990136195 8647778179501499985204293)
            ·
              refine ⟨1621458408656531247225805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8647778179501499985204293 1621458408656531247225805)
              ·
                refine ⟨608046903246199217709677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621458408656531247225805 608046903246199217709677)
                ·
                  refine ⟨228017588717324706641129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608046903246199217709677 228017588717324706641129)
                  ·
                    rfl

theorem cell21_999141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_999141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999141 prefixEnd_999141 := by exact prefixLift 999141
  have htrace : WordTrace (prefixWord ++ tailWord_999141) baseStart_999141 baseEnd_999141 := by
    simpa [prefixWord, tailWord_999141, baseEnd_999141] using wordTrace_append hprefix tailTrace_999141
  have hstable : (prefixWord ++ tailWord_999141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999141).length < 2 ^ (prefixWord ++ tailWord_999141).sum := by decide
  have hdescent : baseEnd_999141 < baseStart_999141 := by decide
  rcases family_descends (prefixWord ++ tailWord_999141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999172 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_999172 : Nat := 118140960795 + 999172 * 2 ^ 59
def prefixEnd_999172 : Nat := 4983230072969 + 3 ^ 40 * 999172 * 2
def baseEnd_999172 : Nat := 228024663339675541624399

theorem tailTrace_999172 : CollatzResearch.WordTrace tailWord_999172 prefixEnd_999172 228024663339675541624399 := by
  unfold tailWord_999172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221398368088981918483885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24295197824118642557978513 18221398368088981918483885)
  ·
    refine ⟨6833024388033368219431457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18221398368088981918483885 6833024388033368219431457)
    ·
      refine ⟨5124768291025026164573593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6833024388033368219431457 5124768291025026164573593)
      ·
        refine ⟨3843576218268769623430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5124768291025026164573593 3843576218268769623430195)
        ·
          refine ⟨5765364327403154435145293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843576218268769623430195 5765364327403154435145293)
          ·
            refine ⟨2162011622776182913179485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5765364327403154435145293 2162011622776182913179485)
            ·
              refine ⟨810754358541068592442307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2162011622776182913179485 810754358541068592442307)
              ·
                refine ⟨1216131537811602888663461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810754358541068592442307 1216131537811602888663461)
                ·
                  refine ⟨228024663339675541624399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216131537811602888663461 228024663339675541624399)
                  ·
                    rfl

theorem cell21_999172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_999172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999172 prefixEnd_999172 := by exact prefixLift 999172
  have htrace : WordTrace (prefixWord ++ tailWord_999172) baseStart_999172 baseEnd_999172 := by
    simpa [prefixWord, tailWord_999172, baseEnd_999172] using wordTrace_append hprefix tailTrace_999172
  have hstable : (prefixWord ++ tailWord_999172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999172).length < 2 ^ (prefixWord ++ tailWord_999172).sum := by decide
  have hdescent : baseEnd_999172 < baseStart_999172 := by decide
  rcases family_descends (prefixWord ++ tailWord_999172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999186 : List Nat := [3, 2, 4, 1, 1, 2, 1, 7]
def baseStart_999186 : Nat := 118140960795 + 999186 * 2 ^ 59
def prefixEnd_999186 : Nat := 4983230072969 + 3 ^ 40 * 999186 * 2
def baseEnd_999186 : Nat := 76009286110138209463679

theorem tailTrace_999186 : CollatzResearch.WordTrace tailWord_999186 prefixEnd_999186 76009286110138209463679 := by
  unfold tailWord_999186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110826839531811056994353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24295538238751496151984941 9110826839531811056994353)
  ·
    refine ⟨6833120129648858292745765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9110826839531811056994353 6833120129648858292745765)
    ·
      refine ⟨1281210024309160929889831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6833120129648858292745765 1281210024309160929889831)
      ·
        refine ⟨1921815036463741394834747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281210024309160929889831 1921815036463741394834747)
        ·
          refine ⟨2882722554695612092252121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921815036463741394834747 2882722554695612092252121)
          ·
            refine ⟨2162041916021709069189091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882722554695612092252121 2162041916021709069189091)
            ·
              refine ⟨3243062874032563603783637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162041916021709069189091 3243062874032563603783637)
              ·
                refine ⟨76009286110138209463679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3243062874032563603783637 76009286110138209463679)
                ·
                  rfl

theorem cell21_999186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_999186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999186 prefixEnd_999186 := by exact prefixLift 999186
  have htrace : WordTrace (prefixWord ++ tailWord_999186) baseStart_999186 baseEnd_999186 := by
    simpa [prefixWord, tailWord_999186, baseEnd_999186] using wordTrace_append hprefix tailTrace_999186
  have hstable : (prefixWord ++ tailWord_999186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999186).length < 2 ^ (prefixWord ++ tailWord_999186).sum := by decide
  have hdescent : baseEnd_999186 < baseStart_999186 := by decide
  rcases family_descends (prefixWord ++ tailWord_999186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999228 : List Nat := [2, 2, 2, 2, 1, 1, 3, 8]
def baseStart_999228 : Nat := 118140960795 + 999228 * 2 ^ 59
def prefixEnd_999228 : Nat := 4983230072969 + 3 ^ 40 * 999228 * 2
def baseEnd_999228 : Nat := 76012481100877296230317

theorem tailTrace_999228 : CollatzResearch.WordTrace tailWord_999228 prefixEnd_999228 76012481100877296230317 := by
  unfold tailWord_999228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222419611987542700503169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24296559482650056934004225 18222419611987542700503169)
  ·
    refine ⟨13666814708990657025377377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18222419611987542700503169 13666814708990657025377377)
    ·
      refine ⟨10250111031742992769033033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13666814708990657025377377 10250111031742992769033033)
      ·
        refine ⟨7687583273807244576774775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10250111031742992769033033 7687583273807244576774775)
        ·
          refine ⟨11531374910710866865162163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687583273807244576774775 11531374910710866865162163)
          ·
            refine ⟨17297062366066300297743245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531374910710866865162163 17297062366066300297743245)
            ·
              refine ⟨6486398387274862611653717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17297062366066300297743245 6486398387274862611653717)
              ·
                refine ⟨76012481100877296230317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6486398387274862611653717 76012481100877296230317)
                ·
                  rfl

theorem cell21_999228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_999228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999228 prefixEnd_999228 := by exact prefixLift 999228
  have htrace : WordTrace (prefixWord ++ tailWord_999228) baseStart_999228 baseEnd_999228 := by
    simpa [prefixWord, tailWord_999228, baseEnd_999228] using wordTrace_append hprefix tailTrace_999228
  have hstable : (prefixWord ++ tailWord_999228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999228).length < 2 ^ (prefixWord ++ tailWord_999228).sum := by decide
  have hdescent : baseEnd_999228 < baseStart_999228 := by decide
  rcases family_descends (prefixWord ++ tailWord_999228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999231 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_999231 : Nat := 118140960795 + 999231 * 2 ^ 59
def prefixEnd_999231 : Nat := 4983230072969 + 3 ^ 40 * 999231 * 2
def baseEnd_999231 : Nat := 228038127943504550140945

theorem tailTrace_999231 : CollatzResearch.WordTrace tailWord_999231 prefixEnd_999231 228038127943504550140945 := by
  unfold tailWord_999231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36444948642964216913365547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24296632428642811275577031 36444948642964216913365547)
  ·
    refine ⟨54667422964446325370048321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36444948642964216913365547 54667422964446325370048321)
    ·
      refine ⟨41000567223334744027536241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54667422964446325370048321 41000567223334744027536241)
      ·
        refine ⟨30750425417501058020652181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41000567223334744027536241 30750425417501058020652181)
        ·
          refine ⟨1441426191445362094718071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30750425417501058020652181 1441426191445362094718071)
          ·
            refine ⟨2162139287168043142077107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441426191445362094718071 2162139287168043142077107)
            ·
              refine ⟨3243208930752064713115661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162139287168043142077107 3243208930752064713115661)
              ·
                refine ⟨1216203349032024267418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243208930752064713115661 1216203349032024267418373)
                ·
                  refine ⟨228038127943504550140945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216203349032024267418373 228038127943504550140945)
                  ·
                    rfl

theorem cell21_999231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_999231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999231 prefixEnd_999231 := by exact prefixLift 999231
  have htrace : WordTrace (prefixWord ++ tailWord_999231) baseStart_999231 baseEnd_999231 := by
    simpa [prefixWord, tailWord_999231, baseEnd_999231] using wordTrace_append hprefix tailTrace_999231
  have hstable : (prefixWord ++ tailWord_999231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999231).length < 2 ^ (prefixWord ++ tailWord_999231).sum := by decide
  have hdescent : baseEnd_999231 < baseStart_999231 := by decide
  rcases family_descends (prefixWord ++ tailWord_999231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999273 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_999273 : Nat := 118140960795 + 999273 * 2 ^ 59
def prefixEnd_999273 : Nat := 4983230072969 + 3 ^ 40 * 999273 * 2
def baseEnd_999273 : Nat := 228047712915721810440859

theorem tailTrace_999273 : CollatzResearch.WordTrace tailWord_999273 prefixEnd_999273 228047712915721810440859 := by
  unfold tailWord_999273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446480508812058086394473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24297653672541372057596315 36446480508812058086394473)
  ·
    refine ⟨27334860381609043564795855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36446480508812058086394473 27334860381609043564795855)
    ·
      refine ⟨41002290572413565347193783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27334860381609043564795855 41002290572413565347193783)
      ·
        refine ⟨61503435858620348020790675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41002290572413565347193783 61503435858620348020790675)
        ·
          refine ⟨92255153787930522031186013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61503435858620348020790675 92255153787930522031186013)
          ·
            refine ⟨34595682670473945761694755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92255153787930522031186013 34595682670473945761694755)
            ·
              refine ⟨51893524005710918642542133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34595682670473945761694755 51893524005710918642542133)
              ·
                refine ⟨4865017875535398622738325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51893524005710918642542133 4865017875535398622738325)
                ·
                  refine ⟨228047712915721810440859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4865017875535398622738325 228047712915721810440859)
                  ·
                    rfl

theorem cell21_999273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_999273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999273 prefixEnd_999273 := by exact prefixLift 999273
  have htrace : WordTrace (prefixWord ++ tailWord_999273) baseStart_999273 baseEnd_999273 := by
    simpa [prefixWord, tailWord_999273, baseEnd_999273] using wordTrace_append hprefix tailTrace_999273
  have hstable : (prefixWord ++ tailWord_999273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999273).length < 2 ^ (prefixWord ++ tailWord_999273).sum := by decide
  have hdescent : baseEnd_999273 < baseStart_999273 := by decide
  rcases family_descends (prefixWord ++ tailWord_999273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999290 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_999290 : Nat := 118140960795 + 999290 * 2 ^ 59
def prefixEnd_999290 : Nat := 4983230072969 + 3 ^ 40 * 999290 * 2
def baseEnd_999290 : Nat := 228051592547333558657491

theorem tailTrace_999290 : CollatzResearch.WordTrace tailWord_999290 prefixEnd_999290 228051592547333558657491 := by
  unfold tailWord_999290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111775137437617497440831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24298067033166979993175549 9111775137437617497440831)
  ·
    refine ⟨13667662706156426246161247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9111775137437617497440831 13667662706156426246161247)
    ·
      refine ⟨20501494059234639369241871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667662706156426246161247 20501494059234639369241871)
      ·
        refine ⟨30752241088851959053862807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20501494059234639369241871 30752241088851959053862807)
        ·
          refine ⟨46128361633277938580794211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30752241088851959053862807 46128361633277938580794211)
          ·
            refine ⟨69192542449916907871191317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46128361633277938580794211 69192542449916907871191317)
            ·
              refine ⟨3243400427339855056462093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69192542449916907871191317 3243400427339855056462093)
              ·
                refine ⟨1216275160252445646173285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243400427339855056462093 1216275160252445646173285)
                ·
                  refine ⟨228051592547333558657491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216275160252445646173285 228051592547333558657491)
                  ·
                    rfl

theorem cell21_999290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_999290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999290 prefixEnd_999290 := by exact prefixLift 999290
  have htrace : WordTrace (prefixWord ++ tailWord_999290) baseStart_999290 baseEnd_999290 := by
    simpa [prefixWord, tailWord_999290, baseEnd_999290] using wordTrace_append hprefix tailTrace_999290
  have hstable : (prefixWord ++ tailWord_999290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999290).length < 2 ^ (prefixWord ++ tailWord_999290).sum := by decide
  have hdescent : baseEnd_999290 < baseStart_999290 := by decide
  rcases family_descends (prefixWord ++ tailWord_999290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999324 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_999324 : Nat := 118140960795 + 999324 * 2 ^ 59
def prefixEnd_999324 : Nat := 4983230072969 + 3 ^ 40 * 999324 * 2
def baseEnd_999324 : Nat := 228059351810557055090755

theorem tailTrace_999324 : CollatzResearch.WordTrace tailWord_999324 prefixEnd_999324 228059351810557055090755 := by
  unfold tailWord_999324
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224170315813646898250513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24298893754418195864334017 18224170315813646898250513)
  ·
    refine ⟨13668127736860235173687885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18224170315813646898250513 13668127736860235173687885)
    ·
      refine ⟨5125547901322588190132957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13668127736860235173687885 5125547901322588190132957)
      ·
        refine ⟨1922080462995970571299859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5125547901322588190132957 1922080462995970571299859)
        ·
          refine ⟨2883120694493955856949789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922080462995970571299859 2883120694493955856949789)
          ·
            refine ⟨1081170260435233446356171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2883120694493955856949789 1081170260435233446356171)
            ·
              refine ⟨1621755390652850169534257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081170260435233446356171 1621755390652850169534257)
              ·
                refine ⟨1216316542989637627150693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621755390652850169534257 1216316542989637627150693)
                ·
                  refine ⟨228059351810557055090755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216316542989637627150693 228059351810557055090755)
                  ·
                    rfl

theorem cell21_999324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_999324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999324 prefixEnd_999324 := by exact prefixLift 999324
  have htrace : WordTrace (prefixWord ++ tailWord_999324) baseStart_999324 baseEnd_999324 := by
    simpa [prefixWord, tailWord_999324, baseEnd_999324] using wordTrace_append hprefix tailTrace_999324
  have hstable : (prefixWord ++ tailWord_999324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999324).length < 2 ^ (prefixWord ++ tailWord_999324).sum := by decide
  have hdescent : baseEnd_999324 < baseStart_999324 := by decide
  rcases family_descends (prefixWord ++ tailWord_999324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999386 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_999386 : Nat := 118140960795 + 999386 * 2 ^ 59
def prefixEnd_999386 : Nat := 4983230072969 + 3 ^ 40 * 999386 * 2
def baseEnd_999386 : Nat := 228073501055258725057295

theorem tailTrace_999386 : CollatzResearch.WordTrace tailWord_999386 prefixEnd_999386 228073501055258725057295 := by
  unfold tailWord_999386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112650489350669596314503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24300401304935118923505341 9112650489350669596314503)
  ·
    refine ⟨13668975734026004394471755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112650489350669596314503 13668975734026004394471755)
    ·
      refine ⟨20503463601039006591707633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668975734026004394471755 20503463601039006591707633)
      ·
        refine ⟨15377597700779254943780725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20503463601039006591707633 15377597700779254943780725)
        ·
          refine ⟨1441649784448055150979443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15377597700779254943780725 1441649784448055150979443)
          ·
            refine ⟨2162474676672082726469165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441649784448055150979443 2162474676672082726469165)
            ·
              refine ⟨810928003752031022425937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2162474676672082726469165 810928003752031022425937)
              ·
                refine ⟨608196002814023266819453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810928003752031022425937 608196002814023266819453)
                ·
                  refine ⟨228073501055258725057295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608196002814023266819453 228073501055258725057295)
                  ·
                    rfl

theorem cell21_999386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_999386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999386 prefixEnd_999386 := by exact prefixLift 999386
  have htrace : WordTrace (prefixWord ++ tailWord_999386) baseStart_999386 baseEnd_999386 := by
    simpa [prefixWord, tailWord_999386, baseEnd_999386] using wordTrace_append hprefix tailTrace_999386
  have hstable : (prefixWord ++ tailWord_999386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999386).length < 2 ^ (prefixWord ++ tailWord_999386).sum := by decide
  have hdescent : baseEnd_999386 < baseStart_999386 := by decide
  rcases family_descends (prefixWord ++ tailWord_999386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999437 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 3]
def baseStart_999437 : Nat := 118140960795 + 999437 * 2 ^ 59
def prefixEnd_999437 : Nat := 4983230072969 + 3 ^ 40 * 999437 * 2
def baseEnd_999437 : Nat := 228085139950093969707191

theorem tailTrace_999437 : CollatzResearch.WordTrace tailWord_999437 prefixEnd_999437 228085139950093969707191 := by
  unfold tailWord_999437
  simp only [CollatzResearch.WordTrace]
  refine ⟨36452462080217914095364565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24301641386811942730243043 36452462080217914095364565)
  ·
    refine ⟨854354580005107361610107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36452462080217914095364565 854354580005107361610107)
    ·
      refine ⟨1281531870007661042415161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854354580005107361610107 1281531870007661042415161)
      ·
        refine ⟨961148902505745781811371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281531870007661042415161 961148902505745781811371)
        ·
          refine ⟨1441723353758618672717057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961148902505745781811371 1441723353758618672717057)
          ·
            refine ⟨1081292515318964004537793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1441723353758618672717057 1081292515318964004537793)
            ·
              refine ⟨810969386489223003403345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081292515318964004537793 810969386489223003403345)
              ·
                refine ⟨608227039866917252552509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810969386489223003403345 608227039866917252552509)
                ·
                  refine ⟨228085139950093969707191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608227039866917252552509 228085139950093969707191)
                  ·
                    rfl

theorem cell21_999437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_999437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999437 prefixEnd_999437 := by exact prefixLift 999437
  have htrace : WordTrace (prefixWord ++ tailWord_999437) baseStart_999437 baseEnd_999437 := by
    simpa [prefixWord, tailWord_999437, baseEnd_999437] using wordTrace_append hprefix tailTrace_999437
  have hstable : (prefixWord ++ tailWord_999437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999437).length < 2 ^ (prefixWord ++ tailWord_999437).sum := by decide
  have hdescent : baseEnd_999437 < baseStart_999437 := by decide
  rcases family_descends (prefixWord ++ tailWord_999437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999445 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 3]
def baseStart_999445 : Nat := 118140960795 + 999445 * 2 ^ 59
def prefixEnd_999445 : Nat := 4983230072969 + 3 ^ 40 * 999445 * 2
def baseEnd_999445 : Nat := 228086965659087733573841

theorem tailTrace_999445 : CollatzResearch.WordTrace tailWord_999445 prefixEnd_999445 228086965659087733573841 := by
  unfold tailWord_999445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36452753864188931461655789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24301835909459287641103859 36452753864188931461655789)
  ·
    refine ⟨13669782699070849298120921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36452753864188931461655789 13669782699070849298120921)
    ·
      refine ⟨10252337024303136973590691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13669782699070849298120921 10252337024303136973590691)
      ·
        refine ⟨15378505536454705460386037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10252337024303136973590691 15378505536454705460386037)
        ·
          refine ⟨1441734894042628636911191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15378505536454705460386037 1441734894042628636911191)
          ·
            refine ⟨2162602341063942955366787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441734894042628636911191 2162602341063942955366787)
            ·
              refine ⟨3243903511595914433050181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162602341063942955366787 3243903511595914433050181)
              ·
                refine ⟨608231908424233956196909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3243903511595914433050181 608231908424233956196909)
                ·
                  refine ⟨228086965659087733573841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608231908424233956196909 228086965659087733573841)
                  ·
                    rfl

theorem cell21_999445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_999445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999445 prefixEnd_999445 := by exact prefixLift 999445
  have htrace : WordTrace (prefixWord ++ tailWord_999445) baseStart_999445 baseEnd_999445 := by
    simpa [prefixWord, tailWord_999445, baseEnd_999445] using wordTrace_append hprefix tailTrace_999445
  have hstable : (prefixWord ++ tailWord_999445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999445).length < 2 ^ (prefixWord ++ tailWord_999445).sum := by decide
  have hdescent : baseEnd_999445 < baseStart_999445 := by decide
  rcases family_descends (prefixWord ++ tailWord_999445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999473 : List Nat := [1, 2, 2, 3, 1, 4, 3, 5]
def baseStart_999473 : Nat := 118140960795 + 999473 * 2 ^ 59
def prefixEnd_999473 : Nat := 4983230072969 + 3 ^ 40 * 999473 * 2
def baseEnd_999473 : Nat := 76031118546855302369039

theorem tailTrace_999473 : CollatzResearch.WordTrace tailWord_999473 prefixEnd_999473 76031118546855302369039 := by
  unfold tailWord_999473
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453775108087492243675073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24302516738724994829116715 36453775108087492243675073)
  ·
    refine ⟨27340331331065619182756305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36453775108087492243675073 27340331331065619182756305)
    ·
      refine ⟨20505248498299214387067229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27340331331065619182756305 20505248498299214387067229)
      ·
        refine ⟨7689468186862205395150211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20505248498299214387067229 7689468186862205395150211)
        ·
          refine ⟨11534202280293308092725317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689468186862205395150211 11534202280293308092725317)
          ·
            refine ⟨2162662927554995267385997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11534202280293308092725317 2162662927554995267385997)
            ·
              refine ⟨810998597833123225269749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2162662927554995267385997 810998597833123225269749)
              ·
                refine ⟨76031118546855302369039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 810998597833123225269749 76031118546855302369039)
                ·
                  rfl

theorem cell21_999473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].length) (baseStart_999473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999473 prefixEnd_999473 := by exact prefixLift 999473
  have htrace : WordTrace (prefixWord ++ tailWord_999473) baseStart_999473 baseEnd_999473 := by
    simpa [prefixWord, tailWord_999473, baseEnd_999473] using wordTrace_append hprefix tailTrace_999473
  have hstable : (prefixWord ++ tailWord_999473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999473).length < 2 ^ (prefixWord ++ tailWord_999473).sum := by decide
  have hdescent : baseEnd_999473 < baseStart_999473 := by decide
  rcases family_descends (prefixWord ++ tailWord_999473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999532 : List Nat := [2, 2, 1, 1, 3, 4, 1, 7]
def baseStart_999532 : Nat := 118140960795 + 999532 * 2 ^ 59
def prefixEnd_999532 : Nat := 4983230072969 + 3 ^ 40 * 999532 * 2
def baseEnd_999532 : Nat := 76035606748131638541221

theorem tailTrace_999532 : CollatzResearch.WordTrace tailWord_999532 prefixEnd_999532 76035606748131638541221 := by
  unfold tailWord_999532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227963507436872660036425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24303951343249163546715233 18227963507436872660036425)
  ·
    refine ⟨13670972630577654495027319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18227963507436872660036425 13670972630577654495027319)
    ·
      refine ⟨20506458945866481742540979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670972630577654495027319 20506458945866481742540979)
      ·
        refine ⟨30759688418799722613811469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506458945866481742540979 30759688418799722613811469)
        ·
          refine ⟨11534883157049895980179301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30759688418799722613811469 11534883157049895980179301)
          ·
            refine ⟨2162790591946855496283619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11534883157049895980179301 2162790591946855496283619)
            ·
              refine ⟨3244185887920283244425429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162790591946855496283619 3244185887920283244425429)
              ·
                refine ⟨76035606748131638541221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3244185887920283244425429 76035606748131638541221)
                ·
                  rfl

theorem cell21_999532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_999532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999532 prefixEnd_999532 := by exact prefixLift 999532
  have htrace : WordTrace (prefixWord ++ tailWord_999532) baseStart_999532 baseEnd_999532 := by
    simpa [prefixWord, tailWord_999532, baseEnd_999532] using wordTrace_append hprefix tailTrace_999532
  have hstable : (prefixWord ++ tailWord_999532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999532).length < 2 ^ (prefixWord ++ tailWord_999532).sum := by decide
  have hdescent : baseEnd_999532 < baseStart_999532 := by decide
  rcases family_descends (prefixWord ++ tailWord_999532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999656 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_999656 : Nat := 118140960795 + 999656 * 2 ^ 59
def prefixEnd_999656 : Nat := 4983230072969 + 3 ^ 40 * 999656 * 2
def baseEnd_999656 : Nat := 228135118733798255556743

theorem tailTrace_999656 : CollatzResearch.WordTrace tailWord_999656 prefixEnd_999656 228135118733798255556743 := by
  unfold tailWord_999656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18230224833212257248793411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24306966444283009665057881 18230224833212257248793411)
  ·
    refine ⟨27345337249818385873190117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18230224833212257248793411 27345337249818385873190117)
    ·
      refine ⟨5127250734340947351223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27345337249818385873190117 5127250734340947351223147)
      ·
        refine ⟨7690876101511421026834721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127250734340947351223147 7690876101511421026834721)
        ·
          refine ⟨5768157076133565770126041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7690876101511421026834721 5768157076133565770126041)
          ·
            refine ⟨4326117807100174327594531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5768157076133565770126041 4326117807100174327594531)
            ·
              refine ⟨6489176710650261491391797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326117807100174327594531 6489176710650261491391797)
              ·
                refine ⟨608360316623462014817981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6489176710650261491391797 608360316623462014817981)
                ·
                  refine ⟨228135118733798255556743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608360316623462014817981 228135118733798255556743)
                  ·
                    rfl

theorem cell21_999656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_999656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999656 prefixEnd_999656 := by exact prefixLift 999656
  have htrace : WordTrace (prefixWord ++ tailWord_999656) baseStart_999656 baseEnd_999656 := by
    simpa [prefixWord, tailWord_999656, baseEnd_999656] using wordTrace_append hprefix tailTrace_999656
  have hstable : (prefixWord ++ tailWord_999656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999656).length < 2 ^ (prefixWord ++ tailWord_999656).sum := by decide
  have hdescent : baseEnd_999656 < baseStart_999656 := by decide
  rcases family_descends (prefixWord ++ tailWord_999656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999667 : List Nat := [1, 1, 1, 2, 2, 4, 10]
def baseStart_999667 : Nat := 118140960795 + 999667 * 2 ^ 59
def prefixEnd_999667 : Nat := 4983230072969 + 3 ^ 40 * 999667 * 2
def baseEnd_999667 : Nat := 25348625453740520097043

theorem tailTrace_999667 : CollatzResearch.WordTrace tailWord_999667 prefixEnd_999667 25348625453740520097043 := by
  unfold tailWord_999667
  simp only [CollatzResearch.WordTrace]
  refine ⟨36460850869384663376237255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24307233912923108917491503 36460850869384663376237255)
  ·
    refine ⟨54691276304076995064355883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36460850869384663376237255 54691276304076995064355883)
    ·
      refine ⟨82036914456115492596533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54691276304076995064355883 82036914456115492596533825)
      ·
        refine ⟨61527685842086619447400369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82036914456115492596533825 61527685842086619447400369)
        ·
          refine ⟨46145764381564964585550277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61527685842086619447400369 46145764381564964585550277)
          ·
            refine ⟨8652330821543430859790677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46145764381564964585550277 8652330821543430859790677)
            ·
              refine ⟨25348625453740520097043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8652330821543430859790677 25348625453740520097043)
              ·
                rfl

theorem cell21_999667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_999667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999667 prefixEnd_999667 := by exact prefixLift 999667
  have htrace : WordTrace (prefixWord ++ tailWord_999667) baseStart_999667 baseEnd_999667 := by
    simpa [prefixWord, tailWord_999667, baseEnd_999667] using wordTrace_append hprefix tailTrace_999667
  have hstable : (prefixWord ++ tailWord_999667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999667).length < 2 ^ (prefixWord ++ tailWord_999667).sum := by decide
  have hdescent : baseEnd_999667 < baseStart_999667 := by decide
  rcases family_descends (prefixWord ++ tailWord_999667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999732 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_999732 : Nat := 118140960795 + 999732 * 2 ^ 59
def prefixEnd_999732 : Nat := 4983230072969 + 3 ^ 40 * 999732 * 2
def baseEnd_999732 : Nat := 228152462969239012289921

theorem tailTrace_999732 : CollatzResearch.WordTrace tailWord_999732 prefixEnd_999732 228152462969239012289921 := by
  unfold tailWord_999732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231610807074589738676725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24308814409432786318235633 18231610807074589738676725)
  ·
    refine ⟨1709213513163242788000943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18231610807074589738676725 1709213513163242788000943)
    ·
      refine ⟨2563820269744864182001415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709213513163242788000943 2563820269744864182001415)
      ·
        refine ⟨3845730404617296273002123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563820269744864182001415 3845730404617296273002123)
        ·
          refine ⟨5768595606925944409503185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845730404617296273002123 5768595606925944409503185)
          ·
            refine ⟨4326446705194458307127389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5768595606925944409503185 4326446705194458307127389)
            ·
              refine ⟨1622417514447921865172771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4326446705194458307127389 1622417514447921865172771)
              ·
                refine ⟨2433626271671882797759157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622417514447921865172771 2433626271671882797759157)
                ·
                  refine ⟨228152462969239012289921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2433626271671882797759157 228152462969239012289921)
                  ·
                    rfl

theorem cell21_999732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_999732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999732 prefixEnd_999732 := by exact prefixLift 999732
  have htrace : WordTrace (prefixWord ++ tailWord_999732) baseStart_999732 baseEnd_999732 := by
    simpa [prefixWord, tailWord_999732, baseEnd_999732] using wordTrace_append hprefix tailTrace_999732
  have hstable : (prefixWord ++ tailWord_999732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999732).length < 2 ^ (prefixWord ++ tailWord_999732).sum := by decide
  have hdescent : baseEnd_999732 < baseStart_999732 := by decide
  rcases family_descends (prefixWord ++ tailWord_999732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999901 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 3]
def baseStart_999901 : Nat := 118140960795 + 999901 * 2 ^ 59
def prefixEnd_999901 : Nat := 4983230072969 + 3 ^ 40 * 999901 * 2
def baseEnd_999901 : Nat := 228191031071732273972909

theorem tailTrace_999901 : CollatzResearch.WordTrace tailWord_999901 prefixEnd_999901 228191031071732273972909 := by
  unfold tailWord_999901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36469385550536921340255557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24312923700357947560170371 36469385550536921340255557)
  ·
    refine ⟨6838009790725672751297917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36469385550536921340255557 6838009790725672751297917)
    ·
      refine ⟨2564253671522127281736719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6838009790725672751297917 2564253671522127281736719)
      ·
        refine ⟨3846380507283190922605079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564253671522127281736719 3846380507283190922605079)
        ·
          refine ⟨5769570760924786383907619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846380507283190922605079 5769570760924786383907619)
          ·
            refine ⟨8654356141387179575861429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769570760924786383907619 8654356141387179575861429)
            ·
              refine ⟨811345888255048085237009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8654356141387179575861429 811345888255048085237009)
              ·
                refine ⟨608509416191286063927757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811345888255048085237009 608509416191286063927757)
                ·
                  refine ⟨228191031071732273972909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608509416191286063927757 228191031071732273972909)
                  ·
                    rfl

theorem cell21_999901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_999901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999901 prefixEnd_999901 := by exact prefixLift 999901
  have htrace : WordTrace (prefixWord ++ tailWord_999901) baseStart_999901 baseEnd_999901 := by
    simpa [prefixWord, tailWord_999901, baseEnd_999901] using wordTrace_append hprefix tailTrace_999901
  have hstable : (prefixWord ++ tailWord_999901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999901).length < 2 ^ (prefixWord ++ tailWord_999901).sum := by decide
  have hdescent : baseEnd_999901 < baseStart_999901 := by decide
  rcases family_descends (prefixWord ++ tailWord_999901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999912 : List Nat := [2, 1, 4, 1, 1, 4, 2, 6]
def baseStart_999912 : Nat := 118140960795 + 999912 * 2 ^ 59
def prefixEnd_999912 : Nat := 4983230072969 + 3 ^ 40 * 999912 * 2
def baseEnd_999912 : Nat := 76064513807199566429851

theorem tailTrace_999912 : CollatzResearch.WordTrace tailWord_999912 prefixEnd_999912 76064513807199566429851 := by
  unfold tailWord_999912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234893376748535109452995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24313191168998046812603993 18234893376748535109452995)
  ·
    refine ⟨27352340065122802664179493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18234893376748535109452995 27352340065122802664179493)
    ·
      refine ⟨5128563762210525499533655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27352340065122802664179493 5128563762210525499533655)
      ·
        refine ⟨7692845643315788249300483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128563762210525499533655 7692845643315788249300483)
        ·
          refine ⟨11539268464973682373950725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692845643315788249300483 11539268464973682373950725)
          ·
            refine ⟨2163612837182565445115761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11539268464973682373950725 2163612837182565445115761)
            ·
              refine ⟨1622709627886924083836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163612837182565445115761 1622709627886924083836821)
              ·
                refine ⟨76064513807199566429851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1622709627886924083836821 76064513807199566429851)
                ·
                  rfl

theorem cell21_999912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_999912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999912 prefixEnd_999912 := by exact prefixLift 999912
  have htrace : WordTrace (prefixWord ++ tailWord_999912) baseStart_999912 baseEnd_999912 := by
    simpa [prefixWord, tailWord_999912, baseEnd_999912] using wordTrace_append hprefix tailTrace_999912
  have hstable : (prefixWord ++ tailWord_999912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999912).length < 2 ^ (prefixWord ++ tailWord_999912).sum := by decide
  have hdescent : baseEnd_999912 < baseStart_999912 := by decide
  rcases family_descends (prefixWord ++ tailWord_999912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999960 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_999960 : Nat := 118140960795 + 999960 * 2 ^ 59
def prefixEnd_999960 : Nat := 4983230072969 + 3 ^ 40 * 999960 * 2
def baseEnd_999960 : Nat := 228204495675561282489455

theorem tailTrace_999960 : CollatzResearch.WordTrace tailWord_999960 prefixEnd_999960 228204495675561282489455 := by
  unfold tailWord_999960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235768728661587208326667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24314358304882116277768889 18235768728661587208326667)
  ·
    refine ⟨27353653092992380812490001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18235768728661587208326667 27353653092992380812490001)
    ·
      refine ⟨20515239819744285609367501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27353653092992380812490001 20515239819744285609367501)
      ·
        refine ⟨7693214932404107103512813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20515239819744285609367501 7693214932404107103512813)
        ·
          refine ⟨2884955599651540163817305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7693214932404107103512813 2884955599651540163817305)
          ·
            refine ⟨2163716699738655122862979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884955599651540163817305 2163716699738655122862979)
            ·
              refine ⟨3245575049607982684294469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163716699738655122862979 3245575049607982684294469)
              ·
                refine ⟨608545321801496753305213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3245575049607982684294469 608545321801496753305213)
                ·
                  refine ⟨228204495675561282489455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608545321801496753305213 228204495675561282489455)
                  ·
                    rfl

theorem cell21_999960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_999960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_999960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_999960 prefixEnd_999960 := by exact prefixLift 999960
  have htrace : WordTrace (prefixWord ++ tailWord_999960) baseStart_999960 baseEnd_999960 := by
    simpa [prefixWord, tailWord_999960, baseEnd_999960] using wordTrace_append hprefix tailTrace_999960
  have hstable : (prefixWord ++ tailWord_999960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999960).length < 2 ^ (prefixWord ++ tailWord_999960).sum := by decide
  have hdescent : baseEnd_999960 < baseStart_999960 := by decide
  rcases family_descends (prefixWord ++ tailWord_999960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000084 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1000084 : Nat := 118140960795 + 1000084 * 2 ^ 59
def prefixEnd_1000084 : Nat := 4983230072969 + 3 ^ 40 * 1000084 * 2
def baseEnd_1000084 : Nat := 228232794164964622422535

theorem tailTrace_1000084 : CollatzResearch.WordTrace tailWord_1000084 prefixEnd_1000084 228232794164964622422535 := by
  unfold tailWord_1000084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238030054436971797083653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24317373405915962396111537 18238030054436971797083653)
  ·
    refine ⟨3419630635206932211953185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18238030054436971797083653 3419630635206932211953185)
    ·
      refine ⟨2564722976405199158964889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3419630635206932211953185 2564722976405199158964889)
      ·
        refine ⟨1923542232303899369223667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564722976405199158964889 1923542232303899369223667)
        ·
          refine ⟨2885313348455849053835501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923542232303899369223667 2885313348455849053835501)
          ·
            refine ⟨1081992505670943395188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2885313348455849053835501 1081992505670943395188313)
            ·
              refine ⟨811494379253207546391235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081992505670943395188313 811494379253207546391235)
              ·
                refine ⟨1217241568879811319586853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811494379253207546391235 1217241568879811319586853)
                ·
                  refine ⟨228232794164964622422535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217241568879811319586853 228232794164964622422535)
                  ·
                    rfl

theorem cell21_1000084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1000084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000084 prefixEnd_1000084 := by exact prefixLift 1000084
  have htrace : WordTrace (prefixWord ++ tailWord_1000084) baseStart_1000084 baseEnd_1000084 := by
    simpa [prefixWord, tailWord_1000084, baseEnd_1000084] using wordTrace_append hprefix tailTrace_1000084
  have hstable : (prefixWord ++ tailWord_1000084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000084).length < 2 ^ (prefixWord ++ tailWord_1000084).sum := by decide
  have hdescent : baseEnd_1000084 < baseStart_1000084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000126 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1000126 : Nat := 118140960795 + 1000126 * 2 ^ 59
def prefixEnd_1000126 : Nat := 4983230072969 + 3 ^ 40 * 1000126 * 2
def baseEnd_1000126 : Nat := 228242379137181882722449

theorem tailTrace_1000126 : CollatzResearch.WordTrace tailWord_1000126 prefixEnd_1000126 228242379137181882722449 := by
  unfold tailWord_1000126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559698996840223095899529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24318394649814523178130821 4559698996840223095899529)
  ·
    refine ⟨3419774247630167321924647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4559698996840223095899529 3419774247630167321924647)
    ·
      refine ⟨5129661371445250982886971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419774247630167321924647 5129661371445250982886971)
      ·
        refine ⟨7694492057167876474330457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129661371445250982886971 7694492057167876474330457)
        ·
          refine ⟨5770869042875907355747843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7694492057167876474330457 5770869042875907355747843)
          ·
            refine ⟨8656303564313861033621765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770869042875907355747843 8656303564313861033621765)
            ·
              refine ⟨1623056918308848943804081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8656303564313861033621765 1623056918308848943804081)
              ·
                refine ⟨1217292688731636707853061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623056918308848943804081 1217292688731636707853061)
                ·
                  refine ⟨228242379137181882722449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217292688731636707853061 228242379137181882722449)
                  ·
                    rfl

theorem cell21_1000126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1000126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000126 prefixEnd_1000126 := by exact prefixLift 1000126
  have htrace : WordTrace (prefixWord ++ tailWord_1000126) baseStart_1000126 baseEnd_1000126 := by
    simpa [prefixWord, tailWord_1000126, baseEnd_1000126] using wordTrace_append hprefix tailTrace_1000126
  have hstable : (prefixWord ++ tailWord_1000126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000126).length < 2 ^ (prefixWord ++ tailWord_1000126).sum := by decide
  have hdescent : baseEnd_1000126 < baseStart_1000126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000137 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1000137 : Nat := 118140960795 + 1000137 * 2 ^ 59
def prefixEnd_1000137 : Nat := 4983230072969 + 3 ^ 40 * 1000137 * 2
def baseEnd_1000137 : Nat := 228244889487048308039093

theorem tailTrace_1000137 : CollatzResearch.WordTrace tailWord_1000137 prefixEnd_1000137 228244889487048308039093 := by
  unfold tailWord_1000137
  simp only [CollatzResearch.WordTrace]
  refine ⟨36477993177681933645846665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24318662118454622430564443 36477993177681933645846665)
  ·
    refine ⟨27358494883261450234384999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36477993177681933645846665 27358494883261450234384999)
    ·
      refine ⟨41037742324892175351577499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27358494883261450234384999 41037742324892175351577499)
      ·
        refine ⟨61556613487338263027366249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41037742324892175351577499 61556613487338263027366249)
        ·
          refine ⟨46167460115503697270524687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61556613487338263027366249 46167460115503697270524687)
          ·
            refine ⟨69251190173255545905787031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46167460115503697270524687 69251190173255545905787031)
            ·
              refine ⟨103876785259883318858680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69251190173255545905787031 103876785259883318858680547)
              ·
                refine ⟨155815177889824978288020821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103876785259883318858680547 155815177889824978288020821)
                ·
                  refine ⟨228244889487048308039093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 155815177889824978288020821 228244889487048308039093)
                  ·
                    rfl

theorem cell21_1000137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1000137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000137 prefixEnd_1000137 := by exact prefixLift 1000137
  have htrace : WordTrace (prefixWord ++ tailWord_1000137) baseStart_1000137 baseEnd_1000137 := by
    simpa [prefixWord, tailWord_1000137, baseEnd_1000137] using wordTrace_append hprefix tailTrace_1000137
  have hstable : (prefixWord ++ tailWord_1000137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000137).length < 2 ^ (prefixWord ++ tailWord_1000137).sum := by decide
  have hdescent : baseEnd_1000137 < baseStart_1000137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000140 : List Nat := [2, 2, 1, 5, 1, 1, 3, 6]
def baseStart_1000140 : Nat := 118140960795 + 1000140 * 2 ^ 59
def prefixEnd_1000140 : Nat := 4983230072969 + 3 ^ 40 * 1000140 * 2
def baseEnd_1000140 : Nat := 76081858042640323163029

theorem tailTrace_1000140 : CollatzResearch.WordTrace tailWord_1000140 prefixEnd_1000140 76081858042640323163029 := by
  unfold tailWord_1000140
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239051298335532579102937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24318735064447376772137249 18239051298335532579102937)
  ·
    refine ⟨13679288473751649434327203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18239051298335532579102937 13679288473751649434327203)
    ·
      refine ⟨20518932710627474151490805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13679288473751649434327203 20518932710627474151490805)
      ·
        refine ⟨1923649941621325701702263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20518932710627474151490805 1923649941621325701702263)
        ·
          refine ⟨2885474912431988552553395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923649941621325701702263 2885474912431988552553395)
          ·
            refine ⟨4328212368647982828830093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885474912431988552553395 4328212368647982828830093)
            ·
              refine ⟨1623079638242993560811285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4328212368647982828830093 1623079638242993560811285)
              ·
                refine ⟨76081858042640323163029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1623079638242993560811285 76081858042640323163029)
                ·
                  rfl

theorem cell21_1000140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_1000140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000140 prefixEnd_1000140 := by exact prefixLift 1000140
  have htrace : WordTrace (prefixWord ++ tailWord_1000140) baseStart_1000140 baseEnd_1000140 := by
    simpa [prefixWord, tailWord_1000140, baseEnd_1000140] using wordTrace_append hprefix tailTrace_1000140
  have hstable : (prefixWord ++ tailWord_1000140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000140).length < 2 ^ (prefixWord ++ tailWord_1000140).sum := by decide
  have hdescent : baseEnd_1000140 < baseStart_1000140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000154 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_1000154 : Nat := 118140960795 + 1000154 * 2 ^ 59
def prefixEnd_1000154 : Nat := 4983230072969 + 3 ^ 40 * 1000154 * 2
def baseEnd_1000154 : Nat := 228248769118660056255725

theorem tailTrace_1000154 : CollatzResearch.WordTrace tailWord_1000154 prefixEnd_1000154 228248769118660056255725 := by
  unfold tailWord_1000154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119653304655086387303879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24319075479080230366143677 9119653304655086387303879)
  ·
    refine ⟨13679479956982629580955819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119653304655086387303879 13679479956982629580955819)
    ·
      refine ⟨20519219935473944371433729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13679479956982629580955819 20519219935473944371433729)
      ·
        refine ⟨15389414951605458278575297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20519219935473944371433729 15389414951605458278575297)
        ·
          refine ⟨11542061213704093708931473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15389414951605458278575297 11542061213704093708931473)
          ·
            refine ⟨8656545910278070281698605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542061213704093708931473 8656545910278070281698605)
            ·
              refine ⟨3246204716354276355636977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8656545910278070281698605 3246204716354276355636977)
              ·
                refine ⟨2434653537265707266727733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246204716354276355636977 2434653537265707266727733)
                ·
                  refine ⟨228248769118660056255725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2434653537265707266727733 228248769118660056255725)
                  ·
                    rfl

theorem cell21_1000154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_1000154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000154 prefixEnd_1000154 := by exact prefixLift 1000154
  have htrace : WordTrace (prefixWord ++ tailWord_1000154) baseStart_1000154 baseEnd_1000154 := by
    simpa [prefixWord, tailWord_1000154, baseEnd_1000154] using wordTrace_append hprefix tailTrace_1000154
  have hstable : (prefixWord ++ tailWord_1000154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000154).length < 2 ^ (prefixWord ++ tailWord_1000154).sum := by decide
  have hdescent : baseEnd_1000154 < baseStart_1000154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000202 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_1000202 : Nat := 118140960795 + 1000202 * 2 ^ 59
def prefixEnd_1000202 : Nat := 4983230072969 + 3 ^ 40 * 1000202 * 2
def baseEnd_1000202 : Nat := 228259723372622639455627

theorem tailTrace_1000202 : CollatzResearch.WordTrace tailWord_1000202 prefixEnd_1000202 228259723372622639455627 := by
  unfold tailWord_1000202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120090980611612436740715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24320242614964299831308573 9120090980611612436740715)
  ·
    refine ⟨13680136470917418655111073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120090980611612436740715 13680136470917418655111073)
    ·
      refine ⟨10260102353188063991333305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13680136470917418655111073 10260102353188063991333305)
      ·
        refine ⟨7695076764891047993499979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10260102353188063991333305 7695076764891047993499979)
        ·
          refine ⟨11542615147336571990249969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695076764891047993499979 11542615147336571990249969)
          ·
            refine ⟨8656961360502428992687477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542615147336571990249969 8656961360502428992687477)
            ·
              refine ⟨811590127547102718064451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8656961360502428992687477 811590127547102718064451)
              ·
                refine ⟨1217385191320654077096677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811590127547102718064451 1217385191320654077096677)
                ·
                  refine ⟨228259723372622639455627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217385191320654077096677 228259723372622639455627)
                  ·
                    rfl

theorem cell21_1000202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_1000202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000202 prefixEnd_1000202 := by exact prefixLift 1000202
  have htrace : WordTrace (prefixWord ++ tailWord_1000202) baseStart_1000202 baseEnd_1000202 := by
    simpa [prefixWord, tailWord_1000202, baseEnd_1000202] using wordTrace_append hprefix tailTrace_1000202
  have hstable : (prefixWord ++ tailWord_1000202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000202).length < 2 ^ (prefixWord ++ tailWord_1000202).sum := by decide
  have hdescent : baseEnd_1000202 < baseStart_1000202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000289 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1000289 : Nat := 118140960795 + 1000289 * 2 ^ 59
def prefixEnd_1000289 : Nat := 4983230072969 + 3 ^ 40 * 1000289 * 2
def baseEnd_1000289 : Nat := 228279577957929821505449

theorem tailTrace_1000289 : CollatzResearch.WordTrace tailWord_1000289 prefixEnd_1000289 228279577957929821505449 := by
  unfold tailWord_1000289
  simp only [CollatzResearch.WordTrace]
  refine ⟨36483537073131263605379921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24322358048754175736919947 36483537073131263605379921)
  ·
    refine ⟨27362652804848447704034941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36483537073131263605379921 27362652804848447704034941)
    ·
      refine ⟨10260994801818167889013103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27362652804848447704034941 10260994801818167889013103)
      ·
        refine ⟨15391492202727251833519655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260994801818167889013103 15391492202727251833519655)
        ·
          refine ⟨23087238304090877750279483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15391492202727251833519655 23087238304090877750279483)
          ·
            refine ⟨34630857456136316625419225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23087238304090877750279483 34630857456136316625419225)
            ·
              refine ⟨25973143092102237469064419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34630857456136316625419225 25973143092102237469064419)
              ·
                refine ⟨38959714638153356203596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25973143092102237469064419 38959714638153356203596629)
                ·
                  refine ⟨228279577957929821505449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38959714638153356203596629 228279577957929821505449)
                  ·
                    rfl

theorem cell21_1000289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1000289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000289 prefixEnd_1000289 := by exact prefixLift 1000289
  have htrace : WordTrace (prefixWord ++ tailWord_1000289) baseStart_1000289 baseEnd_1000289 := by
    simpa [prefixWord, tailWord_1000289, baseEnd_1000289] using wordTrace_append hprefix tailTrace_1000289
  have hstable : (prefixWord ++ tailWord_1000289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000289).length < 2 ^ (prefixWord ++ tailWord_1000289).sum := by decide
  have hdescent : baseEnd_1000289 < baseStart_1000289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000340 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1000340 : Nat := 118140960795 + 1000340 * 2 ^ 59
def prefixEnd_1000340 : Nat := 4983230072969 + 3 ^ 40 * 1000340 * 2
def baseEnd_1000340 : Nat := 228291216852765066155345

theorem tailTrace_1000340 : CollatzResearch.WordTrace tailWord_1000340 prefixEnd_1000340 228291216852765066155345 := by
  unfold tailWord_1000340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242698597973249657743237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24323598130630999543657649 18242698597973249657743237)
  ·
    refine ⟨3420505987119984310826857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18242698597973249657743237 3420505987119984310826857)
    ·
      refine ⟨2565379490339988233120143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3420505987119984310826857 2565379490339988233120143)
      ·
        refine ⟨3848069235509982349680215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565379490339988233120143 3848069235509982349680215)
        ·
          refine ⟨5772103853264973524520323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848069235509982349680215 5772103853264973524520323)
          ·
            refine ⟨8658155779897460286780485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772103853264973524520323 8658155779897460286780485)
            ·
              refine ⟨1623404208730773803771341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8658155779897460286780485 1623404208730773803771341)
              ·
                refine ⟨608776578274040176414253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623404208730773803771341 608776578274040176414253)
                ·
                  refine ⟨228291216852765066155345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608776578274040176414253 228291216852765066155345)
                  ·
                    rfl

theorem cell21_1000340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1000340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000340 prefixEnd_1000340 := by exact prefixLift 1000340
  have htrace : WordTrace (prefixWord ++ tailWord_1000340) baseStart_1000340 baseEnd_1000340 := by
    simpa [prefixWord, tailWord_1000340, baseEnd_1000340] using wordTrace_append hprefix tailTrace_1000340
  have hstable : (prefixWord ++ tailWord_1000340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000340).length < 2 ^ (prefixWord ++ tailWord_1000340).sum := by decide
  have hdescent : baseEnd_1000340 < baseStart_1000340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000351 : List Nat := [1, 1, 2, 5, 2, 2, 8]
def baseStart_1000351 : Nat := 118140960795 + 1000351 * 2 ^ 59
def prefixEnd_1000351 : Nat := 4983230072969 + 3 ^ 40 * 1000351 * 2
def baseEnd_1000351 : Nat := 25365969689181276830221

theorem tailTrace_1000351 : CollatzResearch.WordTrace tailWord_1000351 prefixEnd_1000351 25365969689181276830221 := by
  unfold tailWord_1000351
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485798398906648194136907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24323865599271098796091271 36485798398906648194136907)
  ·
    refine ⟨54728697598359972291205361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36485798398906648194136907 54728697598359972291205361)
    ·
      refine ⟨41046523198769979218404021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54728697598359972291205361 41046523198769979218404021)
      ·
        refine ⟨3848111549884685551725377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41046523198769979218404021 3848111549884685551725377)
        ·
          refine ⟨2886083662413514163794033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848111549884685551725377 2886083662413514163794033)
          ·
            refine ⟨2164562746810135622845525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886083662413514163794033 2164562746810135622845525)
            ·
              refine ⟨25365969689181276830221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2164562746810135622845525 25365969689181276830221)
              ·
                rfl

theorem cell21_1000351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_1000351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000351 prefixEnd_1000351 := by exact prefixLift 1000351
  have htrace : WordTrace (prefixWord ++ tailWord_1000351) baseStart_1000351 baseEnd_1000351 := by
    simpa [prefixWord, tailWord_1000351, baseEnd_1000351] using wordTrace_append hprefix tailTrace_1000351
  have hstable : (prefixWord ++ tailWord_1000351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000351).length < 2 ^ (prefixWord ++ tailWord_1000351).sum := by decide
  have hdescent : baseEnd_1000351 < baseStart_1000351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000354 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1000354 : Nat := 118140960795 + 1000354 * 2 ^ 59
def prefixEnd_1000354 : Nat := 4983230072969 + 3 ^ 40 * 1000354 * 2
def baseEnd_1000354 : Nat := 228294411843504152921983

theorem tailTrace_1000354 : CollatzResearch.WordTrace tailWord_1000354 prefixEnd_1000354 228294411843504152921983 := by
  unfold tailWord_1000354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121476954473944926624029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24323938545263853137664077 9121476954473944926624029)
  ·
    refine ⟨3420553857927729347484011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9121476954473944926624029 3420553857927729347484011)
    ·
      refine ⟨5130830786891594021226017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420553857927729347484011 5130830786891594021226017)
      ·
        refine ⟨3848123090168695515919513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5130830786891594021226017 3848123090168695515919513)
        ·
          refine ⟨2886092317626521636939635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848123090168695515919513 2886092317626521636939635)
          ·
            refine ⟨4329138476439782455409453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886092317626521636939635 4329138476439782455409453)
            ·
              refine ⟨1623426928664918420778545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4329138476439782455409453 1623426928664918420778545)
              ·
                refine ⟨1217570196498688815583909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623426928664918420778545 1217570196498688815583909)
                ·
                  refine ⟨228294411843504152921983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217570196498688815583909 228294411843504152921983)
                  ·
                    rfl

theorem cell21_1000354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1000354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000354 prefixEnd_1000354 := by exact prefixLift 1000354
  have htrace : WordTrace (prefixWord ++ tailWord_1000354) baseStart_1000354 baseEnd_1000354 := by
    simpa [prefixWord, tailWord_1000354, baseEnd_1000354] using wordTrace_append hprefix tailTrace_1000354
  have hstable : (prefixWord ++ tailWord_1000354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000354).length < 2 ^ (prefixWord ++ tailWord_1000354).sum := by decide
  have hdescent : baseEnd_1000354 < baseStart_1000354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000382 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1000382 : Nat := 118140960795 + 1000382 * 2 ^ 59
def prefixEnd_1000382 : Nat := 4983230072969 + 3 ^ 40 * 1000382 * 2
def baseEnd_1000382 : Nat := 228300801824982326455259

theorem tailTrace_1000382 : CollatzResearch.WordTrace tailWord_1000382 prefixEnd_1000382 228300801824982326455259 := by
  unfold tailWord_1000382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560866132724292561064425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24324619374529560325676933 4560866132724292561064425)
  ·
    refine ⟨3420649599543219420798319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4560866132724292561064425 3420649599543219420798319)
    ·
      refine ⟨5130974399314829131197479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420649599543219420798319 5130974399314829131197479)
      ·
        refine ⟨7696461598972243696796219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130974399314829131197479 7696461598972243696796219)
        ·
          refine ⟨11544692398458365545194329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696461598972243696796219 11544692398458365545194329)
          ·
            refine ⟨8658519298843774158895747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11544692398458365545194329 8658519298843774158895747)
            ·
              refine ⟨12987778948265661238343621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658519298843774158895747 12987778948265661238343621)
              ·
                refine ⟨2435208552799811482189429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12987778948265661238343621 2435208552799811482189429)
                ·
                  refine ⟨228300801824982326455259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435208552799811482189429 228300801824982326455259)
                  ·
                    rfl

theorem cell21_1000382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1000382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000382 prefixEnd_1000382 := by exact prefixLift 1000382
  have htrace : WordTrace (prefixWord ++ tailWord_1000382) baseStart_1000382 baseEnd_1000382 := by
    simpa [prefixWord, tailWord_1000382, baseEnd_1000382] using wordTrace_append hprefix tailTrace_1000382
  have hstable : (prefixWord ++ tailWord_1000382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000382).length < 2 ^ (prefixWord ++ tailWord_1000382).sum := by decide
  have hdescent : baseEnd_1000382 < baseStart_1000382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000396 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1000396 : Nat := 118140960795 + 1000396 * 2 ^ 59
def prefixEnd_1000396 : Nat := 4983230072969 + 3 ^ 40 * 1000396 * 2
def baseEnd_1000396 : Nat := 228303996815721413221897

theorem tailTrace_1000396 : CollatzResearch.WordTrace tailWord_1000396 prefixEnd_1000396 228303996815721413221897 := by
  unfold tailWord_1000396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243719841871810439762521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24324959789162413919683361 18243719841871810439762521)
  ·
    refine ⟨13682789881403857829821891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18243719841871810439762521 13682789881403857829821891)
    ·
      refine ⟨20524184822105786744732837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682789881403857829821891 20524184822105786744732837)
      ·
        refine ⟨3848284654144835014637407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20524184822105786744732837 3848284654144835014637407)
        ·
          refine ⟨5772426981217252521956111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848284654144835014637407 5772426981217252521956111)
          ·
            refine ⟨8658640471825878782934167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772426981217252521956111 8658640471825878782934167)
            ·
              refine ⟨12987960707738818174401251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658640471825878782934167 12987960707738818174401251)
              ·
                refine ⟨19481941061608227261601877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987960707738818174401251 19481941061608227261601877)
                ·
                  refine ⟨228303996815721413221897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19481941061608227261601877 228303996815721413221897)
                  ·
                    rfl

theorem cell21_1000396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1000396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000396 prefixEnd_1000396 := by exact prefixLift 1000396
  have htrace : WordTrace (prefixWord ++ tailWord_1000396) baseStart_1000396 baseEnd_1000396 := by
    simpa [prefixWord, tailWord_1000396, baseEnd_1000396] using wordTrace_append hprefix tailTrace_1000396
  have hstable : (prefixWord ++ tailWord_1000396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000396).length < 2 ^ (prefixWord ++ tailWord_1000396).sum := by decide
  have hdescent : baseEnd_1000396 < baseStart_1000396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000399 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 3]
def baseStart_1000399 : Nat := 118140960795 + 1000399 * 2 ^ 59
def prefixEnd_1000399 : Nat := 4983230072969 + 3 ^ 40 * 1000399 * 2
def baseEnd_1000399 : Nat := 228304681456594074671891

theorem tailTrace_1000399 : CollatzResearch.WordTrace tailWord_1000399 prefixEnd_1000399 228304681456594074671891 := by
  unfold tailWord_1000399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36487549102732752391884251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24325032735155168261256167 36487549102732752391884251)
  ·
    refine ⟨54731323654099128587826377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36487549102732752391884251 54731323654099128587826377)
    ·
      refine ⟨41048492740574346440869783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54731323654099128587826377 41048492740574346440869783)
      ·
        refine ⟨61572739110861519661304675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41048492740574346440869783 61572739110861519661304675)
        ·
          refine ⟨92359108666292279491957013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61572739110861519661304675 92359108666292279491957013)
          ·
            refine ⟨4329333218732450601185485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92359108666292279491957013 4329333218732450601185485)
            ·
              refine ⟨1623499957024668975444557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4329333218732450601185485 1623499957024668975444557)
              ·
                refine ⟨608812483884250865791709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623499957024668975444557 608812483884250865791709)
                ·
                  refine ⟨228304681456594074671891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608812483884250865791709 228304681456594074671891)
                  ·
                    rfl

theorem cell21_1000399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].length) (baseStart_1000399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000399 prefixEnd_1000399 := by exact prefixLift 1000399
  have htrace : WordTrace (prefixWord ++ tailWord_1000399) baseStart_1000399 baseEnd_1000399 := by
    simpa [prefixWord, tailWord_1000399, baseEnd_1000399] using wordTrace_append hprefix tailTrace_1000399
  have hstable : (prefixWord ++ tailWord_1000399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000399).length < 2 ^ (prefixWord ++ tailWord_1000399).sum := by decide
  have hdescent : baseEnd_1000399 < baseStart_1000399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000413 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1000413 : Nat := 118140960795 + 1000413 * 2 ^ 59
def prefixEnd_1000413 : Nat := 4983230072969 + 3 ^ 40 * 1000413 * 2
def baseEnd_1000413 : Nat := 228307876447333161438529

theorem tailTrace_1000413 : CollatzResearch.WordTrace tailWord_1000413 prefixEnd_1000413 228307876447333161438529 := by
  unfold tailWord_1000413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488059724682032782893893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24325373149788021855262595 36488059724682032782893893)
  ·
    refine ⟨6841511198377881146792605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36488059724682032782893893 6841511198377881146792605)
    ·
      refine ⟨2565566699391705430047227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6841511198377881146792605 2565566699391705430047227)
      ·
        refine ⟨3848350049087558145070841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565566699391705430047227 3848350049087558145070841)
        ·
          refine ⟨2886262536815668608803131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848350049087558145070841 2886262536815668608803131)
          ·
            refine ⟨4329393805223502913204697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886262536815668608803131 4329393805223502913204697)
            ·
              refine ⟨3247045353917627184903523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329393805223502913204697 3247045353917627184903523)
              ·
                refine ⟨4870568030876440777355285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247045353917627184903523 4870568030876440777355285)
                ·
                  refine ⟨228307876447333161438529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4870568030876440777355285 228307876447333161438529)
                  ·
                    rfl

theorem cell21_1000413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1000413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000413 prefixEnd_1000413 := by exact prefixLift 1000413
  have htrace : WordTrace (prefixWord ++ tailWord_1000413) baseStart_1000413 baseEnd_1000413 := by
    simpa [prefixWord, tailWord_1000413, baseEnd_1000413] using wordTrace_append hprefix tailTrace_1000413
  have hstable : (prefixWord ++ tailWord_1000413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000413).length < 2 ^ (prefixWord ++ tailWord_1000413).sum := by decide
  have hdescent : baseEnd_1000413 < baseStart_1000413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000430 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1000430 : Nat := 118140960795 + 1000430 * 2 ^ 59
def prefixEnd_1000430 : Nat := 4983230072969 + 3 ^ 40 * 1000430 * 2
def baseEnd_1000430 : Nat := 228311756078944909655161

theorem tailTrace_1000430 : CollatzResearch.WordTrace tailWord_1000430 prefixEnd_1000430 228311756078944909655161 := by
  unfold tailWord_1000430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561084970702555585782843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24325786510413629790841829 4561084970702555585782843)
  ·
    refine ⟨6841627456053833378674265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561084970702555585782843 6841627456053833378674265)
    ·
      refine ⟨5131220592040375034005699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6841627456053833378674265 5131220592040375034005699)
      ·
        refine ⟨7696830888060562551008549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131220592040375034005699 7696830888060562551008549)
        ·
          refine ⟨1443155791511355478314103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7696830888060562551008549 1443155791511355478314103)
          ·
            refine ⟨2164733687267033217471155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443155791511355478314103 2164733687267033217471155)
            ·
              refine ⟨3247100530900549826206733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164733687267033217471155 3247100530900549826206733)
              ·
                refine ⟨1217662699087706184827525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3247100530900549826206733 1217662699087706184827525)
                ·
                  refine ⟨228311756078944909655161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217662699087706184827525 228311756078944909655161)
                  ·
                    rfl

theorem cell21_1000430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1000430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000430 prefixEnd_1000430 := by exact prefixLift 1000430
  have htrace : WordTrace (prefixWord ++ tailWord_1000430) baseStart_1000430 baseEnd_1000430 := by
    simpa [prefixWord, tailWord_1000430, baseEnd_1000430] using wordTrace_append hprefix tailTrace_1000430
  have hstable : (prefixWord ++ tailWord_1000430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000430).length < 2 ^ (prefixWord ++ tailWord_1000430).sum := by decide
  have hdescent : baseEnd_1000430 < baseStart_1000430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000441 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1000441 : Nat := 118140960795 + 1000441 * 2 ^ 59
def prefixEnd_1000441 : Nat := 4983230072969 + 3 ^ 40 * 1000441 * 2
def baseEnd_1000441 : Nat := 228314266428811334971805

theorem tailTrace_1000441 : CollatzResearch.WordTrace tailWord_1000441 prefixEnd_1000441 228314266428811334971805 := by
  unfold tailWord_1000441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489080968580593564913177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24326053979053729043275451 36489080968580593564913177)
  ·
    refine ⟨27366810726435445173684883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36489080968580593564913177 27366810726435445173684883)
    ·
      refine ⟨41050216089653167760527325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27366810726435445173684883 41050216089653167760527325)
      ·
        refine ⟨15393831033619937910197747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41050216089653167760527325 15393831033619937910197747)
        ·
          refine ⟨23090746550429906865296621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15393831033619937910197747 23090746550429906865296621)
          ·
            refine ⟨8659029956411215074486233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23090746550429906865296621 8659029956411215074486233)
            ·
              refine ⟨6494272467308411305864675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659029956411215074486233 6494272467308411305864675)
              ·
                refine ⟨9741408700962616958797013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494272467308411305864675 9741408700962616958797013)
                ·
                  refine ⟨228314266428811334971805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9741408700962616958797013 228314266428811334971805)
                  ·
                    rfl

theorem cell21_1000441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1000441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000441 prefixEnd_1000441 := by exact prefixLift 1000441
  have htrace : WordTrace (prefixWord ++ tailWord_1000441) baseStart_1000441 baseEnd_1000441 := by
    simpa [prefixWord, tailWord_1000441, baseEnd_1000441] using wordTrace_append hprefix tailTrace_1000441
  have hstable : (prefixWord ++ tailWord_1000441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000441).length < 2 ^ (prefixWord ++ tailWord_1000441).sum := by decide
  have hdescent : baseEnd_1000441 < baseStart_1000441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000644 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1000644 : Nat := 118140960795 + 1000644 * 2 ^ 59
def prefixEnd_1000644 : Nat := 4983230072969 + 3 ^ 40 * 1000644 * 2
def baseEnd_1000644 : Nat := 228360593794528093088057

theorem tailTrace_1000644 : CollatzResearch.WordTrace tailWord_1000644 prefixEnd_1000644 228360593794528093088057 := by
  unfold tailWord_1000644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248242493422579617276493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24330989991230106156368657 18248242493422579617276493)
  ·
    refine ⟨6843090935033467356478685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18248242493422579617276493 6843090935033467356478685)
    ·
      refine ⟨2566159100637550258679507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6843090935033467356478685 2566159100637550258679507)
      ·
        refine ⟨3849238650956325388019261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566159100637550258679507 3849238650956325388019261)
        ·
          refine ⟨1443464494108622020507223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3849238650956325388019261 1443464494108622020507223)
          ·
            refine ⟨2165196741162933030760835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443464494108622020507223 2165196741162933030760835)
            ·
              refine ⟨3247795111744399546141253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165196741162933030760835 3247795111744399546141253)
              ·
                refine ⟨608961583452074914901485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3247795111744399546141253 608961583452074914901485)
                ·
                  refine ⟨228360593794528093088057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608961583452074914901485 228360593794528093088057)
                  ·
                    rfl

theorem cell21_1000644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1000644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000644 prefixEnd_1000644 := by exact prefixLift 1000644
  have htrace : WordTrace (prefixWord ++ tailWord_1000644) baseStart_1000644 baseEnd_1000644 := by
    simpa [prefixWord, tailWord_1000644, baseEnd_1000644] using wordTrace_append hprefix tailTrace_1000644
  have hstable : (prefixWord ++ tailWord_1000644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000644).length < 2 ^ (prefixWord ++ tailWord_1000644).sum := by decide
  have hdescent : baseEnd_1000644 < baseStart_1000644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000714 : List Nat := [3, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1000714 : Nat := 118140960795 + 1000714 * 2 ^ 59
def prefixEnd_1000714 : Nat := 4983230072969 + 3 ^ 40 * 1000714 * 2
def baseEnd_1000714 : Nat := 76125522916074508973749

theorem tailTrace_1000714 : CollatzResearch.WordTrace tailWord_1000714 prefixEnd_1000714 76125522916074508973749 := by
  unfold tailWord_1000714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124759524147890297400299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24332692064394374126400797 9124759524147890297400299)
  ·
    refine ⟨13687139286221835446100449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124759524147890297400299 13687139286221835446100449)
    ·
      refine ⟨10265354464666376584575337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13687139286221835446100449 10265354464666376584575337)
      ·
        refine ⟨7699015848499782438431503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10265354464666376584575337 7699015848499782438431503)
        ·
          refine ⟨11548523772749673657647255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7699015848499782438431503 11548523772749673657647255)
          ·
            refine ⟨17322785659124510486470883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548523772749673657647255 17322785659124510486470883)
            ·
              refine ⟨25984178488686765729706325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322785659124510486470883 25984178488686765729706325)
              ·
                refine ⟨76125522916074508973749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25984178488686765729706325 76125522916074508973749)
                ·
                  rfl

theorem cell21_1000714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1000714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000714 prefixEnd_1000714 := by exact prefixLift 1000714
  have htrace : WordTrace (prefixWord ++ tailWord_1000714) baseStart_1000714 baseEnd_1000714 := by
    simpa [prefixWord, tailWord_1000714, baseEnd_1000714] using wordTrace_append hprefix tailTrace_1000714
  have hstable : (prefixWord ++ tailWord_1000714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000714).length < 2 ^ (prefixWord ++ tailWord_1000714).sum := by decide
  have hdescent : baseEnd_1000714 < baseStart_1000714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000807 : List Nat := [1, 1, 5, 1, 5, 8]
def baseStart_1000807 : Nat := 118140960795 + 1000807 * 2 ^ 59
def prefixEnd_1000807 : Nat := 4983230072969 + 3 ^ 40 * 1000807 * 2
def baseEnd_1000807 : Nat := 8459177504269482661891

theorem tailTrace_1000807 : CollatzResearch.WordTrace tailWord_1000807 prefixEnd_1000807 8459177504269482661891 := by
  unfold tailWord_1000807
  simp only [CollatzResearch.WordTrace]
  refine ⟨36502430085254638072736675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24334953390169758715157783 36502430085254638072736675)
  ·
    refine ⟨54753645127881957109105013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36502430085254638072736675 54753645127881957109105013)
    ·
      refine ⟨5133154230738933478978595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54753645127881957109105013 5133154230738933478978595)
      ·
        refine ⟨7699731346108400218467893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133154230738933478978595 7699731346108400218467893)
        ·
          refine ⟨721849813697662520481365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7699731346108400218467893 721849813697662520481365)
          ·
            refine ⟨8459177504269482661891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 721849813697662520481365 8459177504269482661891)
            ·
              rfl

theorem cell21_1000807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 8].length) (baseStart_1000807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000807 prefixEnd_1000807 := by exact prefixLift 1000807
  have htrace : WordTrace (prefixWord ++ tailWord_1000807) baseStart_1000807 baseEnd_1000807 := by
    simpa [prefixWord, tailWord_1000807, baseEnd_1000807] using wordTrace_append hprefix tailTrace_1000807
  have hstable : (prefixWord ++ tailWord_1000807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000807).length < 2 ^ (prefixWord ++ tailWord_1000807).sum := by decide
  have hdescent : baseEnd_1000807 < baseStart_1000807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000810 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1000810 : Nat := 118140960795 + 1000810 * 2 ^ 59
def prefixEnd_1000810 : Nat := 4983230072969 + 3 ^ 40 * 1000810 * 2
def baseEnd_1000810 : Nat := 228398477256148693321051

theorem tailTrace_1000810 : CollatzResearch.WordTrace tailWord_1000810 prefixEnd_1000810 228398477256148693321051 := by
  unfold tailWord_1000810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125634876060942396273971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24335026336162513056730589 9125634876060942396273971)
  ·
    refine ⟨13688452314091413594410957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9125634876060942396273971 13688452314091413594410957)
    ·
      refine ⟨5133169617784280097904109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13688452314091413594410957 5133169617784280097904109)
      ·
        refine ⟨1924938606669105036714041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5133169617784280097904109 1924938606669105036714041)
        ·
          refine ⟨1443703955001828777535531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924938606669105036714041 1443703955001828777535531)
          ·
            refine ⟨2165555932502743166303297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443703955001828777535531 2165555932502743166303297)
            ·
              refine ⟨1624166949377057374727473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165555932502743166303297 1624166949377057374727473)
              ·
                refine ⟨1218125212032793031045605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624166949377057374727473 1218125212032793031045605)
                ·
                  refine ⟨228398477256148693321051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218125212032793031045605 228398477256148693321051)
                  ·
                    rfl

theorem cell21_1000810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1000810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000810 prefixEnd_1000810 := by exact prefixLift 1000810
  have htrace : WordTrace (prefixWord ++ tailWord_1000810) baseStart_1000810 baseEnd_1000810 := by
    simpa [prefixWord, tailWord_1000810, baseEnd_1000810] using wordTrace_append hprefix tailTrace_1000810
  have hstable : (prefixWord ++ tailWord_1000810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000810).length < 2 ^ (prefixWord ++ tailWord_1000810).sum := by decide
  have hdescent : baseEnd_1000810 < baseStart_1000810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000900 : List Nat := [2, 3, 3, 2, 1, 1, 4, 5]
def baseStart_1000900 : Nat := 118140960795 + 1000900 * 2 ^ 59
def prefixEnd_1000900 : Nat := 4983230072969 + 3 ^ 40 * 1000900 * 2
def baseEnd_1000900 : Nat := 76139672160776178940289

theorem tailTrace_1000900 : CollatzResearch.WordTrace tailWord_1000900 prefixEnd_1000900 76139672160776178940289 := by
  unfold tailWord_1000900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18252911036958857477936077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24337214715945143303914769 18252911036958857477936077)
  ·
    refine ⟨6844841638859571554226029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18252911036958857477936077 6844841638859571554226029)
    ·
      refine ⟨2566815614572339332834761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6844841638859571554226029 2566815614572339332834761)
      ·
        refine ⟨1925111710929254499626071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566815614572339332834761 1925111710929254499626071)
        ·
          refine ⟨2887667566393881749439107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925111710929254499626071 2887667566393881749439107)
          ·
            refine ⟨4331501349590822624158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887667566393881749439107 4331501349590822624158661)
            ·
              refine ⟨812156503048279242029749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4331501349590822624158661 812156503048279242029749)
              ·
                refine ⟨76139672160776178940289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 812156503048279242029749 76139672160776178940289)
                ·
                  rfl

theorem cell21_1000900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_1000900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000900 prefixEnd_1000900 := by exact prefixLift 1000900
  have htrace : WordTrace (prefixWord ++ tailWord_1000900) baseStart_1000900 baseEnd_1000900 := by
    simpa [prefixWord, tailWord_1000900, baseEnd_1000900] using wordTrace_append hprefix tailTrace_1000900
  have hstable : (prefixWord ++ tailWord_1000900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000900).length < 2 ^ (prefixWord ++ tailWord_1000900).sum := by decide
  have hdescent : baseEnd_1000900 < baseStart_1000900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000911 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_1000911 : Nat := 118140960795 + 1000911 * 2 ^ 59
def prefixEnd_1000911 : Nat := 4983230072969 + 3 ^ 40 * 1000911 * 2
def baseEnd_1000911 : Nat := 228421526832194962137511

theorem tailTrace_1000911 : CollatzResearch.WordTrace tailWord_1000911 prefixEnd_1000911 228421526832194962137511 := by
  unfold tailWord_1000911
  simp only [CollatzResearch.WordTrace]
  refine ⟨36506223276877863834522587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24337482184585242556348391 36506223276877863834522587)
  ·
    refine ⟨54759334915316795751783881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36506223276877863834522587 54759334915316795751783881)
    ·
      refine ⟨41069501186487596813837911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54759334915316795751783881 41069501186487596813837911)
      ·
        refine ⟨61604251779731395220756867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41069501186487596813837911 61604251779731395220756867)
        ·
          refine ⟨92406377669597092831135301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61604251779731395220756867 92406377669597092831135301)
          ·
            refine ⟨17326195813049454905837869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92406377669597092831135301 17326195813049454905837869)
            ·
              refine ⟨6497323429893545589689201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17326195813049454905837869 6497323429893545589689201)
              ·
                refine ⟨4872992572420159192266901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497323429893545589689201 4872992572420159192266901)
                ·
                  refine ⟨228421526832194962137511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4872992572420159192266901 228421526832194962137511)
                  ·
                    rfl

theorem cell21_1000911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_1000911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000911 prefixEnd_1000911 := by exact prefixLift 1000911
  have htrace : WordTrace (prefixWord ++ tailWord_1000911) baseStart_1000911 baseEnd_1000911 := by
    simpa [prefixWord, tailWord_1000911, baseEnd_1000911] using wordTrace_append hprefix tailTrace_1000911
  have hstable : (prefixWord ++ tailWord_1000911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000911).length < 2 ^ (prefixWord ++ tailWord_1000911).sum := by decide
  have hdescent : baseEnd_1000911 < baseStart_1000911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000945 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 4]
def baseStart_1000945 : Nat := 118140960795 + 1000945 * 2 ^ 59
def prefixEnd_1000945 : Nat := 4983230072969 + 3 ^ 40 * 1000945 * 2
def baseEnd_1000945 : Nat := 228429286095418458570775

theorem tailTrace_1000945 : CollatzResearch.WordTrace tailWord_1000945 prefixEnd_1000945 228429286095418458570775 := by
  unfold tailWord_1000945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36507463358754687641260289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24338308905836458427506859 36507463358754687641260289)
  ·
    refine ⟨27380597519066015730945217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36507463358754687641260289 27380597519066015730945217)
    ·
      refine ⟨20535448139299511798208913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27380597519066015730945217 20535448139299511798208913)
      ·
        refine ⟨15401586104474633848656685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20535448139299511798208913 15401586104474633848656685)
        ·
          refine ⟨5775594789177987693246257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15401586104474633848656685 5775594789177987693246257)
          ·
            refine ⟨4331696091883490769934693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775594789177987693246257 4331696091883490769934693)
            ·
              refine ⟨812193017228154519362755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4331696091883490769934693 812193017228154519362755)
              ·
                refine ⟨1218289525842231779044133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812193017228154519362755 1218289525842231779044133)
                ·
                  refine ⟨228429286095418458570775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218289525842231779044133 228429286095418458570775)
                  ·
                    rfl

theorem cell21_1000945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_1000945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1000945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1000945 prefixEnd_1000945 := by exact prefixLift 1000945
  have htrace : WordTrace (prefixWord ++ tailWord_1000945) baseStart_1000945 baseEnd_1000945 := by
    simpa [prefixWord, tailWord_1000945, baseEnd_1000945] using wordTrace_append hprefix tailTrace_1000945
  have hstable : (prefixWord ++ tailWord_1000945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000945).length < 2 ^ (prefixWord ++ tailWord_1000945).sum := by decide
  have hdescent : baseEnd_1000945 < baseStart_1000945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001069 : List Nat := [1, 5, 1, 1, 5, 1, 2, 5]
def baseStart_1001069 : Nat := 118140960795 + 1001069 * 2 ^ 59
def prefixEnd_1001069 : Nat := 4983230072969 + 3 ^ 40 * 1001069 * 2
def baseEnd_1001069 : Nat := 76152528194940599501285

theorem tailTrace_1001069 : CollatzResearch.WordTrace tailWord_1001069 prefixEnd_1001069 76152528194940599501285 := by
  unfold tailWord_1001069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511986010305456818774261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24341324006870304545849507 36511986010305456818774261)
  ·
    refine ⟨3422998688466136576760087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36511986010305456818774261 3422998688466136576760087)
    ·
      refine ⟨5134498032699204865140131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422998688466136576760087 5134498032699204865140131)
      ·
        refine ⟨7701747049048807297710197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134498032699204865140131 7701747049048807297710197)
        ·
          refine ⟨722038785848325684160331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7701747049048807297710197 722038785848325684160331)
          ·
            refine ⟨1083058178772488526240497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722038785848325684160331 1083058178772488526240497)
            ·
              refine ⟨812293634079366394680373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083058178772488526240497 812293634079366394680373)
              ·
                refine ⟨76152528194940599501285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 812293634079366394680373 76152528194940599501285)
                ·
                  rfl

theorem cell21_1001069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].length) (baseStart_1001069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001069 prefixEnd_1001069 := by exact prefixLift 1001069
  have htrace : WordTrace (prefixWord ++ tailWord_1001069) baseStart_1001069 baseEnd_1001069 := by
    simpa [prefixWord, tailWord_1001069, baseEnd_1001069] using wordTrace_append hprefix tailTrace_1001069
  have hstable : (prefixWord ++ tailWord_1001069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001069).length < 2 ^ (prefixWord ++ tailWord_1001069).sum := by decide
  have hdescent : baseEnd_1001069 < baseStart_1001069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001184 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1001184 : Nat := 118140960795 + 1001184 * 2 ^ 59
def prefixEnd_1001184 : Nat := 4983230072969 + 3 ^ 40 * 1001184 * 2
def baseEnd_1001184 : Nat := 228483829151607154086953

theorem tailTrace_1001184 : CollatzResearch.WordTrace tailWord_1001184 prefixEnd_1001184 228483829151607154086953 := by
  unfold tailWord_1001184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258090202444415729605303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24344120269925887639473737 18258090202444415729605303)
  ·
    refine ⟨27387135303666623594407955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258090202444415729605303 27387135303666623594407955)
    ·
      refine ⟨41080702955499935391611933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27387135303666623594407955 41080702955499935391611933)
      ·
        refine ⟨15405263608312475771854475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41080702955499935391611933 15405263608312475771854475)
        ·
          refine ⟨23107895412468713657781713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15405263608312475771854475 23107895412468713657781713)
          ·
            refine ⟨17330921559351535243336285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23107895412468713657781713 17330921559351535243336285)
            ·
              refine ⟨6499095584756825716251107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17330921559351535243336285 6499095584756825716251107)
              ·
                refine ⟨9748643377135238574376661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499095584756825716251107 9748643377135238574376661)
                ·
                  refine ⟨228483829151607154086953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9748643377135238574376661 228483829151607154086953)
                  ·
                    rfl

theorem cell21_1001184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1001184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001184 prefixEnd_1001184 := by exact prefixLift 1001184
  have htrace : WordTrace (prefixWord ++ tailWord_1001184) baseStart_1001184 baseEnd_1001184 := by
    simpa [prefixWord, tailWord_1001184, baseEnd_1001184] using wordTrace_append hprefix tailTrace_1001184
  have hstable : (prefixWord ++ tailWord_1001184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001184).length < 2 ^ (prefixWord ++ tailWord_1001184).sum := by decide
  have hdescent : baseEnd_1001184 < baseStart_1001184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001204 : List Nat := [2, 6, 1, 1, 1, 2, 8]
def baseStart_1001204 : Nat := 118140960795 + 1001204 * 2 ^ 59
def prefixEnd_1001204 : Nat := 4983230072969 + 3 ^ 40 * 1001204 * 2
def baseEnd_1001204 : Nat := 25387599269343507083731

theorem tailTrace_1001204 : CollatzResearch.WordTrace tailWord_1001204 prefixEnd_1001204 25387599269343507083731 := by
  unfold tailWord_1001204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258454932408187437469333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24344606576544249916625777 18258454932408187437469333)
  ·
    refine ⟨855865074956633786131375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18258454932408187437469333 855865074956633786131375)
    ·
      refine ⟨1283797612434950679197063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855865074956633786131375 1283797612434950679197063)
      ·
        refine ⟨1925696418652426018795595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283797612434950679197063 1925696418652426018795595)
        ·
          refine ⟨2888544627978639028193393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925696418652426018795595 2888544627978639028193393)
          ·
            refine ⟨2166408470983979271145045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888544627978639028193393 2166408470983979271145045)
            ·
              refine ⟨25387599269343507083731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2166408470983979271145045 25387599269343507083731)
              ·
                rfl

theorem cell21_1001204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 8].length) (baseStart_1001204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001204 prefixEnd_1001204 := by exact prefixLift 1001204
  have htrace : WordTrace (prefixWord ++ tailWord_1001204) baseStart_1001204 baseEnd_1001204 := by
    simpa [prefixWord, tailWord_1001204, baseEnd_1001204] using wordTrace_append hprefix tailTrace_1001204
  have hstable : (prefixWord ++ tailWord_1001204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001204).length < 2 ^ (prefixWord ++ tailWord_1001204).sum := by decide
  have hdescent : baseEnd_1001204 < baseStart_1001204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001218 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1001218 : Nat := 118140960795 + 1001218 * 2 ^ 59
def prefixEnd_1001218 : Nat := 4983230072969 + 3 ^ 40 * 1001218 * 2
def baseEnd_1001218 : Nat := 228491588414830650520217

theorem tailTrace_1001218 : CollatzResearch.WordTrace tailWord_1001218 prefixEnd_1001218 228491588414830650520217 := by
  unfold tailWord_1001218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129355121691413816487077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24344946991177103510632205 9129355121691413816487077)
  ·
    refine ⟨1711754085317140090591327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9129355121691413816487077 1711754085317140090591327)
    ·
      refine ⟨2567631127975710135886991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711754085317140090591327 2567631127975710135886991)
      ·
        refine ⟨3851446691963565203830487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567631127975710135886991 3851446691963565203830487)
        ·
          refine ⟨5777170037945347805745731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851446691963565203830487 5777170037945347805745731)
          ·
            refine ⟨8665755056918021708618597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777170037945347805745731 8665755056918021708618597)
            ·
              refine ⟨1624829073172129070365987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8665755056918021708618597 1624829073172129070365987)
              ·
                refine ⟨2437243609758193605548981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624829073172129070365987 2437243609758193605548981)
                ·
                  refine ⟨228491588414830650520217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2437243609758193605548981 228491588414830650520217)
                  ·
                    rfl

theorem cell21_1001218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1001218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001218 prefixEnd_1001218 := by exact prefixLift 1001218
  have htrace : WordTrace (prefixWord ++ tailWord_1001218) baseStart_1001218 baseEnd_1001218 := by
    simpa [prefixWord, tailWord_1001218, baseEnd_1001218] using wordTrace_append hprefix tailTrace_1001218
  have hstable : (prefixWord ++ tailWord_1001218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001218).length < 2 ^ (prefixWord ++ tailWord_1001218).sum := by decide
  have hdescent : baseEnd_1001218 < baseStart_1001218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001305 : List Nat := [1, 2, 1, 2, 2, 3, 1, 9]
def baseStart_1001305 : Nat := 118140960795 + 1001305 * 2 ^ 59
def prefixEnd_1001305 : Nat := 4983230072969 + 3 ^ 40 * 1001305 * 2
def baseEnd_1001305 : Nat := 76170481000045944190013

theorem tailTrace_1001305 : CollatzResearch.WordTrace tailWord_1001305 prefixEnd_1001305 76170481000045944190013 := by
  unfold tailWord_1001305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36520593637450469124365369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24347062424966979416243579 36520593637450469124365369)
  ·
    refine ⟨27390445228087851843274027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36520593637450469124365369 27390445228087851843274027)
    ·
      refine ⟨41085667842131777764911041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27390445228087851843274027 41085667842131777764911041)
      ·
        refine ⟨30814250881598833323683281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41085667842131777764911041 30814250881598833323683281)
        ·
          refine ⟨23110688161199124992762461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30814250881598833323683281 23110688161199124992762461)
          ·
            refine ⟨8666508060449671872285923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23110688161199124992762461 8666508060449671872285923)
            ·
              refine ⟨12999762090674507808428885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666508060449671872285923 12999762090674507808428885)
              ·
                refine ⟨76170481000045944190013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12999762090674507808428885 76170481000045944190013)
                ·
                  rfl

theorem cell21_1001305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_1001305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001305 prefixEnd_1001305 := by exact prefixLift 1001305
  have htrace : WordTrace (prefixWord ++ tailWord_1001305) baseStart_1001305 baseEnd_1001305 := by
    simpa [prefixWord, tailWord_1001305, baseEnd_1001305] using wordTrace_append hprefix tailTrace_1001305
  have hstable : (prefixWord ++ tailWord_1001305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001305).length < 2 ^ (prefixWord ++ tailWord_1001305).sum := by decide
  have hdescent : baseEnd_1001305 < baseStart_1001305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001322 : List Nat := [3, 1, 3, 4, 10]
def baseStart_1001322 : Nat := 118140960795 + 1001322 * 2 ^ 59
def prefixEnd_1001322 : Nat := 4983230072969 + 3 ^ 40 * 1001322 * 2
def baseEnd_1001322 : Nat := 2821176822614192355391

theorem tailTrace_1001322 : CollatzResearch.WordTrace tailWord_1001322 prefixEnd_1001322 2821176822614192355391 := by
  unfold tailWord_1001322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130303419597220256933555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24347475785592587351822813 9130303419597220256933555)
  ·
    refine ⟨13695455129395830385400333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130303419597220256933555 13695455129395830385400333)
    ·
      refine ⟨5135795673523436394525125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13695455129395830385400333 5135795673523436394525125)
      ·
        refine ⟨962961688785644323973461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5135795673523436394525125 962961688785644323973461)
        ·
          refine ⟨2821176822614192355391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 962961688785644323973461 2821176822614192355391)
          ·
            rfl

theorem cell21_1001322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 10].length) (baseStart_1001322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001322 prefixEnd_1001322 := by exact prefixLift 1001322
  have htrace : WordTrace (prefixWord ++ tailWord_1001322) baseStart_1001322 baseEnd_1001322 := by
    simpa [prefixWord, tailWord_1001322, baseEnd_1001322] using wordTrace_append hprefix tailTrace_1001322
  have hstable : (prefixWord ++ tailWord_1001322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001322).length < 2 ^ (prefixWord ++ tailWord_1001322).sum := by decide
  have hdescent : baseEnd_1001322 < baseStart_1001322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001370 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_1001370 : Nat := 118140960795 + 1001370 * 2 ^ 59
def prefixEnd_1001370 : Nat := 4983230072969 + 3 ^ 40 * 1001370 * 2
def baseEnd_1001370 : Nat := 228526276885712163986573

theorem tailTrace_1001370 : CollatzResearch.WordTrace tailWord_1001370 prefixEnd_1001370 228526276885712163986573 := by
  unfold tailWord_1001370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130741095553746306370391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24348642921476656816987709 9130741095553746306370391)
  ·
    refine ⟨13696111643330619459555587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130741095553746306370391 13696111643330619459555587)
    ·
      refine ⟨20544167464995929189333381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13696111643330619459555587 20544167464995929189333381)
      ·
        refine ⟨3852031399686736723000009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20544167464995929189333381 3852031399686736723000009)
        ·
          refine ⟨2889023549765052542250007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852031399686736723000009 2889023549765052542250007)
          ·
            refine ⟨4333535324647578813375011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889023549765052542250007 4333535324647578813375011)
            ·
              refine ⟨6500302986971368220062517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333535324647578813375011 6500302986971368220062517)
              ·
                refine ⟨609403405028565770630861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6500302986971368220062517 609403405028565770630861)
                ·
                  refine ⟨228526276885712163986573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609403405028565770630861 228526276885712163986573)
                  ·
                    rfl

theorem cell21_1001370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_1001370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001370 prefixEnd_1001370 := by exact prefixLift 1001370
  have htrace : WordTrace (prefixWord ++ tailWord_1001370) baseStart_1001370 baseEnd_1001370 := by
    simpa [prefixWord, tailWord_1001370, baseEnd_1001370] using wordTrace_append hprefix tailTrace_1001370
  have hstable : (prefixWord ++ tailWord_1001370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001370).length < 2 ^ (prefixWord ++ tailWord_1001370).sum := by decide
  have hdescent : baseEnd_1001370 < baseStart_1001370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001443 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_1001443 : Nat := 118140960795 + 1001443 * 2 ^ 59
def prefixEnd_1001443 : Nat := 4983230072969 + 3 ^ 40 * 1001443 * 2
def baseEnd_1001443 : Nat := 228542936480280259269757

theorem tailTrace_1001443 : CollatzResearch.WordTrace tailWord_1001443 prefixEnd_1001443 228542936480280259269757 := by
  unfold tailWord_1001443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36525626910950518692888983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24350417940633679128592655 36525626910950518692888983)
  ·
    refine ⟨54788440366425778039333475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36525626910950518692888983 54788440366425778039333475)
    ·
      refine ⟨82182660549638667059000213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54788440366425778039333475 82182660549638667059000213)
      ·
        refine ⟨3852312213264312518390635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82182660549638667059000213 3852312213264312518390635)
        ·
          refine ⟨5778468319896468777585953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852312213264312518390635 5778468319896468777585953)
          ·
            refine ⟨4333851239922351583189465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778468319896468777585953 4333851239922351583189465)
            ·
              refine ⟨3250388429941763687392099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333851239922351583189465 3250388429941763687392099)
              ·
                refine ⟨4875582644912645531088149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250388429941763687392099 4875582644912645531088149)
                ·
                  refine ⟨228542936480280259269757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4875582644912645531088149 228542936480280259269757)
                  ·
                    rfl

theorem cell21_1001443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_1001443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001443 prefixEnd_1001443 := by exact prefixLift 1001443
  have htrace : WordTrace (prefixWord ++ tailWord_1001443) baseStart_1001443 baseEnd_1001443 := by
    simpa [prefixWord, tailWord_1001443, baseEnd_1001443] using wordTrace_append hprefix tailTrace_1001443
  have hstable : (prefixWord ++ tailWord_1001443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001443).length < 2 ^ (prefixWord ++ tailWord_1001443).sum := by decide
  have hdescent : baseEnd_1001443 < baseStart_1001443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001508 : List Nat := [2, 3, 1, 4, 3, 1, 1, 6]
def baseStart_1001508 : Nat := 118140960795 + 1001508 * 2 ^ 59
def prefixEnd_1001508 : Nat := 4983230072969 + 3 ^ 40 * 1001508 * 2
def baseEnd_1001508 : Nat := 76185923455284863562097

theorem tailTrace_1001508 : CollatzResearch.WordTrace tailWord_1001508 prefixEnd_1001508 76185923455284863562097 := by
  unfold tailWord_1001508
  simp only [CollatzResearch.WordTrace]
  refine ⟨18263998827857517397002589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24351998437143356529336785 18263998827857517397002589)
  ·
    refine ⟨6848999560446569023875971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18263998827857517397002589 6848999560446569023875971)
    ·
      refine ⟨10273499340669853535813957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848999560446569023875971 10273499340669853535813957)
      ·
        refine ⟨1926281126375597537965117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10273499340669853535813957 1926281126375597537965117)
        ·
          refine ⟨722355422390849076736919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926281126375597537965117 722355422390849076736919)
          ·
            refine ⟨1083533133586273615105379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722355422390849076736919 1083533133586273615105379)
            ·
              refine ⟨1625299700379410422658069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083533133586273615105379 1625299700379410422658069)
              ·
                refine ⟨76185923455284863562097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1625299700379410422658069 76185923455284863562097)
                ·
                  rfl

theorem cell21_1001508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_1001508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001508 prefixEnd_1001508 := by exact prefixLift 1001508
  have htrace : WordTrace (prefixWord ++ tailWord_1001508) baseStart_1001508 baseEnd_1001508 := by
    simpa [prefixWord, tailWord_1001508, baseEnd_1001508] using wordTrace_append hprefix tailTrace_1001508
  have hstable : (prefixWord ++ tailWord_1001508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001508).length < 2 ^ (prefixWord ++ tailWord_1001508).sum := by decide
  have hdescent : baseEnd_1001508 < baseStart_1001508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001570 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1001570 : Nat := 118140960795 + 1001570 * 2 ^ 59
def prefixEnd_1001570 : Nat := 4983230072969 + 3 ^ 40 * 1001570 * 2
def baseEnd_1001570 : Nat := 228571919610556260652831

theorem tailTrace_1001570 : CollatzResearch.WordTrace tailWord_1001570 prefixEnd_1001570 228571919610556260652831 := by
  unfold tailWord_1001570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132564745372604845690541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24353505987660279588508109 9132564745372604845690541)
  ·
    refine ⟨3424711779514726817133953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9132564745372604845690541 3424711779514726817133953)
    ·
      refine ⟨2568533834636045112850465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3424711779514726817133953 2568533834636045112850465)
      ·
        refine ⟨1926400375977033834637849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568533834636045112850465 1926400375977033834637849)
        ·
          refine ⟨1444800281982775375978387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926400375977033834637849 1444800281982775375978387)
          ·
            refine ⟨2167200422974163063967581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444800281982775375978387 2167200422974163063967581)
            ·
              refine ⟨812700158615311148987843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2167200422974163063967581 812700158615311148987843)
              ·
                refine ⟨1219050237922966723481765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812700158615311148987843 1219050237922966723481765)
                ·
                  refine ⟨228571919610556260652831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219050237922966723481765 228571919610556260652831)
                  ·
                    rfl

theorem cell21_1001570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1001570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001570 prefixEnd_1001570 := by exact prefixLift 1001570
  have htrace : WordTrace (prefixWord ++ tailWord_1001570) baseStart_1001570 baseEnd_1001570 := by
    simpa [prefixWord, tailWord_1001570, baseEnd_1001570] using wordTrace_append hprefix tailTrace_1001570
  have hstable : (prefixWord ++ tailWord_1001570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001570).length < 2 ^ (prefixWord ++ tailWord_1001570).sum := by decide
  have hdescent : baseEnd_1001570 < baseStart_1001570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001629 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1001629 : Nat := 118140960795 + 1001629 * 2 ^ 59
def prefixEnd_1001629 : Nat := 4983230072969 + 3 ^ 40 * 1001629 * 2
def baseEnd_1001629 : Nat := 228585384214385269169377

theorem tailTrace_1001629 : CollatzResearch.WordTrace tailWord_1001629 prefixEnd_1001629 228585384214385269169377 := by
  unfold tailWord_1001629
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532410888276672459159941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24354940592184448306106627 36532410888276672459159941)
  ·
    refine ⟨6849827041551876086092489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36532410888276672459159941 6849827041551876086092489)
    ·
      refine ⟨5137370281163907064569367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849827041551876086092489 5137370281163907064569367)
      ·
        refine ⟨7706055421745860596854051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137370281163907064569367 7706055421745860596854051)
        ·
          refine ⟨11559083132618790895281077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706055421745860596854051 11559083132618790895281077)
          ·
            refine ⟨1083664043683011646432601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11559083132618790895281077 1083664043683011646432601)
            ·
              refine ⟨812748032762258734824451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083664043683011646432601 812748032762258734824451)
              ·
                refine ⟨1219122049143388102236677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812748032762258734824451 1219122049143388102236677)
                ·
                  refine ⟨228585384214385269169377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219122049143388102236677 228585384214385269169377)
                  ·
                    rfl

theorem cell21_1001629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1001629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001629 prefixEnd_1001629 := by exact prefixLift 1001629
  have htrace : WordTrace (prefixWord ++ tailWord_1001629) baseStart_1001629 baseEnd_1001629 := by
    simpa [prefixWord, tailWord_1001629, baseEnd_1001629] using wordTrace_append hprefix tailTrace_1001629
  have hstable : (prefixWord ++ tailWord_1001629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001629).length < 2 ^ (prefixWord ++ tailWord_1001629).sum := by decide
  have hdescent : baseEnd_1001629 < baseStart_1001629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001657 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 3]
def baseStart_1001657 : Nat := 118140960795 + 1001657 * 2 ^ 59
def prefixEnd_1001657 : Nat := 4983230072969 + 3 ^ 40 * 1001657 * 2
def baseEnd_1001657 : Nat := 228591774195863442702653

theorem tailTrace_1001657 : CollatzResearch.WordTrace tailWord_1001657 prefixEnd_1001657 228591774195863442702653 := by
  unfold tailWord_1001657
  simp only [CollatzResearch.WordTrace]
  refine ⟨36533432132175233241179225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24355621421450155494119483 36533432132175233241179225)
  ·
    refine ⟨27400074099131424930884419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36533432132175233241179225 27400074099131424930884419)
    ·
      refine ⟨41100111148697137396326629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400074099131424930884419 41100111148697137396326629)
      ·
        refine ⟨7706270840380713261811243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41100111148697137396326629 7706270840380713261811243)
        ·
          refine ⟨11559406260571069892716865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706270840380713261811243 11559406260571069892716865)
          ·
            refine ⟨8669554695428302419537649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11559406260571069892716865 8669554695428302419537649)
            ·
              refine ⟨6502166021571226814653237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669554695428302419537649 6502166021571226814653237)
              ·
                refine ⟨609578064522302513873741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6502166021571226814653237 609578064522302513873741)
                ·
                  refine ⟨228591774195863442702653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609578064522302513873741 228591774195863442702653)
                  ·
                    rfl

theorem cell21_1001657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_1001657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001657 prefixEnd_1001657 := by exact prefixLift 1001657
  have htrace : WordTrace (prefixWord ++ tailWord_1001657) baseStart_1001657 baseEnd_1001657 := by
    simpa [prefixWord, tailWord_1001657, baseEnd_1001657] using wordTrace_append hprefix tailTrace_1001657
  have hstable : (prefixWord ++ tailWord_1001657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001657).length < 2 ^ (prefixWord ++ tailWord_1001657).sum := by decide
  have hdescent : baseEnd_1001657 < baseStart_1001657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001775 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_1001775 : Nat := 118140960795 + 1001775 * 2 ^ 59
def prefixEnd_1001775 : Nat := 4983230072969 + 3 ^ 40 * 1001775 * 2
def baseEnd_1001775 : Nat := 228618703403521459735745

theorem tailTrace_1001775 : CollatzResearch.WordTrace tailWord_1001775 prefixEnd_1001775 228618703403521459735745 := by
  unfold tailWord_1001775
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537735945747739393974779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358490630498492929316519 36537735945747739393974779)
  ·
    refine ⟨54806603918621609090962169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36537735945747739393974779 54806603918621609090962169)
    ·
      refine ⟨41104952938966206818221627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54806603918621609090962169 41104952938966206818221627)
      ·
        refine ⟨61657429408449310227332441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41104952938966206818221627 61657429408449310227332441)
        ·
          refine ⟨46243072056336982670499331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61657429408449310227332441 46243072056336982670499331)
          ·
            refine ⟨69364608084505474005748997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46243072056336982670499331 69364608084505474005748997)
            ·
              refine ⟨13005864015844776376077937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69364608084505474005748997 13005864015844776376077937)
              ·
                refine ⟨9754398011883582282058453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13005864015844776376077937 9754398011883582282058453)
                ·
                  refine ⟨228618703403521459735745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9754398011883582282058453 228618703403521459735745)
                  ·
                    rfl

theorem cell21_1001775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_1001775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001775 prefixEnd_1001775 := by exact prefixLift 1001775
  have htrace : WordTrace (prefixWord ++ tailWord_1001775) baseStart_1001775 baseEnd_1001775 := by
    simpa [prefixWord, tailWord_1001775, baseEnd_1001775] using wordTrace_append hprefix tailTrace_1001775
  have hstable : (prefixWord ++ tailWord_1001775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001775).length < 2 ^ (prefixWord ++ tailWord_1001775).sum := by decide
  have hdescent : baseEnd_1001775 < baseStart_1001775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001778 : List Nat := [3, 2, 1, 1, 5, 2, 7]
def baseStart_1001778 : Nat := 118140960795 + 1001778 * 2 ^ 59
def prefixEnd_1001778 : Nat := 4983230072969 + 3 ^ 40 * 1001778 * 2
def baseEnd_1001778 : Nat := 25402154227154902353971

theorem tailTrace_1001778 : CollatzResearch.WordTrace tailWord_1001778 prefixEnd_1001778 25402154227154902353971 := by
  unfold tailWord_1001778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134461341184217726583497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24358563576491247270889325 9134461341184217726583497)
  ·
    refine ⟨6850846005888163294937623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9134461341184217726583497 6850846005888163294937623)
    ·
      refine ⟨10276269008832244942406435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850846005888163294937623 10276269008832244942406435)
      ·
        refine ⟨15414403513248367413609653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276269008832244942406435 15414403513248367413609653)
        ·
          refine ⟨1445100329367034445025905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15414403513248367413609653 1445100329367034445025905)
          ·
            refine ⟨1083825247025275833769429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445100329367034445025905 1083825247025275833769429)
            ·
              refine ⟨25402154227154902353971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1083825247025275833769429 25402154227154902353971)
              ·
                rfl

theorem cell21_1001778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 7].length) (baseStart_1001778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001778 prefixEnd_1001778 := by exact prefixLift 1001778
  have htrace : WordTrace (prefixWord ++ tailWord_1001778) baseStart_1001778 baseEnd_1001778 := by
    simpa [prefixWord, tailWord_1001778, baseEnd_1001778] using wordTrace_append hprefix tailTrace_1001778
  have hstable : (prefixWord ++ tailWord_1001778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001778).length < 2 ^ (prefixWord ++ tailWord_1001778).sum := by decide
  have hdescent : baseEnd_1001778 < baseStart_1001778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001806 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1001806 : Nat := 118140960795 + 1001806 * 2 ^ 59
def prefixEnd_1001806 : Nat := 4983230072969 + 3 ^ 40 * 1001806 * 2
def baseEnd_1001806 : Nat := 228625778025872294719015

theorem tailTrace_1001806 : CollatzResearch.WordTrace tailWord_1001806 prefixEnd_1001806 228625778025872294719015 := by
  unfold tailWord_1001806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567358326079428961044159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24359244405756954458902181 4567358326079428961044159)
  ·
    refine ⟨6851037489119143441566239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567358326079428961044159 6851037489119143441566239)
    ·
      refine ⟨10276556233678715162349359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6851037489119143441566239 10276556233678715162349359)
      ·
        refine ⟨15414834350518072743524039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276556233678715162349359 15414834350518072743524039)
        ·
          refine ⟨23122251525777109115286059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15414834350518072743524039 23122251525777109115286059)
          ·
            refine ⟨34683377288665663672929089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23122251525777109115286059 34683377288665663672929089)
            ·
              refine ⟨26012532966499247754696817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34683377288665663672929089 26012532966499247754696817)
              ·
                refine ⟨19509399724874435816022613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26012532966499247754696817 19509399724874435816022613)
                ·
                  refine ⟨228625778025872294719015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19509399724874435816022613 228625778025872294719015)
                  ·
                    rfl

theorem cell21_1001806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1001806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001806 prefixEnd_1001806 := by exact prefixLift 1001806
  have htrace : WordTrace (prefixWord ++ tailWord_1001806) baseStart_1001806 baseEnd_1001806 := by
    simpa [prefixWord, tailWord_1001806, baseEnd_1001806] using wordTrace_append hprefix tailTrace_1001806
  have hstable : (prefixWord ++ tailWord_1001806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001806).length < 2 ^ (prefixWord ++ tailWord_1001806).sum := by decide
  have hdescent : baseEnd_1001806 < baseStart_1001806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001868 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1001868 : Nat := 118140960795 + 1001868 * 2 ^ 59
def prefixEnd_1001868 : Nat := 4983230072969 + 3 ^ 40 * 1001868 * 2
def baseEnd_1001868 : Nat := 228639927270573964685555

theorem tailTrace_1001868 : CollatzResearch.WordTrace tailWord_1001868 prefixEnd_1001868 228639927270573964685555 := by
  unfold tailWord_1001868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270563967205408138555129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24360751956273877518073505 18270563967205408138555129)
  ·
    refine ⟨13702922975404056103916347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18270563967205408138555129 13702922975404056103916347)
    ·
      refine ⟨20554384463106084155874521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13702922975404056103916347 20554384463106084155874521)
      ·
        refine ⟨15415788347329563116905891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20554384463106084155874521 15415788347329563116905891)
        ·
          refine ⟨23123682520994344675358837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15415788347329563116905891 23123682520994344675358837)
          ·
            refine ⟨2167845236343219813314891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23123682520994344675358837 2167845236343219813314891)
            ·
              refine ⟨3251767854514829719972337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167845236343219813314891 3251767854514829719972337)
              ·
                refine ⟨2438825890886122289979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251767854514829719972337 2438825890886122289979253)
                ·
                  refine ⟨228639927270573964685555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2438825890886122289979253 228639927270573964685555)
                  ·
                    rfl

theorem cell21_1001868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1001868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1001868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1001868 prefixEnd_1001868 := by exact prefixLift 1001868
  have htrace : WordTrace (prefixWord ++ tailWord_1001868) baseStart_1001868 baseEnd_1001868 := by
    simpa [prefixWord, tailWord_1001868, baseEnd_1001868] using wordTrace_append hprefix tailTrace_1001868
  have hstable : (prefixWord ++ tailWord_1001868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001868).length < 2 ^ (prefixWord ++ tailWord_1001868).sum := by decide
  have hdescent : baseEnd_1001868 < baseStart_1001868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002048 : List Nat := [2, 1, 1, 2, 2, 2, 2, 9]
def baseStart_1002048 : Nat := 118140960795 + 1002048 * 2 ^ 59
def prefixEnd_1002048 : Nat := 4983230072969 + 3 ^ 40 * 1002048 * 2
def baseEnd_1002048 : Nat := 76227001907644550561729

theorem tailTrace_1002048 : CollatzResearch.WordTrace tailWord_1002048 prefixEnd_1002048 76227001907644550561729 := by
  unfold tailWord_1002048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273846536879353509331399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24365128715839138012441865 18273846536879353509331399)
  ·
    refine ⟨27410769805319030263997099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273846536879353509331399 27410769805319030263997099)
    ·
      refine ⟨41116154707978545395995649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27410769805319030263997099 41116154707978545395995649)
      ·
        refine ⟨30837116030983909046996737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41116154707978545395995649 30837116030983909046996737)
        ·
          refine ⟨23127837023237931785247553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30837116030983909046996737 23127837023237931785247553)
          ·
            refine ⟨17345877767428448838935665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23127837023237931785247553 17345877767428448838935665)
            ·
              refine ⟨13009408325571336629201749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17345877767428448838935665 13009408325571336629201749)
              ·
                refine ⟨76227001907644550561729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13009408325571336629201749 76227001907644550561729)
                ·
                  rfl

theorem cell21_1002048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_1002048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002048 prefixEnd_1002048 := by exact prefixLift 1002048
  have htrace : WordTrace (prefixWord ++ tailWord_1002048) baseStart_1002048 baseEnd_1002048 := by
    simpa [prefixWord, tailWord_1002048, baseEnd_1002048] using wordTrace_append hprefix tailTrace_1002048
  have hstable : (prefixWord ++ tailWord_1002048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002048).length < 2 ^ (prefixWord ++ tailWord_1002048).sum := by decide
  have hdescent : baseEnd_1002048 < baseStart_1002048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002068 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1002068 : Nat := 118140960795 + 1002068 * 2 ^ 59
def prefixEnd_1002068 : Nat := 4983230072969 + 3 ^ 40 * 1002068 * 2
def baseEnd_1002068 : Nat := 228685569995418061351813

theorem tailTrace_1002068 : CollatzResearch.WordTrace tailWord_1002068 prefixEnd_1002068 228685569995418061351813 := by
  unfold tailWord_1002068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274211266843125217195429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24365615022457500289593905 18274211266843125217195429)
  ·
    refine ⟨3426414612533085978224143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18274211266843125217195429 3426414612533085978224143)
    ·
      refine ⟨5139621918799628967336215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426414612533085978224143 5139621918799628967336215)
      ·
        refine ⟨7709432878199443451004323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139621918799628967336215 7709432878199443451004323)
        ·
          refine ⟨11564149317299165176506485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709432878199443451004323 11564149317299165176506485)
          ·
            refine ⟨1084138998496796735297483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11564149317299165176506485 1084138998496796735297483)
            ·
              refine ⟨1626208497745195102946225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084138998496796735297483 1626208497745195102946225)
              ·
                refine ⟨1219656373308896327209669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626208497745195102946225 1219656373308896327209669)
                ·
                  refine ⟨228685569995418061351813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219656373308896327209669 228685569995418061351813)
                  ·
                    rfl

theorem cell21_1002068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1002068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002068 prefixEnd_1002068 := by exact prefixLift 1002068
  have htrace : WordTrace (prefixWord ++ tailWord_1002068) baseStart_1002068 baseEnd_1002068 := by
    simpa [prefixWord, tailWord_1002068, baseEnd_1002068] using wordTrace_append hprefix tailTrace_1002068
  have hstable : (prefixWord ++ tailWord_1002068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002068).length < 2 ^ (prefixWord ++ tailWord_1002068).sum := by decide
  have hdescent : baseEnd_1002068 < baseStart_1002068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002158 : List Nat := [4, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1002158 : Nat := 118140960795 + 1002158 * 2 ^ 59
def prefixEnd_1002158 : Nat := 4983230072969 + 3 ^ 40 * 1002158 * 2
def baseEnd_1002158 : Nat := 76235369740532634950543

theorem tailTrace_1002158 : CollatzResearch.WordTrace tailWord_1002158 prefixEnd_1002158 76235369740532634950543 := by
  unfold tailWord_1002158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568963137920024475645891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24367803402240130536778085 4568963137920024475645891)
  ·
    refine ⟨6853444706880036713468837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568963137920024475645891 6853444706880036713468837)
    ·
      refine ⟨1285020882540006883775407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6853444706880036713468837 1285020882540006883775407)
      ·
        refine ⟨1927531323810010325663111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285020882540006883775407 1927531323810010325663111)
        ·
          refine ⟨2891296985715015488494667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927531323810010325663111 2891296985715015488494667)
          ·
            refine ⟨4336945478572523232742001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891296985715015488494667 4336945478572523232742001)
            ·
              refine ⟨3252709108929392424556501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336945478572523232742001 3252709108929392424556501)
              ·
                refine ⟨76235369740532634950543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3252709108929392424556501 76235369740532634950543)
                ·
                  rfl

theorem cell21_1002158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1002158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002158 prefixEnd_1002158 := by exact prefixLift 1002158
  have htrace : WordTrace (prefixWord ++ tailWord_1002158) baseStart_1002158 baseEnd_1002158 := by
    simpa [prefixWord, tailWord_1002158, baseEnd_1002158] using wordTrace_append hprefix tailTrace_1002158
  have hstable : (prefixWord ++ tailWord_1002158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002158).length < 2 ^ (prefixWord ++ tailWord_1002158).sum := by decide
  have hdescent : baseEnd_1002158 < baseStart_1002158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002248 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_1002248 : Nat := 118140960795 + 1002248 * 2 ^ 59
def prefixEnd_1002248 : Nat := 4983230072969 + 3 ^ 40 * 1002248 * 2
def baseEnd_1002248 : Nat := 228726648447777748351445

theorem tailTrace_1002248 : CollatzResearch.WordTrace tailWord_1002248 prefixEnd_1002248 228726648447777748351445 := by
  unfold tailWord_1002248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277493836517070587971699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24369991782022760783962265 18277493836517070587971699)
  ·
    refine ⟨27416240754775605881957549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277493836517070587971699 27416240754775605881957549)
    ·
      refine ⟨10281090283040852205734081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27416240754775605881957549 10281090283040852205734081)
      ·
        refine ⟨7710817712280639154300561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10281090283040852205734081 7710817712280639154300561)
        ·
          refine ⟨5783113284210479365725421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710817712280639154300561 5783113284210479365725421)
          ·
            refine ⟨2168667481578929762147033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5783113284210479365725421 2168667481578929762147033)
            ·
              refine ⟨1626500611184197321610275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168667481578929762147033 1626500611184197321610275)
              ·
                refine ⟨2439750916776295982415413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626500611184197321610275 2439750916776295982415413)
                ·
                  refine ⟨228726648447777748351445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439750916776295982415413 228726648447777748351445)
                  ·
                    rfl

theorem cell21_1002248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_1002248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002248 prefixEnd_1002248 := by exact prefixLift 1002248
  have htrace : WordTrace (prefixWord ++ tailWord_1002248) baseStart_1002248 baseEnd_1002248 := by
    simpa [prefixWord, tailWord_1002248, baseEnd_1002248] using wordTrace_append hprefix tailTrace_1002248
  have hstable : (prefixWord ++ tailWord_1002248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002248).length < 2 ^ (prefixWord ++ tailWord_1002248).sum := by decide
  have hdescent : baseEnd_1002248 < baseStart_1002248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002293 : List Nat := [1, 3, 3, 1, 3, 3, 7]
def baseStart_1002293 : Nat := 118140960795 + 1002293 * 2 ^ 59
def prefixEnd_1002293 : Nat := 4983230072969 + 3 ^ 40 * 1002293 * 2
def baseEnd_1002293 : Nat := 25415213117874185566817

theorem tailTrace_1002293 : CollatzResearch.WordTrace tailWord_1002293 prefixEnd_1002293 25415213117874185566817 := by
  unfold tailWord_1002293
  simp only [CollatzResearch.WordTrace]
  refine ⟨36556628957871113861331533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24371085971914075907554355 36556628957871113861331533)
  ·
    refine ⟨13708735859201667697999325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36556628957871113861331533 13708735859201667697999325)
    ·
      refine ⟨5140775947200625386749747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13708735859201667697999325 5140775947200625386749747)
      ·
        refine ⟨7711163920800938080124621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140775947200625386749747 7711163920800938080124621)
        ·
          refine ⟨2891686470300351780046733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7711163920800938080124621 2891686470300351780046733)
          ·
            refine ⟨1084382426362631917517525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2891686470300351780046733 1084382426362631917517525)
            ·
              refine ⟨25415213117874185566817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1084382426362631917517525 25415213117874185566817)
              ·
                rfl

theorem cell21_1002293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 7].length) (baseStart_1002293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002293 prefixEnd_1002293 := by exact prefixLift 1002293
  have htrace : WordTrace (prefixWord ++ tailWord_1002293) baseStart_1002293 baseEnd_1002293 := by
    simpa [prefixWord, tailWord_1002293, baseEnd_1002293] using wordTrace_append hprefix tailTrace_1002293
  have hstable : (prefixWord ++ tailWord_1002293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002293).length < 2 ^ (prefixWord ++ tailWord_1002293).sum := by decide
  have hdescent : baseEnd_1002293 < baseStart_1002293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002358 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1002358 : Nat := 118140960795 + 1002358 * 2 ^ 59
def prefixEnd_1002358 : Nat := 4983230072969 + 3 ^ 40 * 1002358 * 2
def baseEnd_1002358 : Nat := 228751751946442001517887

theorem tailTrace_1002358 : CollatzResearch.WordTrace tailWord_1002358 prefixEnd_1002358 228751751946442001517887 := by
  unfold tailWord_1002358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284937481414726872652983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24372666468423753308298485 2284937481414726872652983)
  ·
    refine ⟨3427406222122090308979475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284937481414726872652983 3427406222122090308979475)
    ·
      refine ⟨5141109333183135463469213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427406222122090308979475 5141109333183135463469213)
      ·
        refine ⟨1927915999943675798800955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5141109333183135463469213 1927915999943675798800955)
        ·
          refine ⟨2891873999915513698201433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927915999943675798800955 2891873999915513698201433)
          ·
            refine ⟨2168905499936635273651075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891873999915513698201433 2168905499936635273651075)
            ·
              refine ⟨3253358249904952910476613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168905499936635273651075 3253358249904952910476613)
              ·
                refine ⟨610004671857178670714365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3253358249904952910476613 610004671857178670714365)
                ·
                  refine ⟨228751751946442001517887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610004671857178670714365 228751751946442001517887)
                  ·
                    rfl

theorem cell21_1002358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1002358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002358 prefixEnd_1002358 := by exact prefixLift 1002358
  have htrace : WordTrace (prefixWord ++ tailWord_1002358) baseStart_1002358 baseEnd_1002358 := by
    simpa [prefixWord, tailWord_1002358, baseEnd_1002358] using wordTrace_append hprefix tailTrace_1002358
  have hstable : (prefixWord ++ tailWord_1002358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002358).length < 2 ^ (prefixWord ++ tailWord_1002358).sum := by decide
  have hdescent : baseEnd_1002358 < baseStart_1002358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002400 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_1002400 : Nat := 118140960795 + 1002400 * 2 ^ 59
def prefixEnd_1002400 : Nat := 4983230072969 + 3 ^ 40 * 1002400 * 2
def baseEnd_1002400 : Nat := 228761336918659261817801

theorem tailTrace_1002400 : CollatzResearch.WordTrace tailWord_1002400 prefixEnd_1002400 228761336918659261817801 := by
  unfold tailWord_1002400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280265784241735567738327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24373687712322314090317769 18280265784241735567738327)
  ·
    refine ⟨27420398676362603351607491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18280265784241735567738327 27420398676362603351607491)
    ·
      refine ⟨41130598014543905027411237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27420398676362603351607491 41130598014543905027411237)
      ·
        refine ⟨7711987127726982192639607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41130598014543905027411237 7711987127726982192639607)
        ·
          refine ⟨11567980691590473288959411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711987127726982192639607 11567980691590473288959411)
          ·
            refine ⟨17351971037385709933439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567980691590473288959411 17351971037385709933439117)
            ·
              refine ⟨6506989139019641225039669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17351971037385709933439117 6506989139019641225039669)
              ·
                refine ⟨610030231783091364847469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6506989139019641225039669 610030231783091364847469)
                ·
                  refine ⟨228761336918659261817801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610030231783091364847469 228761336918659261817801)
                  ·
                    rfl

theorem cell21_1002400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_1002400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002400 prefixEnd_1002400 := by exact prefixLift 1002400
  have htrace : WordTrace (prefixWord ++ tailWord_1002400) baseStart_1002400 baseEnd_1002400 := by
    simpa [prefixWord, tailWord_1002400, baseEnd_1002400] using wordTrace_append hprefix tailTrace_1002400
  have hstable : (prefixWord ++ tailWord_1002400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002400).length < 2 ^ (prefixWord ++ tailWord_1002400).sum := by decide
  have hdescent : baseEnd_1002400 < baseStart_1002400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002482 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_1002482 : Nat := 118140960795 + 1002482 * 2 ^ 59
def prefixEnd_1002482 : Nat := 4983230072969 + 3 ^ 40 * 1002482 * 2
def baseEnd_1002482 : Nat := 228780050435845341450967

theorem tailTrace_1002482 : CollatzResearch.WordTrace tailWord_1002482 prefixEnd_1002482 228780050435845341450967 := by
  unfold tailWord_1002482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140880588546599784990425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24375681569457599426641133 9140880588546599784990425)
  ·
    refine ⟨6855660441409949838742819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9140880588546599784990425 6855660441409949838742819)
    ·
      refine ⟨10283490662114924758114229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855660441409949838742819 10283490662114924758114229)
      ·
        refine ⟨964077249573274196073209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10283490662114924758114229 964077249573274196073209)
        ·
          refine ⟨723057937179955647054907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964077249573274196073209 723057937179955647054907)
          ·
            refine ⟨1084586905769933470582361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723057937179955647054907 1084586905769933470582361)
            ·
              refine ⟨813440179327450102936771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084586905769933470582361 813440179327450102936771)
              ·
                refine ⟨1220160268991175154405157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813440179327450102936771 1220160268991175154405157)
                ·
                  refine ⟨228780050435845341450967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220160268991175154405157 228780050435845341450967)
                  ·
                    rfl

theorem cell21_1002482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_1002482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002482 prefixEnd_1002482 := by exact prefixLift 1002482
  have htrace : WordTrace (prefixWord ++ tailWord_1002482) baseStart_1002482 baseEnd_1002482 := by
    simpa [prefixWord, tailWord_1002482, baseEnd_1002482] using wordTrace_append hprefix tailTrace_1002482
  have hstable : (prefixWord ++ tailWord_1002482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002482).length < 2 ^ (prefixWord ++ tailWord_1002482).sum := by decide
  have hdescent : baseEnd_1002482 < baseStart_1002482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002504 : List Nat := [2, 1, 3, 2, 1, 3, 2, 7]
def baseStart_1002504 : Nat := 118140960795 + 1002504 * 2 ^ 59
def prefixEnd_1002504 : Nat := 4983230072969 + 3 ^ 40 * 1002504 * 2
def baseEnd_1002504 : Nat := 76261690378526064028085

theorem tailTrace_1002504 : CollatzResearch.WordTrace tailWord_1002504 prefixEnd_1002504 76261690378526064028085 := by
  unfold tailWord_1002504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282162380053348448631283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24376216506737797931508377 18282162380053348448631283)
  ·
    refine ⟨27423243570080022672946925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18282162380053348448631283 27423243570080022672946925)
    ·
      refine ⟨10283716338780008502355097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27423243570080022672946925 10283716338780008502355097)
      ·
        refine ⟨7712787254085006376766323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10283716338780008502355097 7712787254085006376766323)
        ·
          refine ⟨11569180881127509565149485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712787254085006376766323 11569180881127509565149485)
          ·
            refine ⟨4338442830422816086931057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11569180881127509565149485 4338442830422816086931057)
            ·
              refine ⟨3253832122817112065198293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4338442830422816086931057 3253832122817112065198293)
              ·
                refine ⟨76261690378526064028085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3253832122817112065198293 76261690378526064028085)
                ·
                  rfl

theorem cell21_1002504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_1002504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002504 prefixEnd_1002504 := by exact prefixLift 1002504
  have htrace : WordTrace (prefixWord ++ tailWord_1002504) baseStart_1002504 baseEnd_1002504 := by
    simpa [prefixWord, tailWord_1002504, baseEnd_1002504] using wordTrace_append hprefix tailTrace_1002504
  have hstable : (prefixWord ++ tailWord_1002504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002504).length < 2 ^ (prefixWord ++ tailWord_1002504).sum := by decide
  have hdescent : baseEnd_1002504 < baseStart_1002504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002538 : List Nat := [3, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1002538 : Nat := 118140960795 + 1002538 * 2 ^ 59
def prefixEnd_1002538 : Nat := 4983230072969 + 3 ^ 40 * 1002538 * 2
def baseEnd_1002538 : Nat := 76264276799600562839173

theorem tailTrace_1002538 : CollatzResearch.WordTrace tailWord_1002538 prefixEnd_1002538 76264276799600562839173 := by
  unfold tailWord_1002538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141391210495880176000067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24377043227989013802666845 9141391210495880176000067)
  ·
    refine ⟨13712086815743820264000101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141391210495880176000067 13712086815743820264000101)
    ·
      refine ⟨2571016277951966299500019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13712086815743820264000101 2571016277951966299500019)
      ·
        refine ⟨3856524416927949449250029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571016277951966299500019 3856524416927949449250029)
        ·
          refine ⟨1446196656347981043468761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3856524416927949449250029 1446196656347981043468761)
          ·
            refine ⟨1084647492260985782601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446196656347981043468761 1084647492260985782601571)
            ·
              refine ⟨1626971238391478673902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084647492260985782601571 1626971238391478673902357)
              ·
                refine ⟨76264276799600562839173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1626971238391478673902357 76264276799600562839173)
                ·
                  rfl

theorem cell21_1002538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1002538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002538 prefixEnd_1002538 := by exact prefixLift 1002538
  have htrace : WordTrace (prefixWord ++ tailWord_1002538) baseStart_1002538 baseEnd_1002538 := by
    simpa [prefixWord, tailWord_1002538, baseEnd_1002538] using wordTrace_append hprefix tailTrace_1002538
  have hstable : (prefixWord ++ tailWord_1002538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002538).length < 2 ^ (prefixWord ++ tailWord_1002538).sum := by decide
  have hdescent : baseEnd_1002538 < baseStart_1002538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002549 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1002549 : Nat := 118140960795 + 1002549 * 2 ^ 59
def prefixEnd_1002549 : Nat := 4983230072969 + 3 ^ 40 * 1002549 * 2
def baseEnd_1002549 : Nat := 228795340748668113834163

theorem tailTrace_1002549 : CollatzResearch.WordTrace tailWord_1002549 prefixEnd_1002549 228795340748668113834163 := by
  unfold tailWord_1002549
  simp only [CollatzResearch.WordTrace]
  refine ⟨36565966044943669582650701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24377310696629113055100467 36565966044943669582650701)
  ·
    refine ⟨13712237266853876093494013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36565966044943669582650701 13712237266853876093494013)
    ·
      refine ⟨5142088975070203535060255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13712237266853876093494013 5142088975070203535060255)
      ·
        refine ⟨7713133462605305302590383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142088975070203535060255 7713133462605305302590383)
        ·
          refine ⟨11569700193907957953885575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713133462605305302590383 11569700193907957953885575)
          ·
            refine ⟨17354550290861936930828363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569700193907957953885575 17354550290861936930828363)
            ·
              refine ⟨26031825436292905396242545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17354550290861936930828363 26031825436292905396242545)
              ·
                refine ⟨19523869077219679047181909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26031825436292905396242545 19523869077219679047181909)
                ·
                  refine ⟨228795340748668113834163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19523869077219679047181909 228795340748668113834163)
                  ·
                    rfl

theorem cell21_1002549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1002549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002549 prefixEnd_1002549 := by exact prefixLift 1002549
  have htrace : WordTrace (prefixWord ++ tailWord_1002549) baseStart_1002549 baseEnd_1002549 := by
    simpa [prefixWord, tailWord_1002549, baseEnd_1002549] using wordTrace_append hprefix tailTrace_1002549
  have hstable : (prefixWord ++ tailWord_1002549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002549).length < 2 ^ (prefixWord ++ tailWord_1002549).sum := by decide
  have hdescent : baseEnd_1002549 < baseStart_1002549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002642 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1002642 : Nat := 118140960795 + 1002642 * 2 ^ 59
def prefixEnd_1002642 : Nat := 4983230072969 + 3 ^ 40 * 1002642 * 2
def baseEnd_1002642 : Nat := 228816564615720618783973

theorem tailTrace_1002642 : CollatzResearch.WordTrace tailWord_1002642 prefixEnd_1002642 228816564615720618783973 := by
  unfold tailWord_1002642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142339508401686616446545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24379572022404497643857453 9142339508401686616446545)
  ·
    refine ⟨6856754631301264962334909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9142339508401686616446545 6856754631301264962334909)
    ·
      refine ⟨2571282986737974360875591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6856754631301264962334909 2571282986737974360875591)
      ·
        refine ⟨3856924480106961541313387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571282986737974360875591 3856924480106961541313387)
        ·
          refine ⟨5785386720160442311970081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856924480106961541313387 5785386720160442311970081)
          ·
            refine ⟨4339040040120331733977561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785386720160442311970081 4339040040120331733977561)
            ·
              refine ⟨3254280030090248800483171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4339040040120331733977561 3254280030090248800483171)
              ·
                refine ⟨4881420045135373200724757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254280030090248800483171 4881420045135373200724757)
                ·
                  refine ⟨228816564615720618783973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4881420045135373200724757 228816564615720618783973)
                  ·
                    rfl

theorem cell21_1002642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1002642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002642 prefixEnd_1002642 := by exact prefixLift 1002642
  have htrace : WordTrace (prefixWord ++ tailWord_1002642) baseStart_1002642 baseEnd_1002642 := by
    simpa [prefixWord, tailWord_1002642, baseEnd_1002642] using wordTrace_append hprefix tailTrace_1002642
  have hstable : (prefixWord ++ tailWord_1002642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002642).length < 2 ^ (prefixWord ++ tailWord_1002642).sum := by decide
  have hdescent : baseEnd_1002642 < baseStart_1002642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002656 : List Nat := [2, 1, 1, 4, 2, 1, 4, 6]
def baseStart_1002656 : Nat := 118140960795 + 1002656 * 2 ^ 59
def prefixEnd_1002656 : Nat := 4983230072969 + 3 ^ 40 * 1002656 * 2
def baseEnd_1002656 : Nat := 76273253202153235183537

theorem tailTrace_1002656 : CollatzResearch.WordTrace tailWord_1002656 prefixEnd_1002656 76273253202153235183537 := by
  unfold tailWord_1002656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284934327778013428397911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24379912437037351237863881 18284934327778013428397911)
  ·
    refine ⟨27427401491667020142596867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18284934327778013428397911 27427401491667020142596867)
    ·
      refine ⟨41141102237500530213895301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27427401491667020142596867 41141102237500530213895301)
      ·
        refine ⟨7713956669531349415105369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41141102237500530213895301 7713956669531349415105369)
        ·
          refine ⟨5785467502148512061329027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713956669531349415105369 5785467502148512061329027)
          ·
            refine ⟨8678201253222768091993541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785467502148512061329027 8678201253222768091993541)
            ·
              refine ⟨1627162734979269017248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8678201253222768091993541 1627162734979269017248789)
              ·
                refine ⟨76273253202153235183537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627162734979269017248789 76273253202153235183537)
                ·
                  rfl

theorem cell21_1002656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_1002656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002656 prefixEnd_1002656 := by exact prefixLift 1002656
  have htrace : WordTrace (prefixWord ++ tailWord_1002656) baseStart_1002656 baseEnd_1002656 := by
    simpa [prefixWord, tailWord_1002656, baseEnd_1002656] using wordTrace_append hprefix tailTrace_1002656
  have hstable : (prefixWord ++ tailWord_1002656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002656).length < 2 ^ (prefixWord ++ tailWord_1002656).sum := by decide
  have hdescent : baseEnd_1002656 < baseStart_1002656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002690 : List Nat := [3, 5, 1, 1, 2, 9]
def baseStart_1002690 : Nat := 118140960795 + 1002690 * 2 ^ 59
def prefixEnd_1002690 : Nat := 4983230072969 + 3 ^ 40 * 1002690 * 2
def baseEnd_1002690 : Nat := 8475093291469748221625

theorem tailTrace_1002690 : CollatzResearch.WordTrace tailWord_1002690 prefixEnd_1002690 8475093291469748221625 := by
  unfold tailWord_1002690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142777184358212665883381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24380739158288567109022349 9142777184358212665883381)
  ·
    refine ⟨857135361033582437426567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9142777184358212665883381 857135361033582437426567)
    ·
      refine ⟨1285703041550373656139851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857135361033582437426567 1285703041550373656139851)
      ·
        refine ⟨1928554562325560484209777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285703041550373656139851 1928554562325560484209777)
        ·
          refine ⟨1446415921744170363157333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928554562325560484209777 1446415921744170363157333)
          ·
            refine ⟨8475093291469748221625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1446415921744170363157333 8475093291469748221625)
            ·
              rfl

theorem cell21_1002690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 9].length) (baseStart_1002690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002690 prefixEnd_1002690 := by exact prefixLift 1002690
  have htrace : WordTrace (prefixWord ++ tailWord_1002690) baseStart_1002690 baseEnd_1002690 := by
    simpa [prefixWord, tailWord_1002690, baseEnd_1002690] using wordTrace_append hprefix tailTrace_1002690
  have hstable : (prefixWord ++ tailWord_1002690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002690).length < 2 ^ (prefixWord ++ tailWord_1002690).sum := by decide
  have hdescent : baseEnd_1002690 < baseStart_1002690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002746 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_1002746 : Nat := 118140960795 + 1002746 * 2 ^ 59
def prefixEnd_1002746 : Nat := 4983230072969 + 3 ^ 40 * 1002746 * 2
def baseEnd_1002746 : Nat := 228840298832639549050427

theorem tailTrace_1002746 : CollatzResearch.WordTrace tailWord_1002746 prefixEnd_1002746 228840298832639549050427 := by
  unfold tailWord_1002746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143287806307493056893023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24382100816819981485048061 9143287806307493056893023)
  ·
    refine ⟨13714931709461239585339535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143287806307493056893023 13714931709461239585339535)
    ·
      refine ⟨20572397564191859378009303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13714931709461239585339535 20572397564191859378009303)
      ·
        refine ⟨30858596346287789067013955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20572397564191859378009303 30858596346287789067013955)
        ·
          refine ⟨46287894519431683600520933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30858596346287789067013955 46287894519431683600520933)
          ·
            refine ⟨8678980222393440675097675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46287894519431683600520933 8678980222393440675097675)
            ·
              refine ⟨13018470333590161012646513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678980222393440675097675 13018470333590161012646513)
              ·
                refine ⟨9763852750192620759484885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13018470333590161012646513 9763852750192620759484885)
                ·
                  refine ⟨228840298832639549050427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9763852750192620759484885 228840298832639549050427)
                  ·
                    rfl

theorem cell21_1002746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_1002746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002746 prefixEnd_1002746 := by exact prefixLift 1002746
  have htrace : WordTrace (prefixWord ++ tailWord_1002746) baseStart_1002746 baseEnd_1002746 := by
    simpa [prefixWord, tailWord_1002746, baseEnd_1002746] using wordTrace_append hprefix tailTrace_1002746
  have hstable : (prefixWord ++ tailWord_1002746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002746).length < 2 ^ (prefixWord ++ tailWord_1002746).sum := by decide
  have hdescent : baseEnd_1002746 < baseStart_1002746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002763 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_1002763 : Nat := 118140960795 + 1002763 * 2 ^ 59
def prefixEnd_1002763 : Nat := 4983230072969 + 3 ^ 40 * 1002763 * 2
def baseEnd_1002763 : Nat := 228844178464251297267059

theorem tailTrace_1002763 : CollatzResearch.WordTrace tailWord_1002763 prefixEnd_1002763 228844178464251297267059 := by
  unfold tailWord_1002763
  simp only [CollatzResearch.WordTrace]
  refine ⟨36573771266168384130940943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24382514177445589420627295 36573771266168384130940943)
  ·
    refine ⟨54860656899252576196411415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36573771266168384130940943 54860656899252576196411415)
    ·
      refine ⟨82290985348878864294617123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54860656899252576196411415 82290985348878864294617123)
      ·
        refine ⟨123436478023318296441925685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82290985348878864294617123 123436478023318296441925685)
        ·
          refine ⟨11572169814686090291430533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123436478023318296441925685 11572169814686090291430533)
          ·
            refine ⟨2169781840253641929643225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11572169814686090291430533 2169781840253641929643225)
            ·
              refine ⟨1627336380190231447232419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169781840253641929643225 1627336380190231447232419)
              ·
                refine ⟨2441004570285347170848629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627336380190231447232419 2441004570285347170848629)
                ·
                  refine ⟨228844178464251297267059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2441004570285347170848629 228844178464251297267059)
                  ·
                    rfl

theorem cell21_1002763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_1002763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002763 prefixEnd_1002763 := by exact prefixLift 1002763
  have htrace : WordTrace (prefixWord ++ tailWord_1002763) baseStart_1002763 baseEnd_1002763 := by
    simpa [prefixWord, tailWord_1002763, baseEnd_1002763] using wordTrace_append hprefix tailTrace_1002763
  have hstable : (prefixWord ++ tailWord_1002763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002763).length < 2 ^ (prefixWord ++ tailWord_1002763).sum := by decide
  have hdescent : baseEnd_1002763 < baseStart_1002763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002794 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_1002794 : Nat := 118140960795 + 1002794 * 2 ^ 59
def prefixEnd_1002794 : Nat := 4983230072969 + 3 ^ 40 * 1002794 * 2
def baseEnd_1002794 : Nat := 228851253086602132250329

theorem tailTrace_1002794 : CollatzResearch.WordTrace tailWord_1002794 prefixEnd_1002794 228851253086602132250329 := by
  unfold tailWord_1002794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143725482264019106329859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24383267952704050950212957 9143725482264019106329859)
  ·
    refine ⟨13715588223396028659494789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143725482264019106329859 13715588223396028659494789)
    ·
      refine ⟨2571672791886755373655273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13715588223396028659494789 2571672791886755373655273)
      ·
        refine ⟨1928754593915066530241455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2571672791886755373655273 1928754593915066530241455)
        ·
          refine ⟨2893131890872599795362183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928754593915066530241455 2893131890872599795362183)
          ·
            refine ⟨4339697836308899693043275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893131890872599795362183 4339697836308899693043275)
            ·
              refine ⟨6509546754463349539564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339697836308899693043275 6509546754463349539564913)
              ·
                refine ⟨4882160065847512154673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509546754463349539564913 4882160065847512154673685)
                ·
                  refine ⟨228851253086602132250329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4882160065847512154673685 228851253086602132250329)
                  ·
                    rfl

theorem cell21_1002794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_1002794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002794 prefixEnd_1002794 := by exact prefixLift 1002794
  have htrace : WordTrace (prefixWord ++ tailWord_1002794) baseStart_1002794 baseEnd_1002794 := by
    simpa [prefixWord, tailWord_1002794, baseEnd_1002794] using wordTrace_append hprefix tailTrace_1002794
  have hstable : (prefixWord ++ tailWord_1002794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002794).length < 2 ^ (prefixWord ++ tailWord_1002794).sum := by decide
  have hdescent : baseEnd_1002794 < baseStart_1002794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002884 : List Nat := [2, 3, 2, 1, 1, 3, 3, 6]
def baseStart_1002884 : Nat := 118140960795 + 1002884 * 2 ^ 59
def prefixEnd_1002884 : Nat := 4983230072969 + 3 ^ 40 * 1002884 * 2
def baseEnd_1002884 : Nat := 76290597437593991916715

theorem tailTrace_1002884 : CollatzResearch.WordTrace tailWord_1002884 prefixEnd_1002884 76290597437593991916715 := by
  unfold tailWord_1002884
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289092249365010898047853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24385456332486681197397137 18289092249365010898047853)
  ·
    refine ⟨6858409593511879086767945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18289092249365010898047853 6858409593511879086767945)
    ·
      refine ⟨5143807195133909315075959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6858409593511879086767945 5143807195133909315075959)
      ·
        refine ⟨7715710792700863972613939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143807195133909315075959 7715710792700863972613939)
        ·
          refine ⟨11573566189051295958920909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715710792700863972613939 11573566189051295958920909)
          ·
            refine ⟨4340087320894235984595341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11573566189051295958920909 4340087320894235984595341)
            ·
              refine ⟨1627532745335338494223253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4340087320894235984595341 1627532745335338494223253)
              ·
                refine ⟨76290597437593991916715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627532745335338494223253 76290597437593991916715)
                ·
                  rfl

theorem cell21_1002884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_1002884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002884 prefixEnd_1002884 := by exact prefixLift 1002884
  have htrace : WordTrace (prefixWord ++ tailWord_1002884) baseStart_1002884 baseEnd_1002884 := by
    simpa [prefixWord, tailWord_1002884, baseEnd_1002884] using wordTrace_append hprefix tailTrace_1002884
  have hstable : (prefixWord ++ tailWord_1002884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002884).length < 2 ^ (prefixWord ++ tailWord_1002884).sum := by decide
  have hdescent : baseEnd_1002884 < baseStart_1002884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002929 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1002929 : Nat := 118140960795 + 1002929 * 2 ^ 59
def prefixEnd_1002929 : Nat := 4983230072969 + 3 ^ 40 * 1002929 * 2
def baseEnd_1002929 : Nat := 228882061925871897500053

theorem tailTrace_1002929 : CollatzResearch.WordTrace tailWord_1002929 prefixEnd_1002929 228882061925871897500053 := by
  unfold tailWord_1002929
  simp only [CollatzResearch.WordTrace]
  refine ⟨36579825783566994481483841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24386550522377996320989227 36579825783566994481483841)
  ·
    refine ⟨27434869337675245861112881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36579825783566994481483841 27434869337675245861112881)
    ·
      refine ⟨20576152003256434395834661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27434869337675245861112881 20576152003256434395834661)
      ·
        refine ⟨3858028500610581449218999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20576152003256434395834661 3858028500610581449218999)
        ·
          refine ⟨5787042750915872173828499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858028500610581449218999 5787042750915872173828499)
          ·
            refine ⟨8680564126373808260742749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787042750915872173828499 8680564126373808260742749)
            ·
              refine ⟨3255211547390178097778531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8680564126373808260742749 3255211547390178097778531)
              ·
                refine ⟨4882817321085267146667797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255211547390178097778531 4882817321085267146667797)
                ·
                  refine ⟨228882061925871897500053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4882817321085267146667797 228882061925871897500053)
                  ·
                    rfl

theorem cell21_1002929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1002929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002929 prefixEnd_1002929 := by exact prefixLift 1002929
  have htrace : WordTrace (prefixWord ++ tailWord_1002929) baseStart_1002929 baseEnd_1002929 := by
    simpa [prefixWord, tailWord_1002929, baseEnd_1002929] using wordTrace_append hprefix tailTrace_1002929
  have hstable : (prefixWord ++ tailWord_1002929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002929).length < 2 ^ (prefixWord ++ tailWord_1002929).sum := by decide
  have hdescent : baseEnd_1002929 < baseStart_1002929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002966 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1002966 : Nat := 118140960795 + 1002966 * 2 ^ 59
def prefixEnd_1002966 : Nat := 4983230072969 + 3 ^ 40 * 1002966 * 2
def baseEnd_1002966 : Nat := 228890505829968055383311

theorem tailTrace_1002966 : CollatzResearch.WordTrace tailWord_1002966 prefixEnd_1002966 228890505829968055383311 := by
  unfold tailWord_1002966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286323455277059362536297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24387450189621966533720501 2286323455277059362536297)
  ·
    refine ⟨1714742591457794521902223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2286323455277059362536297 1714742591457794521902223)
    ·
      refine ⟨2572113887186691782853335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714742591457794521902223 2572113887186691782853335)
      ·
        refine ⟨3858170830780037674280003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572113887186691782853335 3858170830780037674280003)
        ·
          refine ⟨5787256246170056511420005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858170830780037674280003 5787256246170056511420005)
          ·
            refine ⟨1085110546156885595891251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5787256246170056511420005 1085110546156885595891251)
            ·
              refine ⟨1627665819235328393836877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085110546156885595891251 1627665819235328393836877)
              ·
                refine ⟨610374682213248147688829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627665819235328393836877 610374682213248147688829)
                ·
                  refine ⟨228890505829968055383311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610374682213248147688829 228890505829968055383311)
                  ·
                    rfl

theorem cell21_1002966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1002966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002966 prefixEnd_1002966 := by exact prefixLift 1002966
  have htrace : WordTrace (prefixWord ++ tailWord_1002966) baseStart_1002966 baseEnd_1002966 := by
    simpa [prefixWord, tailWord_1002966, baseEnd_1002966] using wordTrace_append hprefix tailTrace_1002966
  have hstable : (prefixWord ++ tailWord_1002966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002966).length < 2 ^ (prefixWord ++ tailWord_1002966).sum := by decide
  have hdescent : baseEnd_1002966 < baseStart_1002966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002991 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 3]
def baseStart_1002991 : Nat := 118140960795 + 1002991 * 2 ^ 59
def prefixEnd_1002991 : Nat := 4983230072969 + 3 ^ 40 * 1002991 * 2
def baseEnd_1002991 : Nat := 228896211170573567466593

theorem tailTrace_1002991 : CollatzResearch.WordTrace tailWord_1002991 prefixEnd_1002991 228896211170573567466593 := by
  unfold tailWord_1002991
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582087109342379070240827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24388058072894919380160551 36582087109342379070240827)
  ·
    refine ⟨54873130664013568605361241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36582087109342379070240827 54873130664013568605361241)
    ·
      refine ⟨41154847998010176454020931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54873130664013568605361241 41154847998010176454020931)
      ·
        refine ⟨61732271997015264681031397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41154847998010176454020931 61732271997015264681031397)
        ·
          refine ⟨11574800999440362127693387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61732271997015264681031397 11574800999440362127693387)
          ·
            refine ⟨17362201499160543191540081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574800999440362127693387 17362201499160543191540081)
            ·
              refine ⟨13021651124370407393655061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17362201499160543191540081 13021651124370407393655061)
              ·
                refine ⟨610389896454862846577581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13021651124370407393655061 610389896454862846577581)
                ·
                  refine ⟨228896211170573567466593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610389896454862846577581 228896211170573567466593)
                  ·
                    rfl

theorem cell21_1002991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].length) (baseStart_1002991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1002991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1002991 prefixEnd_1002991 := by exact prefixLift 1002991
  have htrace : WordTrace (prefixWord ++ tailWord_1002991) baseStart_1002991 baseEnd_1002991 := by
    simpa [prefixWord, tailWord_1002991, baseEnd_1002991] using wordTrace_append hprefix tailTrace_1002991
  have hstable : (prefixWord ++ tailWord_1002991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002991).length < 2 ^ (prefixWord ++ tailWord_1002991).sum := by decide
  have hdescent : baseEnd_1002991 < baseStart_1002991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003084 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1003084 : Nat := 118140960795 + 1003084 * 2 ^ 59
def prefixEnd_1003084 : Nat := 4983230072969 + 3 ^ 40 * 1003084 * 2
def baseEnd_1003084 : Nat := 228917435037626072416403

theorem tailTrace_1003084 : CollatzResearch.WordTrace tailWord_1003084 prefixEnd_1003084 228917435037626072416403 := by
  unfold tailWord_1003084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292739549002727976688153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24390319398670303968917537 18292739549002727976688153)
  ·
    refine ⟨13719554661752045982516115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18292739549002727976688153 13719554661752045982516115)
    ·
      refine ⟨20579331992628068973774173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719554661752045982516115 20579331992628068973774173)
      ·
        refine ⟨7717249497235525865165315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20579331992628068973774173 7717249497235525865165315)
        ·
          refine ⟨11575874245853288797747973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717249497235525865165315 11575874245853288797747973)
          ·
            refine ⟨2170476421097491649577745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11575874245853288797747973 2170476421097491649577745)
            ·
              refine ⟨1627857315823118737183309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2170476421097491649577745 1627857315823118737183309)
              ·
                refine ⟨610446493433669526443741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627857315823118737183309 610446493433669526443741)
                ·
                  refine ⟨228917435037626072416403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610446493433669526443741 228917435037626072416403)
                  ·
                    rfl

theorem cell21_1003084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1003084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003084 prefixEnd_1003084 := by exact prefixLift 1003084
  have htrace : WordTrace (prefixWord ++ tailWord_1003084) baseStart_1003084 baseEnd_1003084 := by
    simpa [prefixWord, tailWord_1003084, baseEnd_1003084] using wordTrace_append hprefix tailTrace_1003084
  have hstable : (prefixWord ++ tailWord_1003084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003084).length < 2 ^ (prefixWord ++ tailWord_1003084).sum := by decide
  have hdescent : baseEnd_1003084 < baseStart_1003084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003095 : List Nat := [1, 1, 3, 2, 2, 4, 8]
def baseStart_1003095 : Nat := 118140960795 + 1003095 * 2 ^ 59
def prefixEnd_1003095 : Nat := 4983230072969 + 3 ^ 40 * 1003095 * 2
def baseEnd_1003095 : Nat := 25435549487499166414783

theorem tailTrace_1003095 : CollatzResearch.WordTrace tailWord_1003095 prefixEnd_1003095 25435549487499166414783 := by
  unfold tailWord_1003095
  simp only [CollatzResearch.WordTrace]
  refine ⟨36585880300965604832026739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24390586867310403221351159 36585880300965604832026739)
  ·
    refine ⟨54878820451448407248040109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36585880300965604832026739 54878820451448407248040109)
    ·
      refine ⟨20579557669293152718015041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54878820451448407248040109 20579557669293152718015041)
      ·
        refine ⟨15434668251969864538511281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20579557669293152718015041 15434668251969864538511281)
        ·
          refine ⟨11576001188977398403883461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15434668251969864538511281 11576001188977398403883461)
          ·
            refine ⟨2170500222933262200728149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11576001188977398403883461 2170500222933262200728149)
            ·
              refine ⟨25435549487499166414783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2170500222933262200728149 25435549487499166414783)
              ·
                rfl

theorem cell21_1003095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_1003095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003095 prefixEnd_1003095 := by exact prefixLift 1003095
  have htrace : WordTrace (prefixWord ++ tailWord_1003095) baseStart_1003095 baseEnd_1003095 := by
    simpa [prefixWord, tailWord_1003095, baseEnd_1003095] using wordTrace_append hprefix tailTrace_1003095
  have hstable : (prefixWord ++ tailWord_1003095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003095).length < 2 ^ (prefixWord ++ tailWord_1003095).sum := by decide
  have hdescent : baseEnd_1003095 < baseStart_1003095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003101 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1003101 : Nat := 118140960795 + 1003101 * 2 ^ 59
def prefixEnd_1003101 : Nat := 4983230072969 + 3 ^ 40 * 1003101 * 2
def baseEnd_1003101 : Nat := 228921314669237820633035

theorem tailTrace_1003101 : CollatzResearch.WordTrace tailWord_1003101 prefixEnd_1003101 228921314669237820633035 := by
  unfold tailWord_1003101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586099138943867856745157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24390732759295911904496771 36586099138943867856745157)
  ·
    refine ⟨6859893588551975223139717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36586099138943867856745157 6859893588551975223139717)
    ·
      refine ⟨1286230047853495354338697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6859893588551975223139717 1286230047853495354338697)
      ·
        refine ⟨964672535890121515754023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286230047853495354338697 964672535890121515754023)
        ·
          refine ⟨1447008803835182273631035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964672535890121515754023 1447008803835182273631035)
          ·
            refine ⟨2170513205752773410446553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447008803835182273631035 2170513205752773410446553)
            ·
              refine ⟨1627884904314580057834915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2170513205752773410446553 1627884904314580057834915)
              ·
                refine ⟨2441827356471870086752373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627884904314580057834915 2441827356471870086752373)
                ·
                  refine ⟨228921314669237820633035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2441827356471870086752373 228921314669237820633035)
                  ·
                    rfl

theorem cell21_1003101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1003101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003101 prefixEnd_1003101 := by exact prefixLift 1003101
  have htrace : WordTrace (prefixWord ++ tailWord_1003101) baseStart_1003101 baseEnd_1003101 := by
    simpa [prefixWord, tailWord_1003101, baseEnd_1003101] using wordTrace_append hprefix tailTrace_1003101
  have hstable : (prefixWord ++ tailWord_1003101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003101).length < 2 ^ (prefixWord ++ tailWord_1003101).sum := by decide
  have hdescent : baseEnd_1003101 < baseStart_1003101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003171 : List Nat := [1, 1, 1, 4, 1, 1, 6, 6]
def baseStart_1003171 : Nat := 118140960795 + 1003171 * 2 ^ 59
def prefixEnd_1003171 : Nat := 4983230072969 + 3 ^ 40 * 1003171 * 2
def baseEnd_1003171 : Nat := 76312429874311084822075

theorem tailTrace_1003171 : CollatzResearch.WordTrace tailWord_1003171 prefixEnd_1003171 76312429874311084822075 := by
  unfold tailWord_1003171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36588652248690269811793367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24392434832460179874528911 36588652248690269811793367)
  ·
    refine ⟨54882978373035404717690051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36588652248690269811793367 54882978373035404717690051)
    ·
      refine ⟨82324467559553107076535077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54882978373035404717690051 82324467559553107076535077)
      ·
        refine ⟨15435837667416207576850327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82324467559553107076535077 15435837667416207576850327)
        ·
          refine ⟨23153756501124311365275491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435837667416207576850327 23153756501124311365275491)
          ·
            refine ⟨34730634751686467047913237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153756501124311365275491 34730634751686467047913237)
            ·
              refine ⟨1627998503985303142870933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34730634751686467047913237 1627998503985303142870933)
              ·
                refine ⟨76312429874311084822075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627998503985303142870933 76312429874311084822075)
                ·
                  rfl

theorem cell21_1003171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_1003171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003171 prefixEnd_1003171 := by exact prefixLift 1003171
  have htrace : WordTrace (prefixWord ++ tailWord_1003171) baseStart_1003171 baseEnd_1003171 := by
    simpa [prefixWord, tailWord_1003171, baseEnd_1003171] using wordTrace_append hprefix tailTrace_1003171
  have hstable : (prefixWord ++ tailWord_1003171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003171).length < 2 ^ (prefixWord ++ tailWord_1003171).sum := by decide
  have hdescent : baseEnd_1003171 < baseStart_1003171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003278 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1003278 : Nat := 118140960795 + 1003278 * 2 ^ 59
def prefixEnd_1003278 : Nat := 4983230072969 + 3 ^ 40 * 1003278 * 2
def baseEnd_1003278 : Nat := 228961708480724846182673

theorem tailTrace_1003278 : CollatzResearch.WordTrace tailWord_1003278 prefixEnd_1003278 228961708480724846182673 := by
  unfold tailWord_1003278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574069357412828385742311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24395036572868418057292325 4574069357412828385742311)
  ·
    refine ⟨6861104036119242578613467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574069357412828385742311 6861104036119242578613467)
    ·
      refine ⟨10291656054178863867920201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861104036119242578613467 10291656054178863867920201)
      ·
        refine ⟨7718742040634147900940151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10291656054178863867920201 7718742040634147900940151)
        ·
          refine ⟨11578113060951221851410227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718742040634147900940151 11578113060951221851410227)
          ·
            refine ⟨17367169591426832777115341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578113060951221851410227 17367169591426832777115341)
            ·
              refine ⟨6512688596785062291418253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17367169591426832777115341 6512688596785062291418253)
              ·
                refine ⟨2442258223794398359281845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6512688596785062291418253 2442258223794398359281845)
                ·
                  refine ⟨228961708480724846182673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2442258223794398359281845 228961708480724846182673)
                  ·
                    rfl

theorem cell21_1003278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1003278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003278 prefixEnd_1003278 := by exact prefixLift 1003278
  have htrace : WordTrace (prefixWord ++ tailWord_1003278) baseStart_1003278 baseEnd_1003278 := by
    simpa [prefixWord, tailWord_1003278, baseEnd_1003278] using wordTrace_append hprefix tailTrace_1003278
  have hstable : (prefixWord ++ tailWord_1003278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003278).length < 2 ^ (prefixWord ++ tailWord_1003278).sum := by decide
  have hdescent : baseEnd_1003278 < baseStart_1003278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003340 : List Nat := [2, 2, 1, 3, 4, 1, 2, 6]
def baseStart_1003340 : Nat := 118140960795 + 1003340 * 2 ^ 59
def prefixEnd_1003340 : Nat := 4983230072969 + 3 ^ 40 * 1003340 * 2
def baseEnd_1003340 : Nat := 76325285908475505383071

theorem tailTrace_1003340 : CollatzResearch.WordTrace tailWord_1003340 prefixEnd_1003340 76325285908475505383071 := by
  unfold tailWord_1003340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297408092539005837347737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24396544123385341116463649 18297408092539005837347737)
  ·
    refine ⟨13723056069404254378010803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18297408092539005837347737 13723056069404254378010803)
    ·
      refine ⟨20584584104106381567016205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13723056069404254378010803 20584584104106381567016205)
      ·
        refine ⟨7719219039039893087631077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20584584104106381567016205 7719219039039893087631077)
        ·
          refine ⟨1447353569819979953930827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7719219039039893087631077 1447353569819979953930827)
          ·
            refine ⟨2171030354729969930896241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447353569819979953930827 2171030354729969930896241)
            ·
              refine ⟨1628272766047477448172181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171030354729969930896241 1628272766047477448172181)
              ·
                refine ⟨76325285908475505383071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1628272766047477448172181 76325285908475505383071)
                ·
                  rfl

theorem cell21_1003340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_1003340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003340 prefixEnd_1003340 := by exact prefixLift 1003340
  have htrace : WordTrace (prefixWord ++ tailWord_1003340) baseStart_1003340 baseEnd_1003340 := by
    simpa [prefixWord, tailWord_1003340, baseEnd_1003340] using wordTrace_append hprefix tailTrace_1003340
  have hstable : (prefixWord ++ tailWord_1003340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003340).length < 2 ^ (prefixWord ++ tailWord_1003340).sum := by decide
  have hdescent : baseEnd_1003340 < baseStart_1003340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003385 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_1003385 : Nat := 118140960795 + 1003385 * 2 ^ 59
def prefixEnd_1003385 : Nat := 4983230072969 + 3 ^ 40 * 1003385 * 2
def baseEnd_1003385 : Nat := 228986127338516437899121

theorem tailTrace_1003385 : CollatzResearch.WordTrace tailWord_1003385 prefixEnd_1003385 228986127338516437899121 := by
  unfold tailWord_1003385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36596457469914984360083609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24397638313276656240055739 36596457469914984360083609)
  ·
    refine ⟨27447343102436238270062707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36596457469914984360083609 27447343102436238270062707)
    ·
      refine ⟨41171014653654357405094061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27447343102436238270062707 41171014653654357405094061)
      ·
        refine ⟨15439130495120384026910273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41171014653654357405094061 15439130495120384026910273)
        ·
          refine ⟨11579347871340288020182705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439130495120384026910273 11579347871340288020182705)
          ·
            refine ⟨8684510903505216015137029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11579347871340288020182705 8684510903505216015137029)
            ·
              refine ⟨1628345794407228002838193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8684510903505216015137029 1628345794407228002838193)
              ·
                refine ⟨1221259345805421002128645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628345794407228002838193 1221259345805421002128645)
                ·
                  refine ⟨228986127338516437899121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221259345805421002128645 228986127338516437899121)
                  ·
                    rfl

theorem cell21_1003385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_1003385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003385 prefixEnd_1003385 := by exact prefixLift 1003385
  have htrace : WordTrace (prefixWord ++ tailWord_1003385) baseStart_1003385 baseEnd_1003385 := by
    simpa [prefixWord, tailWord_1003385, baseEnd_1003385] using wordTrace_append hprefix tailTrace_1003385
  have hstable : (prefixWord ++ tailWord_1003385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003385).length < 2 ^ (prefixWord ++ tailWord_1003385).sum := by decide
  have hdescent : baseEnd_1003385 < baseStart_1003385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003422 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1003422 : Nat := 118140960795 + 1003422 * 2 ^ 59
def prefixEnd_1003422 : Nat := 4983230072969 + 3 ^ 40 * 1003422 * 2
def baseEnd_1003422 : Nat := 228994571242612595782379

theorem tailTrace_1003422 : CollatzResearch.WordTrace tailWord_1003422 prefixEnd_1003422 228994571242612595782379 := by
  unfold tailWord_1003422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574725871347617459897565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24398537980520626452787013 4574725871347617459897565)
  ·
    refine ⟨1715522201755356547461587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4574725871347617459897565 1715522201755356547461587)
    ·
      refine ⟨2573283302633034821192381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715522201755356547461587 2573283302633034821192381)
      ·
        refine ⟨964981238487388057947143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2573283302633034821192381 964981238487388057947143)
        ·
          refine ⟨1447471857731082086920715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964981238487388057947143 1447471857731082086920715)
          ·
            refine ⟨2171207786596623130381073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447471857731082086920715 2171207786596623130381073)
            ·
              refine ⟨1628405839947467347785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171207786596623130381073 1628405839947467347785805)
              ·
                refine ⟨610652189980300255419677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628405839947467347785805 610652189980300255419677)
                ·
                  refine ⟨228994571242612595782379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610652189980300255419677 228994571242612595782379)
                  ·
                    rfl

theorem cell21_1003422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1003422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003422 prefixEnd_1003422 := by exact prefixLift 1003422
  have htrace : WordTrace (prefixWord ++ tailWord_1003422) baseStart_1003422 baseEnd_1003422 := by
    simpa [prefixWord, tailWord_1003422, baseEnd_1003422] using wordTrace_append hprefix tailTrace_1003422
  have hstable : (prefixWord ++ tailWord_1003422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003422).length < 2 ^ (prefixWord ++ tailWord_1003422).sum := by decide
  have hdescent : baseEnd_1003422 < baseStart_1003422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003481 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 3]
def baseStart_1003481 : Nat := 118140960795 + 1003481 * 2 ^ 59
def prefixEnd_1003481 : Nat := 4983230072969 + 3 ^ 40 * 1003481 * 2
def baseEnd_1003481 : Nat := 229008035846441604298925

theorem tailTrace_1003481 : CollatzResearch.WordTrace tailWord_1003481 prefixEnd_1003481 229008035846441604298925 := by
  unfold tailWord_1003481
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599958877567192755578297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24399972585044795170385531 36599958877567192755578297)
  ·
    refine ⟨27449969158175394566683723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36599958877567192755578297 27449969158175394566683723)
    ·
      refine ⟨41174953737263091850025585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449969158175394566683723 41174953737263091850025585)
      ·
        refine ⟨30881215302947318887519189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41174953737263091850025585 30881215302947318887519189)
        ·
          refine ⟨723778483662827786426231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30881215302947318887519189 723778483662827786426231)
          ·
            refine ⟨1085667725494241679639347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723778483662827786426231 1085667725494241679639347)
            ·
              refine ⟨1628501588241362519459021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085667725494241679639347 1628501588241362519459021)
              ·
                refine ⟨610688095590510944797133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628501588241362519459021 610688095590510944797133)
                ·
                  refine ⟨229008035846441604298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610688095590510944797133 229008035846441604298925)
                  ·
                    rfl

theorem cell21_1003481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_1003481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003481 prefixEnd_1003481 := by exact prefixLift 1003481
  have htrace : WordTrace (prefixWord ++ tailWord_1003481) baseStart_1003481 baseEnd_1003481 := by
    simpa [prefixWord, tailWord_1003481, baseEnd_1003481] using wordTrace_append hprefix tailTrace_1003481
  have hstable : (prefixWord ++ tailWord_1003481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003481).length < 2 ^ (prefixWord ++ tailWord_1003481).sum := by decide
  have hdescent : baseEnd_1003481 < baseStart_1003481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003489 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1003489 : Nat := 118140960795 + 1003489 * 2 ^ 59
def prefixEnd_1003489 : Nat := 4983230072969 + 3 ^ 40 * 1003489 * 2
def baseEnd_1003489 : Nat := 229009861555435368165575

theorem tailTrace_1003489 : CollatzResearch.WordTrace tailWord_1003489 prefixEnd_1003489 229009861555435368165575 := by
  unfold tailWord_1003489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36600250661538210121869521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24400167107692140081246347 36600250661538210121869521)
  ·
    refine ⟨27450187996153657591402141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36600250661538210121869521 27450187996153657591402141)
    ·
      refine ⟨10293820498557621596775803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27450187996153657591402141 10293820498557621596775803)
      ·
        refine ⟨15440730747836432395163705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293820498557621596775803 15440730747836432395163705)
        ·
          refine ⟨11580548060877324296372779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15440730747836432395163705 11580548060877324296372779)
          ·
            refine ⟨17370822091315986444559169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580548060877324296372779 17370822091315986444559169)
            ·
              refine ⟨13028116568486989833419377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17370822091315986444559169 13028116568486989833419377)
              ·
                refine ⟨9771087426365242375064533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028116568486989833419377 9771087426365242375064533)
                ·
                  refine ⟨229009861555435368165575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9771087426365242375064533 229009861555435368165575)
                  ·
                    rfl

theorem cell21_1003489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1003489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003489 prefixEnd_1003489 := by exact prefixLift 1003489
  have htrace : WordTrace (prefixWord ++ tailWord_1003489) baseStart_1003489 baseEnd_1003489 := by
    simpa [prefixWord, tailWord_1003489, baseEnd_1003489] using wordTrace_append hprefix tailTrace_1003489
  have hstable : (prefixWord ++ tailWord_1003489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003489).length < 2 ^ (prefixWord ++ tailWord_1003489).sum := by decide
  have hdescent : baseEnd_1003489 < baseStart_1003489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003610 : List Nat := [3, 1, 1, 2, 1, 1, 12]
def baseStart_1003610 : Nat := 118140960795 + 1003610 * 2 ^ 59
def prefixEnd_1003610 : Nat := 4983230072969 + 3 ^ 40 * 1003610 * 2
def baseEnd_1003610 : Nat := 25448608378218449627629

theorem tailTrace_1003610 : CollatzResearch.WordTrace tailWord_1003610 prefixEnd_1003610 25448608378218449627629 := by
  unfold tailWord_1003610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151165973524961946756071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24403109262733231858016189 9151165973524961946756071)
  ·
    refine ⟨13726748960287442920134107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151165973524961946756071 13726748960287442920134107)
    ·
      refine ⟨20590123440431164380201161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13726748960287442920134107 20590123440431164380201161)
      ·
        refine ⟨15442592580323373285150871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20590123440431164380201161 15442592580323373285150871)
        ·
          refine ⟨23163888870485059927726307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15442592580323373285150871 23163888870485059927726307)
          ·
            refine ⟨34745833305727589891589461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23163888870485059927726307 34745833305727589891589461)
            ·
              refine ⟨25448608378218449627629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34745833305727589891589461 25448608378218449627629)
              ·
                rfl

theorem cell21_1003610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 12].length) (baseStart_1003610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003610 prefixEnd_1003610 := by exact prefixLift 1003610
  have htrace : WordTrace (prefixWord ++ tailWord_1003610) baseStart_1003610 baseEnd_1003610 := by
    simpa [prefixWord, tailWord_1003610, baseEnd_1003610] using wordTrace_append hprefix tailTrace_1003610
  have hstable : (prefixWord ++ tailWord_1003610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003610).length < 2 ^ (prefixWord ++ tailWord_1003610).sum := by decide
  have hdescent : baseEnd_1003610 < baseStart_1003610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003630 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1003630 : Nat := 118140960795 + 1003630 * 2 ^ 59
def prefixEnd_1003630 : Nat := 4983230072969 + 3 ^ 40 * 1003630 * 2
def baseEnd_1003630 : Nat := 229042039676450456315287

theorem tailTrace_1003630 : CollatzResearch.WordTrace tailWord_1003630 prefixEnd_1003630 229042039676450456315287 := by
  unfold tailWord_1003630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575674169253423900344043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24403595569351594135168229 4575674169253423900344043)
  ·
    refine ⟨6863511253880135850516065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4575674169253423900344043 6863511253880135850516065)
    ·
      refine ⟨5147633440410101887887049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6863511253880135850516065 5147633440410101887887049)
      ·
        refine ⟨3860725080307576415915287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5147633440410101887887049 3860725080307576415915287)
        ·
          refine ⟨5791087620461364623872931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860725080307576415915287 5791087620461364623872931)
          ·
            refine ⟨8686631430692046935809397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791087620461364623872931 8686631430692046935809397)
            ·
              refine ⟨814371696627379400232131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8686631430692046935809397 814371696627379400232131)
              ·
                refine ⟨1221557544941069100348197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814371696627379400232131 1221557544941069100348197)
                ·
                  refine ⟨229042039676450456315287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221557544941069100348197 229042039676450456315287)
                  ·
                    rfl

theorem cell21_1003630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1003630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003630 prefixEnd_1003630 := by exact prefixLift 1003630
  have htrace : WordTrace (prefixWord ++ tailWord_1003630) baseStart_1003630 baseEnd_1003630 := by
    simpa [prefixWord, tailWord_1003630, baseEnd_1003630] using wordTrace_append hprefix tailTrace_1003630
  have hstable : (prefixWord ++ tailWord_1003630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003630).length < 2 ^ (prefixWord ++ tailWord_1003630).sum := by decide
  have hdescent : baseEnd_1003630 < baseStart_1003630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003644 : List Nat := [2, 2, 2, 1, 1, 6, 2, 5]
def baseStart_1003644 : Nat := 118140960795 + 1003644 * 2 ^ 59
def prefixEnd_1003644 : Nat := 4983230072969 + 3 ^ 40 * 1003644 * 2
def baseEnd_1003644 : Nat := 76348411555729847693975

theorem tailTrace_1003644 : CollatzResearch.WordTrace tailWord_1003644 prefixEnd_1003644 76348411555729847693975 := by
  unfold tailWord_1003644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302951987988335796880993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24403935983984447729174657 18302951987988335796880993)
  ·
    refine ⟨13727213990991251847660745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18302951987988335796880993 13727213990991251847660745)
    ·
      refine ⟨10295410493243438885745559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13727213990991251847660745 10295410493243438885745559)
      ·
        refine ⟨15443115739865158328618339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10295410493243438885745559 15443115739865158328618339)
        ·
          refine ⟨23164673609797737492927509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15443115739865158328618339 23164673609797737492927509)
          ·
            refine ⟨1085844075459268944980977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23164673609797737492927509 1085844075459268944980977)
            ·
              refine ⟨814383056594451708735733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085844075459268944980977 814383056594451708735733)
              ·
                refine ⟨76348411555729847693975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814383056594451708735733 76348411555729847693975)
                ·
                  rfl

theorem cell21_1003644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_1003644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003644 prefixEnd_1003644 := by exact prefixLift 1003644
  have htrace : WordTrace (prefixWord ++ tailWord_1003644) baseStart_1003644 baseEnd_1003644 := by
    simpa [prefixWord, tailWord_1003644, baseEnd_1003644] using wordTrace_append hprefix tailTrace_1003644
  have hstable : (prefixWord ++ tailWord_1003644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003644).length < 2 ^ (prefixWord ++ tailWord_1003644).sum := by decide
  have hdescent : baseEnd_1003644 < baseStart_1003644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003793 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1003793 : Nat := 118140960795 + 1003793 * 2 ^ 59
def prefixEnd_1003793 : Nat := 4983230072969 + 3 ^ 40 * 1003793 * 2
def baseEnd_1003793 : Nat := 229079238497198395098287

theorem tailTrace_1003793 : CollatzResearch.WordTrace tailWord_1003793 prefixEnd_1003793 229079238497198395098287 := by
  unfold tailWord_1003793
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611338452436870040936033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24407558968291246693957355 36611338452436870040936033)
  ·
    refine ⟨27458503839327652530702025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36611338452436870040936033 27458503839327652530702025)
    ·
      refine ⟨20593877879495739398026519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27458503839327652530702025 20593877879495739398026519)
      ·
        refine ⟨30890816819243609097039779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593877879495739398026519 30890816819243609097039779)
        ·
          refine ⟨46336225228865413645559669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890816819243609097039779 46336225228865413645559669)
          ·
            refine ⟨4344021115206132529271219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46336225228865413645559669 4344021115206132529271219)
            ·
              refine ⟨6516031672809198793906829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344021115206132529271219 6516031672809198793906829)
              ·
                refine ⟨2443511877303449547715061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6516031672809198793906829 2443511877303449547715061)
                ·
                  refine ⟨229079238497198395098287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443511877303449547715061 229079238497198395098287)
                  ·
                    rfl

theorem cell21_1003793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1003793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003793 prefixEnd_1003793 := by exact prefixLift 1003793
  have htrace : WordTrace (prefixWord ++ tailWord_1003793) baseStart_1003793 baseEnd_1003793 := by
    simpa [prefixWord, tailWord_1003793, baseEnd_1003793] using wordTrace_append hprefix tailTrace_1003793
  have hstable : (prefixWord ++ tailWord_1003793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003793).length < 2 ^ (prefixWord ++ tailWord_1003793).sum := by decide
  have hdescent : baseEnd_1003793 < baseStart_1003793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003810 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1003810 : Nat := 118140960795 + 1003810 * 2 ^ 59
def prefixEnd_1003810 : Nat := 4983230072969 + 3 ^ 40 * 1003810 * 2
def baseEnd_1003810 : Nat := 229083118128810143314919

theorem tailTrace_1003810 : CollatzResearch.WordTrace tailWord_1003810 prefixEnd_1003810 229083118128810143314919 := by
  unfold tailWord_1003810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152989623343820486076221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24407972328916854629536589 9152989623343820486076221)
  ·
    refine ⟨3432371108753932682278583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9152989623343820486076221 3432371108753932682278583)
    ·
      refine ⟨5148556663130899023417875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432371108753932682278583 5148556663130899023417875)
      ·
        refine ⟨7722834994696348535126813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148556663130899023417875 7722834994696348535126813)
        ·
          refine ⟨2896063123011130700672555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7722834994696348535126813 2896063123011130700672555)
          ·
            refine ⟨4344094684516696051008833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896063123011130700672555 4344094684516696051008833)
            ·
              refine ⟨3258071013387522038256625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344094684516696051008833 3258071013387522038256625)
              ·
                refine ⟨2443553260040641528692469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258071013387522038256625 2443553260040641528692469)
                ·
                  refine ⟨229083118128810143314919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443553260040641528692469 229083118128810143314919)
                  ·
                    rfl

theorem cell21_1003810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1003810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003810 prefixEnd_1003810 := by exact prefixLift 1003810
  have htrace : WordTrace (prefixWord ++ tailWord_1003810) baseStart_1003810 baseEnd_1003810 := by
    simpa [prefixWord, tailWord_1003810, baseEnd_1003810] using wordTrace_append hprefix tailTrace_1003810
  have hstable : (prefixWord ++ tailWord_1003810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003810).length < 2 ^ (prefixWord ++ tailWord_1003810).sum := by decide
  have hdescent : baseEnd_1003810 < baseStart_1003810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003813 : List Nat := [1, 3, 1, 2, 6, 1, 2, 5]
def baseStart_1003813 : Nat := 118140960795 + 1003813 * 2 ^ 59
def prefixEnd_1003813 : Nat := 4983230072969 + 3 ^ 40 * 1003813 * 2
def baseEnd_1003813 : Nat := 76361267589894268254971

theorem tailTrace_1003813 : CollatzResearch.WordTrace tailWord_1003813 prefixEnd_1003813 76361267589894268254971 := by
  unfold tailWord_1003813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612067912364413456664093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24408045274909608971109395 36612067912364413456664093)
  ·
    refine ⟨13729525467136655046249035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36612067912364413456664093 13729525467136655046249035)
    ·
      refine ⟨20594288200704982569373553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13729525467136655046249035 20594288200704982569373553)
      ·
        refine ⟨15445716150528736927030165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20594288200704982569373553 15445716150528736927030165)
        ·
          refine ⟨724017944556034543454539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15445716150528736927030165 724017944556034543454539)
          ·
            refine ⟨1086026916834051815181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724017944556034543454539 1086026916834051815181809)
            ·
              refine ⟨814520187625538861386357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086026916834051815181809 814520187625538861386357)
              ·
                refine ⟨76361267589894268254971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814520187625538861386357 76361267589894268254971)
                ·
                  rfl

theorem cell21_1003813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].length) (baseStart_1003813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003813 prefixEnd_1003813 := by exact prefixLift 1003813
  have htrace : WordTrace (prefixWord ++ tailWord_1003813) baseStart_1003813 baseEnd_1003813 := by
    simpa [prefixWord, tailWord_1003813, baseEnd_1003813] using wordTrace_append hprefix tailTrace_1003813
  have hstable : (prefixWord ++ tailWord_1003813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003813).length < 2 ^ (prefixWord ++ tailWord_1003813).sum := by decide
  have hdescent : baseEnd_1003813 < baseStart_1003813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003844 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1003844 : Nat := 118140960795 + 1003844 * 2 ^ 59
def prefixEnd_1003844 : Nat := 4983230072969 + 3 ^ 40 * 1003844 * 2
def baseEnd_1003844 : Nat := 229090877392033639748183

theorem tailTrace_1003844 : CollatzResearch.WordTrace tailWord_1003844 prefixEnd_1003844 229090877392033639748183 := by
  unfold tailWord_1003844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306599287626052875521293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24408799050168070500695057 18306599287626052875521293)
  ·
    refine ⟨6864974732859769828320485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18306599287626052875521293 6864974732859769828320485)
    ·
      refine ⟨1287182762411206842810091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6864974732859769828320485 1287182762411206842810091)
      ·
        refine ⟨1930774143616810264215137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287182762411206842810091 1930774143616810264215137)
        ·
          refine ⟨1448080607712607698161353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930774143616810264215137 1448080607712607698161353)
          ·
            refine ⟨1086060455784455773621015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448080607712607698161353 1086060455784455773621015)
            ·
              refine ⟨1629090683676683660431523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086060455784455773621015 1629090683676683660431523)
              ·
                refine ⟨2443636025515025490647285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629090683676683660431523 2443636025515025490647285)
                ·
                  refine ⟨229090877392033639748183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443636025515025490647285 229090877392033639748183)
                  ·
                    rfl

theorem cell21_1003844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1003844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003844 prefixEnd_1003844 := by exact prefixLift 1003844
  have htrace : WordTrace (prefixWord ++ tailWord_1003844) baseStart_1003844 baseEnd_1003844 := by
    simpa [prefixWord, tailWord_1003844, baseEnd_1003844] using wordTrace_append hprefix tailTrace_1003844
  have hstable : (prefixWord ++ tailWord_1003844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003844).length < 2 ^ (prefixWord ++ tailWord_1003844).sum := by decide
  have hdescent : baseEnd_1003844 < baseStart_1003844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003906 : List Nat := [3, 4, 2, 1, 3, 1, 1, 6]
def baseStart_1003906 : Nat := 118140960795 + 1003906 * 2 ^ 59
def prefixEnd_1003906 : Nat := 4983230072969 + 3 ^ 40 * 1003906 * 2
def baseEnd_1003906 : Nat := 76368342212245103238241

theorem tailTrace_1003906 : CollatzResearch.WordTrace tailWord_1003906 prefixEnd_1003906 76368342212245103238241 := by
  unfold tailWord_1003906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153864975256872584949893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24410306600684993559866381 9153864975256872584949893)
  ·
    refine ⟨1716349682860663609678105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9153864975256872584949893 1716349682860663609678105)
    ·
      refine ⟨1287262262145497707258579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716349682860663609678105 1287262262145497707258579)
      ·
        refine ⟨1930893393218246560887869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287262262145497707258579 1930893393218246560887869)
        ·
          refine ⟨724085022456842460332951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930893393218246560887869 724085022456842460332951)
          ·
            refine ⟨1086127533685263690499427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724085022456842460332951 1086127533685263690499427)
            ·
              refine ⟨1629191300527895535749141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086127533685263690499427 1629191300527895535749141)
              ·
                refine ⟨76368342212245103238241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1629191300527895535749141 76368342212245103238241)
                ·
                  rfl

theorem cell21_1003906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_1003906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1003906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1003906 prefixEnd_1003906 := by exact prefixLift 1003906
  have htrace : WordTrace (prefixWord ++ tailWord_1003906) baseStart_1003906 baseEnd_1003906 := by
    simpa [prefixWord, tailWord_1003906, baseEnd_1003906] using wordTrace_append hprefix tailTrace_1003906
  have hstable : (prefixWord ++ tailWord_1003906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003906).length < 2 ^ (prefixWord ++ tailWord_1003906).sum := by decide
  have hdescent : baseEnd_1003906 < baseStart_1003906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004072 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_1004072 : Nat := 118140960795 + 1004072 * 2 ^ 59
def prefixEnd_1004072 : Nat := 4983230072969 + 3 ^ 40 * 1004072 * 2
def baseEnd_1004072 : Nat := 229142910098355909947717

theorem tailTrace_1004072 : CollatzResearch.WordTrace tailWord_1004072 prefixEnd_1004072 229142910098355909947717 := by
  unfold tailWord_1004072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310757209213050345171235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24414342945617400460228313 18310757209213050345171235)
  ·
    refine ⟨27466135813819575517756853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18310757209213050345171235 27466135813819575517756853)
    ·
      refine ⟨2574950232545585204789705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27466135813819575517756853 2574950232545585204789705)
      ·
        refine ⟨1931212674409188903592279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2574950232545585204789705 1931212674409188903592279)
        ·
          refine ⟨2896819011613783355388419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931212674409188903592279 2896819011613783355388419)
          ·
            refine ⟨4345228517420675033082629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896819011613783355388419 4345228517420675033082629)
            ·
              refine ⟨814730347016376568702993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4345228517420675033082629 814730347016376568702993)
              ·
                refine ⟨611047760262282426527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814730347016376568702993 611047760262282426527245)
                ·
                  refine ⟨229142910098355909947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611047760262282426527245 229142910098355909947717)
                  ·
                    rfl

theorem cell21_1004072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_1004072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004072 prefixEnd_1004072 := by exact prefixLift 1004072
  have htrace : WordTrace (prefixWord ++ tailWord_1004072) baseStart_1004072 baseEnd_1004072 := by
    simpa [prefixWord, tailWord_1004072, baseEnd_1004072] using wordTrace_append hprefix tailTrace_1004072
  have hstable : (prefixWord ++ tailWord_1004072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004072).length < 2 ^ (prefixWord ++ tailWord_1004072).sum := by decide
  have hdescent : baseEnd_1004072 < baseStart_1004072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004097 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1004097 : Nat := 118140960795 + 1004097 * 2 ^ 59
def prefixEnd_1004097 : Nat := 4983230072969 + 3 ^ 40 * 1004097 * 2
def baseEnd_1004097 : Nat := 229148615438961422030999

theorem tailTrace_1004097 : CollatzResearch.WordTrace tailWord_1004097 prefixEnd_1004097 229148615438961422030999 := by
  unfold tailWord_1004097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622426243335529960002545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24414950828890353306668363 36622426243335529960002545)
  ·
    refine ⟨27466819682501647470001909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36622426243335529960002545 27466819682501647470001909)
    ·
      refine ⟨2575014345234529450312679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27466819682501647470001909 2575014345234529450312679)
      ·
        refine ⟨3862521517851794175469019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575014345234529450312679 3862521517851794175469019)
        ·
          refine ⟨5793782276777691263203529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862521517851794175469019 5793782276777691263203529)
          ·
            refine ⟨4345336707583268447402647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793782276777691263203529 4345336707583268447402647)
            ·
              refine ⟨6518005061374902671103971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345336707583268447402647 6518005061374902671103971)
              ·
                refine ⟨9777007592062354006655957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518005061374902671103971 9777007592062354006655957)
                ·
                  refine ⟨229148615438961422030999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9777007592062354006655957 229148615438961422030999)
                  ·
                    rfl

theorem cell21_1004097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1004097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004097 prefixEnd_1004097 := by exact prefixLift 1004097
  have htrace : WordTrace (prefixWord ++ tailWord_1004097) baseStart_1004097 baseEnd_1004097 := by
    simpa [prefixWord, tailWord_1004097, baseEnd_1004097] using wordTrace_append hprefix tailTrace_1004097
  have hstable : (prefixWord ++ tailWord_1004097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004097).length < 2 ^ (prefixWord ++ tailWord_1004097).sum := by decide
  have hdescent : baseEnd_1004097 < baseStart_1004097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004128 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1004128 : Nat := 118140960795 + 1004128 * 2 ^ 59
def prefixEnd_1004128 : Nat := 4983230072969 + 3 ^ 40 * 1004128 * 2
def baseEnd_1004128 : Nat := 229155690061312257014269

theorem tailTrace_1004128 : CollatzResearch.WordTrace tailWord_1004128 prefixEnd_1004128 229155690061312257014269 := by
  unfold tailWord_1004128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311778453111611127190519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24415704604148814836254025 18311778453111611127190519)
  ·
    refine ⟨27467667679667416690785779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18311778453111611127190519 27467667679667416690785779)
    ·
      refine ⟨41201501519501125036178669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27467667679667416690785779 41201501519501125036178669)
      ·
        refine ⟨15450563069812921888567001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41201501519501125036178669 15450563069812921888567001)
        ·
          refine ⟨11587922302359691416425251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15450563069812921888567001 11587922302359691416425251)
          ·
            refine ⟨17381883453539537124637877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587922302359691416425251 17381883453539537124637877)
            ·
              refine ⟨1629551573769331605434801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17381883453539537124637877 1629551573769331605434801)
              ·
                refine ⟨1222163680326998704076101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629551573769331605434801 1222163680326998704076101)
                ·
                  refine ⟨229155690061312257014269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222163680326998704076101 229155690061312257014269)
                  ·
                    rfl

theorem cell21_1004128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1004128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004128 prefixEnd_1004128 := by exact prefixLift 1004128
  have htrace : WordTrace (prefixWord ++ tailWord_1004128) baseStart_1004128 baseEnd_1004128 := by
    simpa [prefixWord, tailWord_1004128, baseEnd_1004128] using wordTrace_append hprefix tailTrace_1004128
  have hstable : (prefixWord ++ tailWord_1004128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004128).length < 2 ^ (prefixWord ++ tailWord_1004128).sum := by decide
  have hdescent : baseEnd_1004128 < baseStart_1004128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004201 : List Nat := [1, 2, 1, 1, 1, 1, 2, 12]
def baseStart_1004201 : Nat := 118140960795 + 1004201 * 2 ^ 59
def prefixEnd_1004201 : Nat := 4983230072969 + 3 ^ 40 * 1004201 * 2
def baseEnd_1004201 : Nat := 76390783218626784099151

theorem tailTrace_1004201 : CollatzResearch.WordTrace tailWord_1004201 prefixEnd_1004201 76390783218626784099151 := by
  unfold tailWord_1004201
  simp only [CollatzResearch.WordTrace]
  refine ⟨36626219434958755721788457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24417479623305837147858971 36626219434958755721788457)
  ·
    refine ⟨27469664576219066791341343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36626219434958755721788457 27469664576219066791341343)
    ·
      refine ⟨41204496864328600187012015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27469664576219066791341343 41204496864328600187012015)
      ·
        refine ⟨61806745296492900280518023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41204496864328600187012015 61806745296492900280518023)
        ·
          refine ⟨92710117944739350420777035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61806745296492900280518023 92710117944739350420777035)
          ·
            refine ⟨139065176917109025631165553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92710117944739350420777035 139065176917109025631165553)
            ·
              refine ⟨104298882687831769223374165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139065176917109025631165553 104298882687831769223374165)
              ·
                refine ⟨76390783218626784099151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 104298882687831769223374165 76390783218626784099151)
                ·
                  rfl

theorem cell21_1004201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_1004201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004201 prefixEnd_1004201 := by exact prefixLift 1004201
  have htrace : WordTrace (prefixWord ++ tailWord_1004201) baseStart_1004201 baseEnd_1004201 := by
    simpa [prefixWord, tailWord_1004201, baseEnd_1004201] using wordTrace_append hprefix tailTrace_1004201
  have hstable : (prefixWord ++ tailWord_1004201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004201).length < 2 ^ (prefixWord ++ tailWord_1004201).sum := by decide
  have hdescent : baseEnd_1004201 < baseStart_1004201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004252 : List Nat := [2, 2, 5, 1, 1, 3, 1, 6]
def baseStart_1004252 : Nat := 118140960795 + 1004252 * 2 ^ 59
def prefixEnd_1004252 : Nat := 4983230072969 + 3 ^ 40 * 1004252 * 2
def baseEnd_1004252 : Nat := 76394662850238532315783

theorem tailTrace_1004252 : CollatzResearch.WordTrace tailWord_1004252 prefixEnd_1004252 76394662850238532315783 := by
  unfold tailWord_1004252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314039778886995715947505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24418719705182660954596673 18314039778886995715947505)
  ·
    refine ⟨13735529834165246786960629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18314039778886995715947505 13735529834165246786960629)
    ·
      refine ⟨1287705921952991886277559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13735529834165246786960629 1287705921952991886277559)
      ·
        refine ⟨1931558882929487829416339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287705921952991886277559 1931558882929487829416339)
        ·
          refine ⟨2897338324394231744124509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931558882929487829416339 2897338324394231744124509)
          ·
            refine ⟨1086501871647836904046691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2897338324394231744124509 1086501871647836904046691)
            ·
              refine ⟨1629752807471755356070037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086501871647836904046691 1629752807471755356070037)
              ·
                refine ⟨76394662850238532315783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1629752807471755356070037 76394662850238532315783)
                ·
                  rfl

theorem cell21_1004252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_1004252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004252 prefixEnd_1004252 := by exact prefixLift 1004252
  have htrace : WordTrace (prefixWord ++ tailWord_1004252) baseStart_1004252 baseEnd_1004252 := by
    simpa [prefixWord, tailWord_1004252, baseEnd_1004252] using wordTrace_append hprefix tailTrace_1004252
  have hstable : (prefixWord ++ tailWord_1004252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004252).length < 2 ^ (prefixWord ++ tailWord_1004252).sum := by decide
  have hdescent : baseEnd_1004252 < baseStart_1004252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004339 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_1004339 : Nat := 118140960795 + 1004339 * 2 ^ 59
def prefixEnd_1004339 : Nat := 4983230072969 + 3 ^ 40 * 1004339 * 2
def baseEnd_1004339 : Nat := 229203843136022778997171

theorem tailTrace_1004339 : CollatzResearch.WordTrace tailWord_1004339 prefixEnd_1004339 229203843136022778997171 := by
  unfold tailWord_1004339
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631252708458805290312071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24420835138972536860208047 36631252708458805290312071)
  ·
    refine ⟨54946879062688207935468107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36631252708458805290312071 54946879062688207935468107)
    ·
      refine ⟨82420318594032311903202161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54946879062688207935468107 82420318594032311903202161)
      ·
        refine ⟨61815238945524233927401621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82420318594032311903202161 61815238945524233927401621)
        ·
          refine ⟨2897589325571448465346951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61815238945524233927401621 2897589325571448465346951)
          ·
            refine ⟨4346383988357172698020427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897589325571448465346951 4346383988357172698020427)
            ·
              refine ⟨6519575982535759047030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346383988357172698020427 6519575982535759047030641)
              ·
                refine ⟨4889681986901819285272981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6519575982535759047030641 4889681986901819285272981)
                ·
                  refine ⟨229203843136022778997171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4889681986901819285272981 229203843136022778997171)
                  ·
                    rfl

theorem cell21_1004339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_1004339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004339 prefixEnd_1004339 := by exact prefixLift 1004339
  have htrace : WordTrace (prefixWord ++ tailWord_1004339) baseStart_1004339 baseEnd_1004339 := by
    simpa [prefixWord, tailWord_1004339, baseEnd_1004339] using wordTrace_append hprefix tailTrace_1004339
  have hstable : (prefixWord ++ tailWord_1004339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004339).length < 2 ^ (prefixWord ++ tailWord_1004339).sum := by decide
  have hdescent : baseEnd_1004339 < baseStart_1004339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004370 : List Nat := [3, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1004370 : Nat := 118140960795 + 1004370 * 2 ^ 59
def prefixEnd_1004370 : Nat := 4983230072969 + 3 ^ 40 * 1004370 * 2
def baseEnd_1004370 : Nat := 76403639252791204660147

theorem tailTrace_1004370 : CollatzResearch.WordTrace tailWord_1004370 prefixEnd_1004370 76403639252791204660147 := by
  unfold tailWord_1004370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158095842836624396172641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24421588914230998389793709 9158095842836624396172641)
  ·
    refine ⟨6868571882127468297129481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9158095842836624396172641 6868571882127468297129481)
    ·
      refine ⟨5151428911595601222847111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6868571882127468297129481 5151428911595601222847111)
      ·
        refine ⟨7727143367393401834270667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151428911595601222847111 7727143367393401834270667)
        ·
          refine ⟨11590715051090102751406001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727143367393401834270667 11590715051090102751406001)
          ·
            refine ⟨8693036288317577063554501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590715051090102751406001 8693036288317577063554501)
            ·
              refine ⟨1629944304059545699416469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8693036288317577063554501 1629944304059545699416469)
              ·
                refine ⟨76403639252791204660147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1629944304059545699416469 76403639252791204660147)
                ·
                  rfl

theorem cell21_1004370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1004370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004370 prefixEnd_1004370 := by exact prefixLift 1004370
  have htrace : WordTrace (prefixWord ++ tailWord_1004370) baseStart_1004370 baseEnd_1004370 := by
    simpa [prefixWord, tailWord_1004370, baseEnd_1004370] using wordTrace_append hprefix tailTrace_1004370
  have hstable : (prefixWord ++ tailWord_1004370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004370).length < 2 ^ (prefixWord ++ tailWord_1004370).sum := by decide
  have hdescent : baseEnd_1004370 < baseStart_1004370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004384 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_1004384 : Nat := 118140960795 + 1004384 * 2 ^ 59
def prefixEnd_1004384 : Nat := 4983230072969 + 3 ^ 40 * 1004384 * 2
def baseEnd_1004384 : Nat := 229214112749112700747079

theorem tailTrace_1004384 : CollatzResearch.WordTrace tailWord_1004384 prefixEnd_1004384 229214112749112700747079 := by
  unfold tailWord_1004384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316446996647888987850103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24421929328863851983800137 18316446996647888987850103)
  ·
    refine ⟨27474670494971833481775155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18316446996647888987850103 27474670494971833481775155)
    ·
      refine ⟨41212005742457750222662733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27474670494971833481775155 41212005742457750222662733)
      ·
        refine ⟨15454502153421656333498525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41212005742457750222662733 15454502153421656333498525)
        ·
          refine ⟨5795438307533121125061947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15454502153421656333498525 5795438307533121125061947)
          ·
            refine ⟨8693157461299681687592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795438307533121125061947 8693157461299681687592921)
            ·
              refine ⟨6519868095974761265694691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693157461299681687592921 6519868095974761265694691)
              ·
                refine ⟨9779802143962141898542037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519868095974761265694691 9779802143962141898542037)
                ·
                  refine ⟨229214112749112700747079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9779802143962141898542037 229214112749112700747079)
                  ·
                    rfl

theorem cell21_1004384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_1004384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004384 prefixEnd_1004384 := by exact prefixLift 1004384
  have htrace : WordTrace (prefixWord ++ tailWord_1004384) baseStart_1004384 baseEnd_1004384 := by
    simpa [prefixWord, tailWord_1004384, baseEnd_1004384] using wordTrace_append hprefix tailTrace_1004384
  have hstable : (prefixWord ++ tailWord_1004384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004384).length < 2 ^ (prefixWord ++ tailWord_1004384).sum := by decide
  have hdescent : baseEnd_1004384 < baseStart_1004384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004415 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_1004415 : Nat := 118140960795 + 1004415 * 2 ^ 59
def prefixEnd_1004415 : Nat := 4983230072969 + 3 ^ 40 * 1004415 * 2
def baseEnd_1004415 : Nat := 229221187371463535730349

theorem tailTrace_1004415 : CollatzResearch.WordTrace tailWord_1004415 prefixEnd_1004415 229221187371463535730349 := by
  unfold tailWord_1004415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36634024656183470270078699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24422683104122313513385799 36634024656183470270078699)
  ·
    refine ⟨54951036984275205405118049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36634024656183470270078699 54951036984275205405118049)
    ·
      refine ⟨41213277738206404053838537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54951036984275205405118049 41213277738206404053838537)
      ·
        refine ⟨30909958303654803040378903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41213277738206404053838537 30909958303654803040378903)
        ·
          refine ⟨46364937455482204560568355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30909958303654803040378903 46364937455482204560568355)
          ·
            refine ⟨69547406183223306840852533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46364937455482204560568355 69547406183223306840852533)
            ·
              refine ⟨6520069329677185016329925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69547406183223306840852533 6520069329677185016329925)
              ·
                refine ⟨1222512999314472190561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6520069329677185016329925 1222512999314472190561861)
                ·
                  refine ⟨229221187371463535730349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222512999314472190561861 229221187371463535730349)
                  ·
                    rfl

theorem cell21_1004415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_1004415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004415 prefixEnd_1004415 := by exact prefixLift 1004415
  have htrace : WordTrace (prefixWord ++ tailWord_1004415) baseStart_1004415 baseEnd_1004415 := by
    simpa [prefixWord, tailWord_1004415, baseEnd_1004415] using wordTrace_append hprefix tailTrace_1004415
  have hstable : (prefixWord ++ tailWord_1004415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004415).length < 2 ^ (prefixWord ++ tailWord_1004415).sum := by decide
  have hdescent : baseEnd_1004415 < baseStart_1004415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004511 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 3]
def baseStart_1004511 : Nat := 118140960795 + 1004511 * 2 ^ 59
def prefixEnd_1004511 : Nat := 4983230072969 + 3 ^ 40 * 1004511 * 2
def baseEnd_1004511 : Nat := 229243095879388702130153

theorem tailTrace_1004511 : CollatzResearch.WordTrace tailWord_1004511 prefixEnd_1004511 229243095879388702130153 := by
  unfold tailWord_1004511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637526063835678665573387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24425017375890452443715591 36637526063835678665573387)
  ·
    refine ⟨54956289095753517998360081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36637526063835678665573387 54956289095753517998360081)
    ·
      refine ⟨41217216821815138498770061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54956289095753517998360081 41217216821815138498770061)
      ·
        refine ⟨15456456308180676937038773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41217216821815138498770061 15456456308180676937038773)
        ·
          refine ⟨1449042778891938462847385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15456456308180676937038773 1449042778891938462847385)
          ·
            refine ⟨1086782084168953847135539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449042778891938462847385 1086782084168953847135539)
            ·
              refine ⟨1630173126253430770703309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086782084168953847135539 1630173126253430770703309)
              ·
                refine ⟨611314922345036539013741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1630173126253430770703309 611314922345036539013741)
                ·
                  refine ⟨229243095879388702130153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611314922345036539013741 229243095879388702130153)
                  ·
                    rfl

theorem cell21_1004511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].length) (baseStart_1004511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004511 prefixEnd_1004511 := by exact prefixLift 1004511
  have htrace : WordTrace (prefixWord ++ tailWord_1004511) baseStart_1004511 baseEnd_1004511 := by
    simpa [prefixWord, tailWord_1004511, baseEnd_1004511] using wordTrace_append hprefix tailTrace_1004511
  have hstable : (prefixWord ++ tailWord_1004511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004511).length < 2 ^ (prefixWord ++ tailWord_1004511).sum := by decide
  have hdescent : baseEnd_1004511 < baseStart_1004511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004522 : List Nat := [3, 1, 3, 1, 2, 4, 7]
def baseStart_1004522 : Nat := 118140960795 + 1004522 * 2 ^ 59
def prefixEnd_1004522 : Nat := 4983230072969 + 3 ^ 40 * 1004522 * 2
def baseEnd_1004522 : Nat := 25471734025472791938533

theorem tailTrace_1004522 : CollatzResearch.WordTrace tailWord_1004522 prefixEnd_1004522 25471734025472791938533 := by
  unfold tailWord_1004522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9159481816698956886055955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24425284844530551696149213 9159481816698956886055955)
  ·
    refine ⟨13739222725048435329083933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9159481816698956886055955 13739222725048435329083933)
    ·
      refine ⟨5152208521893163248406475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13739222725048435329083933 5152208521893163248406475)
      ·
        refine ⟨7728312782839744872609713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152208521893163248406475 7728312782839744872609713)
        ·
          refine ⟨5796234587129808654457285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7728312782839744872609713 5796234587129808654457285)
          ·
            refine ⟨1086793985086839122710741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5796234587129808654457285 1086793985086839122710741)
            ·
              refine ⟨25471734025472791938533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1086793985086839122710741 25471734025472791938533)
              ·
                rfl

theorem cell21_1004522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 7].length) (baseStart_1004522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004522 prefixEnd_1004522 := by exact prefixLift 1004522
  have htrace : WordTrace (prefixWord ++ tailWord_1004522) baseStart_1004522 baseEnd_1004522 := by
    simpa [prefixWord, tailWord_1004522, baseEnd_1004522] using wordTrace_append hprefix tailTrace_1004522
  have hstable : (prefixWord ++ tailWord_1004522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004522).length < 2 ^ (prefixWord ++ tailWord_1004522).sum := by decide
  have hdescent : baseEnd_1004522 < baseStart_1004522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004680 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_1004680 : Nat := 118140960795 + 1004680 * 2 ^ 59
def prefixEnd_1004680 : Nat := 4983230072969 + 3 ^ 40 * 1004680 * 2
def baseEnd_1004680 : Nat := 229281663981881963813141

theorem tailTrace_1004680 : CollatzResearch.WordTrace tailWord_1004680 prefixEnd_1004680 229281663981881963813141 := by
  unfold tailWord_1004680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321845000111710264237747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24429126666815613685650329 18321845000111710264237747)
  ·
    refine ⟨27482767500167565396356621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18321845000111710264237747 27482767500167565396356621)
    ·
      refine ⟨10306037812562837023633733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27482767500167565396356621 10306037812562837023633733)
      ·
        refine ⟨1932382089855531941931325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10306037812562837023633733 1932382089855531941931325)
        ·
          refine ⟨724643283695824478224247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1932382089855531941931325 724643283695824478224247)
          ·
            refine ⟨1086964925543736717336371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724643283695824478224247 1086964925543736717336371)
            ·
              refine ⟨1630447388315605076004557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086964925543736717336371 1630447388315605076004557)
              ·
                refine ⟨611417770618351903501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1630447388315605076004557 611417770618351903501709)
                ·
                  refine ⟨229281663981881963813141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611417770618351903501709 229281663981881963813141)
                  ·
                    rfl

theorem cell21_1004680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_1004680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004680 prefixEnd_1004680 := by exact prefixLift 1004680
  have htrace : WordTrace (prefixWord ++ tailWord_1004680) baseStart_1004680 baseEnd_1004680 := by
    simpa [prefixWord, tailWord_1004680, baseEnd_1004680] using wordTrace_append hprefix tailTrace_1004680
  have hstable : (prefixWord ++ tailWord_1004680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004680).length < 2 ^ (prefixWord ++ tailWord_1004680).sum := by decide
  have hdescent : baseEnd_1004680 < baseStart_1004680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004733 : List Nat := [1, 4, 1, 2, 1, 1, 4, 7]
def baseStart_1004733 : Nat := 118140960795 + 1004733 * 2 ^ 59
def prefixEnd_1004733 : Nat := 4983230072969 + 3 ^ 40 * 1004733 * 2
def baseEnd_1004733 : Nat := 76431253101321883143233

theorem tailTrace_1004733 : CollatzResearch.WordTrace tailWord_1004733 prefixEnd_1004733 76431253101321883143233 := by
  unfold tailWord_1004733
  simp only [CollatzResearch.WordTrace]
  refine ⟨36645623069031410580154853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24430415379354273720103235 36645623069031410580154853)
  ·
    refine ⟨6871054325443389483779035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36645623069031410580154853 6871054325443389483779035)
    ·
      refine ⟨10306581488165084225668553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871054325443389483779035 10306581488165084225668553)
      ·
        refine ⟨7729936116123813169251415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10306581488165084225668553 7729936116123813169251415)
        ·
          refine ⟨11594904174185719753877123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729936116123813169251415 11594904174185719753877123)
          ·
            refine ⟨17392356261278579630815685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594904174185719753877123 17392356261278579630815685)
            ·
              refine ⟨3261066798989733680777941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17392356261278579630815685 3261066798989733680777941)
              ·
                refine ⟨76431253101321883143233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3261066798989733680777941 76431253101321883143233)
                ·
                  rfl

theorem cell21_1004733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_1004733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004733 prefixEnd_1004733 := by exact prefixLift 1004733
  have htrace : WordTrace (prefixWord ++ tailWord_1004733) baseStart_1004733 baseEnd_1004733 := by
    simpa [prefixWord, tailWord_1004733, baseEnd_1004733] using wordTrace_append hprefix tailTrace_1004733
  have hstable : (prefixWord ++ tailWord_1004733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004733).length < 2 ^ (prefixWord ++ tailWord_1004733).sum := by decide
  have hdescent : baseEnd_1004733 < baseStart_1004733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004747 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_1004747 : Nat := 118140960795 + 1004747 * 2 ^ 59
def prefixEnd_1004747 : Nat := 4983230072969 + 3 ^ 40 * 1004747 * 2
def baseEnd_1004747 : Nat := 229296954294704736196337

theorem tailTrace_1004747 : CollatzResearch.WordTrace tailWord_1004747 prefixEnd_1004747 229296954294704736196337 := by
  unfold tailWord_1004747
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646133690980690971164495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24430755793987127314109663 36646133690980690971164495)
  ·
    refine ⟨54969200536471036456746743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646133690980690971164495 54969200536471036456746743)
    ·
      refine ⟨82453800804706554685120115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54969200536471036456746743 82453800804706554685120115)
      ·
        refine ⟨123680701207059832027680173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82453800804706554685120115 123680701207059832027680173)
        ·
          refine ⟨46380262952647437010380065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123680701207059832027680173 46380262952647437010380065)
          ·
            refine ⟨34785197214485577757785049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46380262952647437010380065 34785197214485577757785049)
            ·
              refine ⟨26088897910864183318338787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34785197214485577757785049 26088897910864183318338787)
              ·
                refine ⟨39133346866296274977508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26088897910864183318338787 39133346866296274977508181)
                ·
                  refine ⟨229296954294704736196337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39133346866296274977508181 229296954294704736196337)
                  ·
                    rfl

theorem cell21_1004747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_1004747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004747 prefixEnd_1004747 := by exact prefixLift 1004747
  have htrace : WordTrace (prefixWord ++ tailWord_1004747) baseStart_1004747 baseEnd_1004747 := by
    simpa [prefixWord, tailWord_1004747, baseEnd_1004747] using wordTrace_append hprefix tailTrace_1004747
  have hstable : (prefixWord ++ tailWord_1004747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004747).length < 2 ^ (prefixWord ++ tailWord_1004747).sum := by decide
  have hdescent : baseEnd_1004747 < baseStart_1004747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004750 : List Nat := [4, 1, 1, 1, 6, 8]
def baseStart_1004750 : Nat := 118140960795 + 1004750 * 2 ^ 59
def prefixEnd_1004750 : Nat := 4983230072969 + 3 ^ 40 * 1004750 * 2
def baseEnd_1004750 : Nat := 8492505145762125838753

theorem tailTrace_1004750 : CollatzResearch.WordTrace tailWord_1004750 prefixEnd_1004750 8492505145762125838753 := by
  unfold tailWord_1004750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580780388746227810440463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24430828739979881655682469 4580780388746227810440463)
  ·
    refine ⟨6871170583119341715660695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580780388746227810440463 6871170583119341715660695)
    ·
      refine ⟨10306755874679012573491043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871170583119341715660695 10306755874679012573491043)
      ·
        refine ⟨15460133812018518860236565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306755874679012573491043 15460133812018518860236565)
        ·
          refine ⟨724693772438368071573589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15460133812018518860236565 724693772438368071573589)
          ·
            refine ⟨8492505145762125838753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 724693772438368071573589 8492505145762125838753)
            ·
              rfl

theorem cell21_1004750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 8].length) (baseStart_1004750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004750 prefixEnd_1004750 := by exact prefixLift 1004750
  have htrace : WordTrace (prefixWord ++ tailWord_1004750) baseStart_1004750 baseEnd_1004750 := by
    simpa [prefixWord, tailWord_1004750, baseEnd_1004750] using wordTrace_append hprefix tailTrace_1004750
  have hstable : (prefixWord ++ tailWord_1004750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004750).length < 2 ^ (prefixWord ++ tailWord_1004750).sum := by decide
  have hdescent : baseEnd_1004750 < baseStart_1004750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004781 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1004781 : Nat := 118140960795 + 1004781 * 2 ^ 59
def prefixEnd_1004781 : Nat := 4983230072969 + 3 ^ 40 * 1004781 * 2
def baseEnd_1004781 : Nat := 229304713557928232629601

theorem tailTrace_1004781 : CollatzResearch.WordTrace tailWord_1004781 prefixEnd_1004781 229304713557928232629601 := by
  unfold tailWord_1004781
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647373772857514777902197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431582515238343185268131 36647373772857514777902197)
  ·
    refine ⟨3435691291205392010428331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36647373772857514777902197 3435691291205392010428331)
    ·
      refine ⟨5153536936808088015642497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435691291205392010428331 5153536936808088015642497)
      ·
        refine ⟨3865152702606066011731873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5153536936808088015642497 3865152702606066011731873)
        ·
          refine ⟨2898864526954549508798905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3865152702606066011731873 2898864526954549508798905)
          ·
            refine ⟨2174148395215912131599179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898864526954549508798905 2174148395215912131599179)
            ·
              refine ⟨3261222592823868197398769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174148395215912131599179 3261222592823868197398769)
              ·
                refine ⟨2445916944617901148049077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261222592823868197398769 2445916944617901148049077)
                ·
                  refine ⟨229304713557928232629601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2445916944617901148049077 229304713557928232629601)
                  ·
                    rfl

theorem cell21_1004781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1004781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004781 prefixEnd_1004781 := by exact prefixLift 1004781
  have htrace : WordTrace (prefixWord ++ tailWord_1004781) baseStart_1004781 baseEnd_1004781 := by
    simpa [prefixWord, tailWord_1004781, baseEnd_1004781] using wordTrace_append hprefix tailTrace_1004781
  have hstable : (prefixWord ++ tailWord_1004781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004781).length < 2 ^ (prefixWord ++ tailWord_1004781).sum := by decide
  have hdescent : baseEnd_1004781 < baseStart_1004781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004798 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1004798 : Nat := 118140960795 + 1004798 * 2 ^ 59
def prefixEnd_1004798 : Nat := 4983230072969 + 3 ^ 40 * 1004798 * 2
def baseEnd_1004798 : Nat := 229308593189539980846233

theorem tailTrace_1004798 : CollatzResearch.WordTrace tailWord_1004798 prefixEnd_1004798 229308593189539980846233 := by
  unfold tailWord_1004798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580999226724490835158881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24431995875863951120847365 4580999226724490835158881)
  ·
    refine ⟨3435749420043368126369161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4580999226724490835158881 3435749420043368126369161)
    ·
      refine ⟨2576812065032526094776871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3435749420043368126369161 2576812065032526094776871)
      ·
        refine ⟨3865218097548789142165307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576812065032526094776871 3865218097548789142165307)
        ·
          refine ⟨5797827146323183713247961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865218097548789142165307 5797827146323183713247961)
          ·
            refine ⟨4348370359742387784935971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797827146323183713247961 4348370359742387784935971)
            ·
              refine ⟨6522555539613581677403957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348370359742387784935971 6522555539613581677403957)
              ·
                refine ⟨611489581838773282256621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6522555539613581677403957 611489581838773282256621)
                ·
                  refine ⟨229308593189539980846233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611489581838773282256621 229308593189539980846233)
                  ·
                    rfl

theorem cell21_1004798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1004798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004798 prefixEnd_1004798 := by exact prefixLift 1004798
  have htrace : WordTrace (prefixWord ++ tailWord_1004798) baseStart_1004798 baseEnd_1004798 := by
    simpa [prefixWord, tailWord_1004798, baseEnd_1004798] using wordTrace_append hprefix tailTrace_1004798
  have hstable : (prefixWord ++ tailWord_1004798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004798).length < 2 ^ (prefixWord ++ tailWord_1004798).sum := by decide
  have hdescent : baseEnd_1004798 < baseStart_1004798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004812 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1004812 : Nat := 118140960795 + 1004812 * 2 ^ 59
def prefixEnd_1004812 : Nat := 4983230072969 + 3 ^ 40 * 1004812 * 2
def baseEnd_1004812 : Nat := 229311788180279067612871

theorem tailTrace_1004812 : CollatzResearch.WordTrace tailWord_1004812 prefixEnd_1004812 229311788180279067612871 := by
  unfold tailWord_1004812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18324252217872603536140345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24432336290496804714853793 18324252217872603536140345)
  ·
    refine ⟨13743189163404452652105259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18324252217872603536140345 13743189163404452652105259)
    ·
      refine ⟨20614783745106678978157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13743189163404452652105259 20614783745106678978157889)
      ·
        refine ⟨15461087808830009233618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20614783745106678978157889 15461087808830009233618417)
        ·
          refine ⟨11595815856622506925213813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15461087808830009233618417 11595815856622506925213813)
          ·
            refine ⟨1087107736558360024238795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11595815856622506925213813 1087107736558360024238795)
            ·
              refine ⟨1630661604837540036358193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087107736558360024238795 1630661604837540036358193)
              ·
                refine ⟨1222996203628155027268645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630661604837540036358193 1222996203628155027268645)
                ·
                  refine ⟨229311788180279067612871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222996203628155027268645 229311788180279067612871)
                  ·
                    rfl

theorem cell21_1004812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1004812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004812 prefixEnd_1004812 := by exact prefixLift 1004812
  have htrace : WordTrace (prefixWord ++ tailWord_1004812) baseStart_1004812 baseEnd_1004812 := by
    simpa [prefixWord, tailWord_1004812, baseEnd_1004812] using wordTrace_append hprefix tailTrace_1004812
  have hstable : (prefixWord ++ tailWord_1004812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004812).length < 2 ^ (prefixWord ++ tailWord_1004812).sum := by decide
  have hdescent : baseEnd_1004812 < baseStart_1004812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004829 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1004829 : Nat := 118140960795 + 1004829 * 2 ^ 59
def prefixEnd_1004829 : Nat := 4983230072969 + 3 ^ 40 * 1004829 * 2
def baseEnd_1004829 : Nat := 229315667811890815829503

theorem tailTrace_1004829 : CollatzResearch.WordTrace tailWord_1004829 prefixEnd_1004829 229315667811890815829503 := by
  unfold tailWord_1004829
  simp only [CollatzResearch.WordTrace]
  refine ⟨36649124476683618975649541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24432749651122412650433027 36649124476683618975649541)
  ·
    refine ⟨6871710839378178557934289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36649124476683618975649541 6871710839378178557934289)
    ·
      refine ⟨5153783129533633918450717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6871710839378178557934289 5153783129533633918450717)
      ·
        refine ⟨1932668673575112719419019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5153783129533633918450717 1932668673575112719419019)
        ·
          refine ⟨2899003010362669079128529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932668673575112719419019 2899003010362669079128529)
          ·
            refine ⟨2174252257772001809346397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899003010362669079128529 2174252257772001809346397)
            ·
              refine ⟨815344596664500678504899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174252257772001809346397 815344596664500678504899)
              ·
                refine ⟨1223016894996751017757349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815344596664500678504899 1223016894996751017757349)
                ·
                  refine ⟨229315667811890815829503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223016894996751017757349 229315667811890815829503)
                  ·
                    rfl

theorem cell21_1004829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1004829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004829 prefixEnd_1004829 := by exact prefixLift 1004829
  have htrace : WordTrace (prefixWord ++ tailWord_1004829) baseStart_1004829 baseEnd_1004829 := by
    simpa [prefixWord, tailWord_1004829, baseEnd_1004829] using wordTrace_append hprefix tailTrace_1004829
  have hstable : (prefixWord ++ tailWord_1004829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004829).length < 2 ^ (prefixWord ++ tailWord_1004829).sum := by decide
  have hdescent : baseEnd_1004829 < baseStart_1004829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004885 : List Nat := [1, 3, 2, 2, 3, 1, 1, 8]
def baseStart_1004885 : Nat := 118140960795 + 1004885 * 2 ^ 59
def prefixEnd_1004885 : Nat := 4983230072969 + 3 ^ 40 * 1004885 * 2
def baseEnd_1004885 : Nat := 76442815924949054298685

theorem tailTrace_1004885 : CollatzResearch.WordTrace tailWord_1004885 prefixEnd_1004885 76442815924949054298685 := by
  unfold tailWord_1004885
  simp only [CollatzResearch.WordTrace]
  refine ⟨36651166964480740539688109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24434111309653827026458739 36651166964480740539688109)
  ·
    refine ⟨13744187611680277702383041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36651166964480740539688109 13744187611680277702383041)
    ·
      refine ⟨10308140708760208276787281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13744187611680277702383041 10308140708760208276787281)
      ·
        refine ⟨7731105531570156207590461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308140708760208276787281 7731105531570156207590461)
        ·
          refine ⟨2899164574338808577846423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7731105531570156207590461 2899164574338808577846423)
          ·
            refine ⟨4348746861508212866769635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899164574338808577846423 4348746861508212866769635)
            ·
              refine ⟨6523120292262319300154453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348746861508212866769635 6523120292262319300154453)
              ·
                refine ⟨76442815924949054298685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6523120292262319300154453 76442815924949054298685)
                ·
                  rfl

theorem cell21_1004885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_1004885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1004885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1004885 prefixEnd_1004885 := by exact prefixLift 1004885
  have htrace : WordTrace (prefixWord ++ tailWord_1004885) baseStart_1004885 baseEnd_1004885 := by
    simpa [prefixWord, tailWord_1004885, baseEnd_1004885] using wordTrace_append hprefix tailTrace_1004885
  have hstable : (prefixWord ++ tailWord_1004885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004885).length < 2 ^ (prefixWord ++ tailWord_1004885).sum := by decide
  have hdescent : baseEnd_1004885 < baseStart_1004885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005012 : List Nat := [2, 4, 1, 2, 4, 1, 2, 5]
def baseStart_1005012 : Nat := 118140960795 + 1005012 * 2 ^ 59
def prefixEnd_1005012 : Nat := 4983230072969 + 3 ^ 40 * 1005012 * 2
def baseEnd_1005012 : Nat := 76452476968374388093043

theorem tailTrace_1005012 : CollatzResearch.WordTrace tailWord_1005012 prefixEnd_1005012 76452476968374388093043 := by
  unfold tailWord_1005012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327899517510320614780645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24437199356680427486374193 18327899517510320614780645)
  ·
    refine ⟨3436481159533185115271371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18327899517510320614780645 3436481159533185115271371)
    ·
      refine ⟨5154721739299777672907057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3436481159533185115271371 5154721739299777672907057)
      ·
        refine ⟨3866041304474833254680293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5154721739299777672907057 3866041304474833254680293)
        ·
          refine ⟨724882744589031235252555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3866041304474833254680293 724882744589031235252555)
          ·
            refine ⟨1087324116883546852878833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724882744589031235252555 1087324116883546852878833)
            ·
              refine ⟨815493087662660139659125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087324116883546852878833 815493087662660139659125)
              ·
                refine ⟨76452476968374388093043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 815493087662660139659125 76452476968374388093043)
                ·
                  rfl

theorem cell21_1005012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_1005012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005012 prefixEnd_1005012 := by exact prefixLift 1005012
  have htrace : WordTrace (prefixWord ++ tailWord_1005012) baseStart_1005012 baseEnd_1005012 := by
    simpa [prefixWord, tailWord_1005012, baseEnd_1005012] using wordTrace_append hprefix tailTrace_1005012
  have hstable : (prefixWord ++ tailWord_1005012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005012).length < 2 ^ (prefixWord ++ tailWord_1005012).sum := by decide
  have hdescent : baseEnd_1005012 < baseStart_1005012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005057 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 4]
def baseStart_1005057 : Nat := 118140960795 + 1005057 * 2 ^ 59
def prefixEnd_1005057 : Nat := 4983230072969 + 3 ^ 40 * 1005057 * 2
def baseEnd_1005057 : Nat := 229367700518213086029037

theorem tailTrace_1005057 : CollatzResearch.WordTrace tailWord_1005057 prefixEnd_1005057 229367700518213086029037 := by
  unfold tailWord_1005057
  simp only [CollatzResearch.WordTrace]
  refine ⟨36657440319857613914949425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24438293546571742609966283 36657440319857613914949425)
  ·
    refine ⟨27493080239893210436212069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36657440319857613914949425 27493080239893210436212069)
    ·
      refine ⟨5154952544979976956789763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27493080239893210436212069 5154952544979976956789763)
      ·
        refine ⟨7732428817469965435184645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154952544979976956789763 7732428817469965435184645)
        ·
          refine ⟨1449830403275618519097121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7732428817469965435184645 1449830403275618519097121)
          ·
            refine ⟨1087372802456713889322841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449830403275618519097121 1087372802456713889322841)
            ·
              refine ⟨815529601842535416992131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087372802456713889322841 815529601842535416992131)
              ·
                refine ⟨1223294402763803125488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815529601842535416992131 1223294402763803125488197)
                ·
                  refine ⟨229367700518213086029037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223294402763803125488197 229367700518213086029037)
                  ·
                    rfl

theorem cell21_1005057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_1005057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005057 prefixEnd_1005057 := by exact prefixLift 1005057
  have htrace : WordTrace (prefixWord ++ tailWord_1005057) baseStart_1005057 baseEnd_1005057 := by
    simpa [prefixWord, tailWord_1005057, baseEnd_1005057] using wordTrace_append hprefix tailTrace_1005057
  have hstable : (prefixWord ++ tailWord_1005057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005057).length < 2 ^ (prefixWord ++ tailWord_1005057).sum := by decide
  have hdescent : baseEnd_1005057 < baseStart_1005057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005085 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1005085 : Nat := 118140960795 + 1005085 * 2 ^ 59
def prefixEnd_1005085 : Nat := 4983230072969 + 3 ^ 40 * 1005085 * 2
def baseEnd_1005085 : Nat := 229374090499691259562313

theorem tailTrace_1005085 : CollatzResearch.WordTrace tailWord_1005085 prefixEnd_1005085 229374090499691259562313 := by
  unfold tailWord_1005085
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658461563756174696968709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24438974375837449797979139 36658461563756174696968709)
  ·
    refine ⟨6873461543204282755681633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36658461563756174696968709 6873461543204282755681633)
    ·
      refine ⟨5155096157403212066761225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6873461543204282755681633 5155096157403212066761225)
      ·
        refine ⟨3866322118052409050070919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5155096157403212066761225 3866322118052409050070919)
        ·
          refine ⟨5799483177078613575106379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866322118052409050070919 5799483177078613575106379)
          ·
            refine ⟨8699224765617920362659569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799483177078613575106379 8699224765617920362659569)
            ·
              refine ⟨6524418574213440271994677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8699224765617920362659569 6524418574213440271994677)
              ·
                refine ⟨611664241332510025499501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6524418574213440271994677 611664241332510025499501)
                ·
                  refine ⟨229374090499691259562313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611664241332510025499501 229374090499691259562313)
                  ·
                    rfl

theorem cell21_1005085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1005085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005085 prefixEnd_1005085 := by exact prefixLift 1005085
  have htrace : WordTrace (prefixWord ++ tailWord_1005085) baseStart_1005085 baseEnd_1005085 := by
    simpa [prefixWord, tailWord_1005085, baseEnd_1005085] using wordTrace_append hprefix tailTrace_1005085
  have hstable : (prefixWord ++ tailWord_1005085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005085).length < 2 ^ (prefixWord ++ tailWord_1005085).sum := by decide
  have hdescent : baseEnd_1005085 < baseStart_1005085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005102 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1005102 : Nat := 118140960795 + 1005102 * 2 ^ 59
def prefixEnd_1005102 : Nat := 4983230072969 + 3 ^ 40 * 1005102 * 2
def baseEnd_1005102 : Nat := 229377970131303007778945

theorem tailTrace_1005102 : CollatzResearch.WordTrace tailWord_1005102 prefixEnd_1005102 229377970131303007778945 := by
  unfold tailWord_1005102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582385200586823325042195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24439387736463057733558373 4582385200586823325042195)
  ·
    refine ⟨6873577800880234987563293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582385200586823325042195 6873577800880234987563293)
    ·
      refine ⟨2577591675330088120336235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6873577800880234987563293 2577591675330088120336235)
      ·
        refine ⟨3866387512995132180504353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577591675330088120336235 3866387512995132180504353)
        ·
          refine ⟨2899790634746349135378265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866387512995132180504353 2899790634746349135378265)
          ·
            refine ⟨2174842976059761851533699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899790634746349135378265 2174842976059761851533699)
            ·
              refine ⟨3262264464089642777300549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174842976059761851533699 3262264464089642777300549)
              ·
                refine ⟨611674587016808020743853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3262264464089642777300549 611674587016808020743853)
                ·
                  refine ⟨229377970131303007778945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611674587016808020743853 229377970131303007778945)
                  ·
                    rfl

theorem cell21_1005102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1005102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005102 prefixEnd_1005102 := by exact prefixLift 1005102
  have htrace : WordTrace (prefixWord ++ tailWord_1005102) baseStart_1005102 baseEnd_1005102 := by
    simpa [prefixWord, tailWord_1005102, baseEnd_1005102] using wordTrace_append hprefix tailTrace_1005102
  have hstable : (prefixWord ++ tailWord_1005102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005102).length < 2 ^ (prefixWord ++ tailWord_1005102).sum := by decide
  have hdescent : baseEnd_1005102 < baseStart_1005102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005113 : List Nat := [1, 2, 1, 5, 1, 2, 3, 6]
def baseStart_1005113 : Nat := 118140960795 + 1005113 * 2 ^ 59
def prefixEnd_1005113 : Nat := 4983230072969 + 3 ^ 40 * 1005113 * 2
def baseEnd_1005113 : Nat := 76460160160389811031863

theorem tailTrace_1005113 : CollatzResearch.WordTrace tailWord_1005113 prefixEnd_1005113 76460160160389811031863 := by
  unfold tailWord_1005113
  simp only [CollatzResearch.WordTrace]
  refine ⟨36659482807654735478987993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24439655205103156985991995 36659482807654735478987993)
  ·
    refine ⟨27494612105741051609240995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36659482807654735478987993 27494612105741051609240995)
    ·
      refine ⟨41241918158611577413861493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27494612105741051609240995 41241918158611577413861493)
      ·
        refine ⟨3866429827369835382549515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41241918158611577413861493 3866429827369835382549515)
        ·
          refine ⟨5799644741054753073824273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866429827369835382549515 5799644741054753073824273)
          ·
            refine ⟨4349733555791064805368205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799644741054753073824273 4349733555791064805368205)
            ·
              refine ⟨1631150083421649302013077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4349733555791064805368205 1631150083421649302013077)
              ·
                refine ⟨76460160160389811031863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1631150083421649302013077 76460160160389811031863)
                ·
                  rfl

theorem cell21_1005113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_1005113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005113 prefixEnd_1005113 := by exact prefixLift 1005113
  have htrace : WordTrace (prefixWord ++ tailWord_1005113) baseStart_1005113 baseEnd_1005113 := by
    simpa [prefixWord, tailWord_1005113, baseEnd_1005113] using wordTrace_append hprefix tailTrace_1005113
  have hstable : (prefixWord ++ tailWord_1005113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005113).length < 2 ^ (prefixWord ++ tailWord_1005113).sum := by decide
  have hdescent : baseEnd_1005113 < baseStart_1005113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005220 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1005220 : Nat := 118140960795 + 1005220 * 2 ^ 59
def prefixEnd_1005220 : Nat := 4983230072969 + 3 ^ 40 * 1005220 * 2
def baseEnd_1005220 : Nat := 229404899338961024812037

theorem tailTrace_1005220 : CollatzResearch.WordTrace tailWord_1005220 prefixEnd_1005220 229404899338961024812037 := by
  unfold tailWord_1005220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331692709133546376566557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24442256945511395168755409 18331692709133546376566557)
  ·
    refine ⟨6874384765925079891212459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18331692709133546376566557 6874384765925079891212459)
    ·
      refine ⟨10311577148887619836818689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874384765925079891212459 10311577148887619836818689)
      ·
        refine ⟨7733682861665714877614017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10311577148887619836818689 7733682861665714877614017)
        ·
          refine ⟨5800262146249286158210513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733682861665714877614017 5800262146249286158210513)
          ·
            refine ⟨4350196609686964618657885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800262146249286158210513 4350196609686964618657885)
            ·
              refine ⟨1631323728632611731996707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350196609686964618657885 1631323728632611731996707)
              ·
                refine ⟨2446985592948917597995061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631323728632611731996707 2446985592948917597995061)
                ·
                  refine ⟨229404899338961024812037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446985592948917597995061 229404899338961024812037)
                  ·
                    rfl

theorem cell21_1005220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1005220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005220 prefixEnd_1005220 := by exact prefixLift 1005220
  have htrace : WordTrace (prefixWord ++ tailWord_1005220) baseStart_1005220 baseEnd_1005220 := by
    simpa [prefixWord, tailWord_1005220, baseEnd_1005220] using wordTrace_append hprefix tailTrace_1005220
  have hstable : (prefixWord ++ tailWord_1005220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005220).length < 2 ^ (prefixWord ++ tailWord_1005220).sum := by decide
  have hdescent : baseEnd_1005220 < baseStart_1005220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005248 : List Nat := [2, 1, 1, 2, 4, 1, 1, 9]
def baseStart_1005248 : Nat := 118140960795 + 1005248 * 2 ^ 59
def prefixEnd_1005248 : Nat := 4983230072969 + 3 ^ 40 * 1005248 * 2
def baseEnd_1005248 : Nat := 76470429773479732781771

theorem tailTrace_1005248 : CollatzResearch.WordTrace tailWord_1005248 prefixEnd_1005248 76470429773479732781771 := by
  unfold tailWord_1005248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332203331082826767576199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24442937774777102356768265 18332203331082826767576199)
  ·
    refine ⟨27498304996624240151364299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18332203331082826767576199 27498304996624240151364299)
    ·
      refine ⟨41247457494936360227046449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498304996624240151364299 41247457494936360227046449)
      ·
        refine ⟨30935593121202270170284837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41247457494936360227046449 30935593121202270170284837)
        ·
          refine ⟨5800423710225425656928407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30935593121202270170284837 5800423710225425656928407)
          ·
            refine ⟨8700635565338138485392611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800423710225425656928407 8700635565338138485392611)
            ·
              refine ⟨13050953348007207728088917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700635565338138485392611 13050953348007207728088917)
              ·
                refine ⟨76470429773479732781771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13050953348007207728088917 76470429773479732781771)
                ·
                  rfl

theorem cell21_1005248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_1005248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005248 prefixEnd_1005248 := by exact prefixLift 1005248
  have htrace : WordTrace (prefixWord ++ tailWord_1005248) baseStart_1005248 baseEnd_1005248 := by
    simpa [prefixWord, tailWord_1005248, baseEnd_1005248] using wordTrace_append hprefix tailTrace_1005248
  have hstable : (prefixWord ++ tailWord_1005248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005248).length < 2 ^ (prefixWord ++ tailWord_1005248).sum := by decide
  have hdescent : baseEnd_1005248 < baseStart_1005248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005268 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1005268 : Nat := 118140960795 + 1005268 * 2 ^ 59
def prefixEnd_1005268 : Nat := 4983230072969 + 3 ^ 40 * 1005268 * 2
def baseEnd_1005268 : Nat := 229415853592923608011939

theorem tailTrace_1005268 : CollatzResearch.WordTrace tailWord_1005268 prefixEnd_1005268 229415853592923608011939 := by
  unfold tailWord_1005268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332568061046598475440229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24443424081395464633920305 18332568061046598475440229)
  ·
    refine ⟨3437356511446237214145043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18332568061046598475440229 3437356511446237214145043)
    ·
      refine ⟨5156034767169355821217565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437356511446237214145043 5156034767169355821217565)
      ·
        refine ⟨1933513037688508432956587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5156034767169355821217565 1933513037688508432956587)
        ·
          refine ⟨2900269556532762649434881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933513037688508432956587 2900269556532762649434881)
          ·
            refine ⟨2175202167399571987076161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2900269556532762649434881 2175202167399571987076161)
            ·
              refine ⟨1631401625549678990307121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175202167399571987076161 1631401625549678990307121)
              ·
                refine ⟨1223551219162259242730341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631401625549678990307121 1223551219162259242730341)
                ·
                  refine ⟨229415853592923608011939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223551219162259242730341 229415853592923608011939)
                  ·
                    rfl

theorem cell21_1005268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1005268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005268 prefixEnd_1005268 := by exact prefixLift 1005268
  have htrace : WordTrace (prefixWord ++ tailWord_1005268) baseStart_1005268 baseEnd_1005268 := by
    simpa [prefixWord, tailWord_1005268, baseEnd_1005268] using wordTrace_append hprefix tailTrace_1005268
  have hstable : (prefixWord ++ tailWord_1005268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005268).length < 2 ^ (prefixWord ++ tailWord_1005268).sum := by decide
  have hdescent : baseEnd_1005268 < baseStart_1005268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005279 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_1005279 : Nat := 118140960795 + 1005279 * 2 ^ 59
def prefixEnd_1005279 : Nat := 4983230072969 + 3 ^ 40 * 1005279 * 2
def baseEnd_1005279 : Nat := 229418363942790033328583

theorem tailTrace_1005279 : CollatzResearch.WordTrace tailWord_1005279 prefixEnd_1005279 229418363942790033328583 := by
  unfold tailWord_1005279
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665537325053345829530891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24443691550035563886353927 36665537325053345829530891)
  ·
    refine ⟨54998305987580018744296337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36665537325053345829530891 54998305987580018744296337)
    ·
      refine ⟨41248729490685014058222253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54998305987580018744296337 41248729490685014058222253)
      ·
        refine ⟨15468273559006880271833345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41248729490685014058222253 15468273559006880271833345)
        ·
          refine ⟨11601205169255160203875009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15468273559006880271833345 11601205169255160203875009)
          ·
            refine ⟨8700903876941370152906257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11601205169255160203875009 8700903876941370152906257)
            ·
              refine ⟨6525677907706027614679693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700903876941370152906257 6525677907706027614679693)
              ·
                refine ⟨2447129215389760355504885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525677907706027614679693 2447129215389760355504885)
                ·
                  refine ⟨229418363942790033328583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447129215389760355504885 229418363942790033328583)
                  ·
                    rfl

theorem cell21_1005279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_1005279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005279 prefixEnd_1005279 := by exact prefixLift 1005279
  have htrace : WordTrace (prefixWord ++ tailWord_1005279) baseStart_1005279 baseEnd_1005279 := by
    simpa [prefixWord, tailWord_1005279, baseEnd_1005279] using wordTrace_append hprefix tailTrace_1005279
  have hstable : (prefixWord ++ tailWord_1005279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005279).length < 2 ^ (prefixWord ++ tailWord_1005279).sum := by decide
  have hdescent : baseEnd_1005279 < baseStart_1005279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005330 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1005330 : Nat := 118140960795 + 1005330 * 2 ^ 59
def prefixEnd_1005330 : Nat := 4983230072969 + 3 ^ 40 * 1005330 * 2
def baseEnd_1005330 : Nat := 229430002837625277978479

theorem tailTrace_1005330 : CollatzResearch.WordTrace tailWord_1005330 prefixEnd_1005330 229430002837625277978479 := by
  unfold tailWord_1005330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166849361967145384909361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24444931631912387693091629 9166849361967145384909361)
  ·
    refine ⟨6875137021475359038682021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9166849361967145384909361 6875137021475359038682021)
    ·
      refine ⟨1289088191526629819752879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6875137021475359038682021 1289088191526629819752879)
      ·
        refine ⟨1933632287289944729629319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289088191526629819752879 1933632287289944729629319)
        ·
          refine ⟨2900448430934917094443979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933632287289944729629319 2900448430934917094443979)
          ·
            refine ⟨4350672646402375641665969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900448430934917094443979 4350672646402375641665969)
            ·
              refine ⟨3263004484801781731249477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350672646402375641665969 3263004484801781731249477)
              ·
                refine ⟨611813340900334074609277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3263004484801781731249477 611813340900334074609277)
                ·
                  refine ⟨229430002837625277978479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611813340900334074609277 229430002837625277978479)
                  ·
                    rfl

theorem cell21_1005330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1005330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005330 prefixEnd_1005330 := by exact prefixLift 1005330
  have htrace : WordTrace (prefixWord ++ tailWord_1005330) baseStart_1005330 baseEnd_1005330 := by
    simpa [prefixWord, tailWord_1005330, baseEnd_1005330] using wordTrace_append hprefix tailTrace_1005330
  have hstable : (prefixWord ++ tailWord_1005330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005330).length < 2 ^ (prefixWord ++ tailWord_1005330).sum := by decide
  have hdescent : baseEnd_1005330 < baseStart_1005330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005358 : List Nat := [4, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1005358 : Nat := 118140960795 + 1005358 * 2 ^ 59
def prefixEnd_1005358 : Nat := 4983230072969 + 3 ^ 40 * 1005358 * 2
def baseEnd_1005358 : Nat := 76478797606367817170585

theorem tailTrace_1005358 : CollatzResearch.WordTrace tailWord_1005358 prefixEnd_1005358 76478797606367817170585 := by
  unfold tailWord_1005358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583552336470892790207091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24445612461178094881104485 4583552336470892790207091)
  ·
    refine ⟨6875328504706339185310637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583552336470892790207091 6875328504706339185310637)
    ·
      refine ⟨2578248189264877194491489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6875328504706339185310637 2578248189264877194491489)
      ·
        refine ⟨1933686141948657895868617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578248189264877194491489 1933686141948657895868617)
        ·
          refine ⟨1450264606461493421901463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1933686141948657895868617 1450264606461493421901463)
          ·
            refine ⟨2175396909692240132852195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450264606461493421901463 2175396909692240132852195)
            ·
              refine ⟨3263095364538360199278293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175396909692240132852195 3263095364538360199278293)
              ·
                refine ⟨76478797606367817170585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3263095364538360199278293 76478797606367817170585)
                ·
                  rfl

theorem cell21_1005358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1005358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005358 prefixEnd_1005358 := by exact prefixLift 1005358
  have htrace : WordTrace (prefixWord ++ tailWord_1005358) baseStart_1005358 baseEnd_1005358 := by
    simpa [prefixWord, tailWord_1005358, baseEnd_1005358] using wordTrace_append hprefix tailTrace_1005358
  have hstable : (prefixWord ++ tailWord_1005358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005358).length < 2 ^ (prefixWord ++ tailWord_1005358).sum := by decide
  have hdescent : baseEnd_1005358 < baseStart_1005358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005386 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_1005386 : Nat := 118140960795 + 1005386 * 2 ^ 59
def prefixEnd_1005386 : Nat := 4983230072969 + 3 ^ 40 * 1005386 * 2
def baseEnd_1005386 : Nat := 229442782800581625045031

theorem tailTrace_1005386 : CollatzResearch.WordTrace tailWord_1005386 prefixEnd_1005386 229442782800581625045031 := by
  unfold tailWord_1005386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167359983916425775919003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24446293290443802069117341 9167359983916425775919003)
  ·
    refine ⟨13751039975874638663878505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9167359983916425775919003 13751039975874638663878505)
    ·
      refine ⟨10313279981905978997908879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13751039975874638663878505 10313279981905978997908879)
      ·
        refine ⟨15469919972858968496863319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313279981905978997908879 15469919972858968496863319)
        ·
          refine ⟨23204879959288452745294979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469919972858968496863319 23204879959288452745294979)
          ·
            refine ⟨34807319938932679117942469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23204879959288452745294979 34807319938932679117942469)
            ·
              refine ⟨6526372488549877334614213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34807319938932679117942469 6526372488549877334614213)
              ·
                refine ⟨1223694841603102000240165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6526372488549877334614213 1223694841603102000240165)
                ·
                  refine ⟨229442782800581625045031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223694841603102000240165 229442782800581625045031)
                  ·
                    rfl

theorem cell21_1005386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_1005386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005386 prefixEnd_1005386 := by exact prefixLift 1005386
  have htrace : WordTrace (prefixWord ++ tailWord_1005386) baseStart_1005386 baseEnd_1005386 := by
    simpa [prefixWord, tailWord_1005386, baseEnd_1005386] using wordTrace_append hprefix tailTrace_1005386
  have hstable : (prefixWord ++ tailWord_1005386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005386).length < 2 ^ (prefixWord ++ tailWord_1005386).sum := by decide
  have hdescent : baseEnd_1005386 < baseStart_1005386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005389 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1005389 : Nat := 118140960795 + 1005389 * 2 ^ 59
def prefixEnd_1005389 : Nat := 4983230072969 + 3 ^ 40 * 1005389 * 2
def baseEnd_1005389 : Nat := 229443467441454286495025

theorem tailTrace_1005389 : CollatzResearch.WordTrace tailWord_1005389 prefixEnd_1005389 229443467441454286495025 := by
  unfold tailWord_1005389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669549354654834616035221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24446366236436556410690147 36669549354654834616035221)
  ·
    refine ⟨1718885125999445372626651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36669549354654834616035221 1718885125999445372626651)
    ·
      refine ⟨2578327688999168058939977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718885125999445372626651 2578327688999168058939977)
      ·
        refine ⟨1933745766749376044204983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578327688999168058939977 1933745766749376044204983)
        ·
          refine ⟨2900618650124064066307475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933745766749376044204983 2900618650124064066307475)
          ·
            refine ⟨4350927975186096099461213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900618650124064066307475 4350927975186096099461213)
            ·
              refine ⟨1631597990694786037297955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350927975186096099461213 1631597990694786037297955)
              ·
                refine ⟨2447396986042179055946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631597990694786037297955 2447396986042179055946933)
                ·
                  refine ⟨229443467441454286495025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447396986042179055946933 229443467441454286495025)
                  ·
                    rfl

theorem cell21_1005389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1005389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005389 prefixEnd_1005389 := by exact prefixLift 1005389
  have htrace : WordTrace (prefixWord ++ tailWord_1005389) baseStart_1005389 baseEnd_1005389 := by
    simpa [prefixWord, tailWord_1005389, baseEnd_1005389] using wordTrace_append hprefix tailTrace_1005389
  have hstable : (prefixWord ++ tailWord_1005389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005389).length < 2 ^ (prefixWord ++ tailWord_1005389).sum := by decide
  have hdescent : baseEnd_1005389 < baseStart_1005389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005558 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1005558 : Nat := 118140960795 + 1005558 * 2 ^ 59
def prefixEnd_1005558 : Nat := 4983230072969 + 3 ^ 40 * 1005558 * 2
def baseEnd_1005558 : Nat := 229482035543947548178013

theorem tailTrace_1005558 : CollatzResearch.WordTrace tailWord_1005558 prefixEnd_1005558 229482035543947548178013 := by
  unfold tailWord_1005558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292232080690161029933583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24450475527361717652624885 2292232080690161029933583)
  ·
    refine ⟨3438348121035241544900375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292232080690161029933583 3438348121035241544900375)
    ·
      refine ⟨5157522181552862317350563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438348121035241544900375 5157522181552862317350563)
      ·
        refine ⟨7736283272329293476025845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157522181552862317350563 7736283272329293476025845)
        ·
          refine ⟨725276556780871263377423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7736283272329293476025845 725276556780871263377423)
          ·
            refine ⟨1087914835171306895066135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725276556780871263377423 1087914835171306895066135)
            ·
              refine ⟨1631872252756960342599203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087914835171306895066135 1631872252756960342599203)
              ·
                refine ⟨2447808379135440513898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631872252756960342599203 2447808379135440513898805)
                ·
                  refine ⟨229482035543947548178013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447808379135440513898805 229482035543947548178013)
                  ·
                    rfl

theorem cell21_1005558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1005558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005558 prefixEnd_1005558 := by exact prefixLift 1005558
  have htrace : WordTrace (prefixWord ++ tailWord_1005558) baseStart_1005558 baseEnd_1005558 := by
    simpa [prefixWord, tailWord_1005558, baseEnd_1005558] using wordTrace_append hprefix tailTrace_1005558
  have hstable : (prefixWord ++ tailWord_1005558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005558).length < 2 ^ (prefixWord ++ tailWord_1005558).sum := by decide
  have hdescent : baseEnd_1005558 < baseStart_1005558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005572 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1005572 : Nat := 118140960795 + 1005572 * 2 ^ 59
def prefixEnd_1005572 : Nat := 4983230072969 + 3 ^ 40 * 1005572 * 2
def baseEnd_1005572 : Nat := 229485230534686634944651

theorem tailTrace_1005572 : CollatzResearch.WordTrace tailWord_1005572 prefixEnd_1005572 229485230534686634944651 := by
  unfold tailWord_1005572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18338111956495928434973485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24450815941994571246631313 18338111956495928434973485)
  ·
    refine ⟨6876791983685973163115057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18338111956495928434973485 6876791983685973163115057)
    ·
      refine ⟨5157593987764479872336293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6876791983685973163115057 5157593987764479872336293)
      ·
        refine ⟨967048872705839976063055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5157593987764479872336293 967048872705839976063055)
        ·
          refine ⟨1450573309058759964094583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967048872705839976063055 1450573309058759964094583)
          ·
            refine ⟨2175859963588139946141875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450573309058759964094583 2175859963588139946141875)
            ·
              refine ⟨3263789945382209919212813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175859963588139946141875 3263789945382209919212813)
              ·
                refine ⟨1223921229518328719704805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263789945382209919212813 1223921229518328719704805)
                ·
                  refine ⟨229485230534686634944651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223921229518328719704805 229485230534686634944651)
                  ·
                    rfl

theorem cell21_1005572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1005572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005572 prefixEnd_1005572 := by exact prefixLift 1005572
  have htrace : WordTrace (prefixWord ++ tailWord_1005572) baseStart_1005572 baseEnd_1005572 := by
    simpa [prefixWord, tailWord_1005572, baseEnd_1005572] using wordTrace_append hprefix tailTrace_1005572
  have hstable : (prefixWord ++ tailWord_1005572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005572).length < 2 ^ (prefixWord ++ tailWord_1005572).sum := by decide
  have hdescent : baseEnd_1005572 < baseStart_1005572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005617 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 3]
def baseStart_1005617 : Nat := 118140960795 + 1005617 * 2 ^ 59
def prefixEnd_1005617 : Nat := 4983230072969 + 3 ^ 40 * 1005617 * 2
def baseEnd_1005617 : Nat := 229495500147776556694559

theorem tailTrace_1005617 : CollatzResearch.WordTrace tailWord_1005617 prefixEnd_1005617 229495500147776556694559 := by
  unfold tailWord_1005617
  simp only [CollatzResearch.WordTrace]
  refine ⟨36677865197828829555335105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24451910131885886370223403 36677865197828829555335105)
  ·
    refine ⟨27508398898371622166501329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36677865197828829555335105 27508398898371622166501329)
    ·
      refine ⟨20631299173778716624875997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27508398898371622166501329 20631299173778716624875997)
      ·
        refine ⟨7736737190167018734328499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20631299173778716624875997 7736737190167018734328499)
        ·
          refine ⟨11605105785250528101492749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736737190167018734328499 11605105785250528101492749)
          ·
            refine ⟨4351914669468948038059781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11605105785250528101492749 4351914669468948038059781)
            ·
              refine ⟨815984000525427757136209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4351914669468948038059781 815984000525427757136209)
              ·
                refine ⟨611988000394070817852157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815984000525427757136209 611988000394070817852157)
                ·
                  refine ⟨229495500147776556694559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611988000394070817852157 229495500147776556694559)
                  ·
                    rfl

theorem cell21_1005617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_1005617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005617 prefixEnd_1005617 := by exact prefixLift 1005617
  have htrace : WordTrace (prefixWord ++ tailWord_1005617) baseStart_1005617 baseEnd_1005617 := by
    simpa [prefixWord, tailWord_1005617, baseEnd_1005617] using wordTrace_append hprefix tailTrace_1005617
  have hstable : (prefixWord ++ tailWord_1005617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005617).length < 2 ^ (prefixWord ++ tailWord_1005617).sum := by decide
  have hdescent : baseEnd_1005617 < baseStart_1005617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005673 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1005673 : Nat := 118140960795 + 1005673 * 2 ^ 59
def prefixEnd_1005673 : Nat := 4983230072969 + 3 ^ 40 * 1005673 * 2
def baseEnd_1005673 : Nat := 229508280110732903761111

theorem tailTrace_1005673 : CollatzResearch.WordTrace tailWord_1005673 prefixEnd_1005673 229508280110732903761111 := by
  unfold tailWord_1005673
  simp only [CollatzResearch.WordTrace]
  refine ⟨36679907685625951119373673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24453271790417300746249115 36679907685625951119373673)
  ·
    refine ⟨27509930764219463339530255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36679907685625951119373673 27509930764219463339530255)
    ·
      refine ⟨41264896146329195009295383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27509930764219463339530255 41264896146329195009295383)
      ·
        refine ⟨61897344219493792513943075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41264896146329195009295383 61897344219493792513943075)
        ·
          refine ⟨92846016329240688770914613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61897344219493792513943075 92846016329240688770914613)
          ·
            refine ⟨8704314030866314572273245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92846016329240688770914613 8704314030866314572273245)
            ·
              refine ⟨3264117761574867964602467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8704314030866314572273245 3264117761574867964602467)
              ·
                refine ⟨4896176642362301946903701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264117761574867964602467 4896176642362301946903701)
                ·
                  refine ⟨229508280110732903761111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4896176642362301946903701 229508280110732903761111)
                  ·
                    rfl

theorem cell21_1005673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1005673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005673 prefixEnd_1005673 := by exact prefixLift 1005673
  have htrace : WordTrace (prefixWord ++ tailWord_1005673) baseStart_1005673 baseEnd_1005673 := by
    simpa [prefixWord, tailWord_1005673, baseEnd_1005673] using wordTrace_append hprefix tailTrace_1005673
  have hstable : (prefixWord ++ tailWord_1005673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005673).length < 2 ^ (prefixWord ++ tailWord_1005673).sum := by decide
  have hdescent : baseEnd_1005673 < baseStart_1005673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005676 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1005676 : Nat := 118140960795 + 1005676 * 2 ^ 59
def prefixEnd_1005676 : Nat := 4983230072969 + 3 ^ 40 * 1005676 * 2
def baseEnd_1005676 : Nat := 229508964751605565211105

theorem tailTrace_1005676 : CollatzResearch.WordTrace tailWord_1005676 prefixEnd_1005676 229508964751605565211105 := by
  unfold tailWord_1005676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18340008552307541315866441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24453344736410055087821921 18340008552307541315866441)
  ·
    refine ⟨13755006414230655986899831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18340008552307541315866441 13755006414230655986899831)
    ·
      refine ⟨20632509621345983980349747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13755006414230655986899831 20632509621345983980349747)
      ·
        refine ⟨30948764432018975970524621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20632509621345983980349747 30948764432018975970524621)
        ·
          refine ⟨11605786662007115988946733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30948764432018975970524621 11605786662007115988946733)
          ·
            refine ⟨4352169998252668495855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11605786662007115988946733 4352169998252668495855025)
            ·
              refine ⟨3264127498689501371891269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352169998252668495855025 3264127498689501371891269)
              ·
                refine ⟨612023906004281507229613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3264127498689501371891269 612023906004281507229613)
                ·
                  refine ⟨229508964751605565211105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612023906004281507229613 229508964751605565211105)
                  ·
                    rfl

theorem cell21_1005676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1005676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005676 prefixEnd_1005676 := by exact prefixLift 1005676
  have htrace : WordTrace (prefixWord ++ tailWord_1005676) baseStart_1005676 baseEnd_1005676 := by
    simpa [prefixWord, tailWord_1005676, baseEnd_1005676] using wordTrace_append hprefix tailTrace_1005676
  have hstable : (prefixWord ++ tailWord_1005676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005676).length < 2 ^ (prefixWord ++ tailWord_1005676).sum := by decide
  have hdescent : baseEnd_1005676 < baseStart_1005676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005710 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_1005710 : Nat := 118140960795 + 1005710 * 2 ^ 59
def prefixEnd_1005710 : Nat := 4983230072969 + 3 ^ 40 * 1005710 * 2
def baseEnd_1005710 : Nat := 229516724014829061644369

theorem tailTrace_1005710 : CollatzResearch.WordTrace tailWord_1005710 prefixEnd_1005710 229516724014829061644369 := by
  unfold tailWord_1005710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585157148311488304808823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24454171457661270958980389 4585157148311488304808823)
  ·
    refine ⟨6877735722467232457213235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4585157148311488304808823 6877735722467232457213235)
    ·
      refine ⟨10316603583700848685819853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877735722467232457213235 10316603583700848685819853)
      ·
        refine ⟨3868726343887818257182445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10316603583700848685819853 3868726343887818257182445)
        ·
          refine ⟨1450772378957931846443417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3868726343887818257182445 1450772378957931846443417)
          ·
            refine ⟨1088079284218448884832563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450772378957931846443417 1088079284218448884832563)
            ·
              refine ⟨1632118926327673327248845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088079284218448884832563 1632118926327673327248845)
              ·
                refine ⟨612044597372877497718317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632118926327673327248845 612044597372877497718317)
                ·
                  refine ⟨229516724014829061644369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612044597372877497718317 229516724014829061644369)
                  ·
                    rfl

theorem cell21_1005710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_1005710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005710 prefixEnd_1005710 := by exact prefixLift 1005710
  have htrace : WordTrace (prefixWord ++ tailWord_1005710) baseStart_1005710 baseEnd_1005710 := by
    simpa [prefixWord, tailWord_1005710, baseEnd_1005710] using wordTrace_append hprefix tailTrace_1005710
  have hstable : (prefixWord ++ tailWord_1005710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005710).length < 2 ^ (prefixWord ++ tailWord_1005710).sum := by decide
  have hdescent : baseEnd_1005710 < baseStart_1005710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005738 : List Nat := [3, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1005738 : Nat := 118140960795 + 1005738 * 2 ^ 59
def prefixEnd_1005738 : Nat := 4983230072969 + 3 ^ 40 * 1005738 * 2
def baseEnd_1005738 : Nat := 76507704665435745059215

theorem tailTrace_1005738 : CollatzResearch.WordTrace tailWord_1005738 prefixEnd_1005738 76507704665435745059215 := by
  unfold tailWord_1005738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170569607597616805122467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24454852286926978146993245 9170569607597616805122467)
  ·
    refine ⟨13755854411396425207683701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9170569607597616805122467 13755854411396425207683701)
    ·
      refine ⟨1289611351068414863220347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13755854411396425207683701 1289611351068414863220347)
      ·
        refine ⟨1934417026602622294830521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289611351068414863220347 1934417026602622294830521)
        ·
          refine ⟨1450812769951966721122891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934417026602622294830521 1450812769951966721122891)
          ·
            refine ⟨2176219154927950081684337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450812769951966721122891 2176219154927950081684337)
            ·
              refine ⟨1632164366195962561263253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176219154927950081684337 1632164366195962561263253)
              ·
                refine ⟨76507704665435745059215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1632164366195962561263253 76507704665435745059215)
                ·
                  rfl

theorem cell21_1005738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1005738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005738 prefixEnd_1005738 := by exact prefixLift 1005738
  have htrace : WordTrace (prefixWord ++ tailWord_1005738) baseStart_1005738 baseEnd_1005738 := by
    simpa [prefixWord, tailWord_1005738, baseEnd_1005738] using wordTrace_append hprefix tailTrace_1005738
  have hstable : (prefixWord ++ tailWord_1005738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005738).length < 2 ^ (prefixWord ++ tailWord_1005738).sum := by decide
  have hdescent : baseEnd_1005738 < baseStart_1005738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005797 : List Nat := [1, 3, 1, 4, 2, 3, 1, 6]
def baseStart_1005797 : Nat := 118140960795 + 1005797 * 2 ^ 59
def prefixEnd_1005797 : Nat := 4983230072969 + 3 ^ 40 * 1005797 * 2
def baseEnd_1005797 : Nat := 76512192866712081231397

theorem tailTrace_1005797 : CollatzResearch.WordTrace tailWord_1005797 prefixEnd_1005797 76512192866712081231397 := by
  unfold tailWord_1005797
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684430337176720296887645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24456286891451146864591763 36684430337176720296887645)
  ·
    refine ⟨13756661376441270111332867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36684430337176720296887645 13756661376441270111332867)
    ·
      refine ⟨20634992064661905166999301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756661376441270111332867 20634992064661905166999301)
      ·
        refine ⟨3869061012124107218812369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20634992064661905166999301 3869061012124107218812369)
        ·
          refine ⟨2901795759093080414109277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869061012124107218812369 2901795759093080414109277)
          ·
            refine ⟨1088173409659905155290979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2901795759093080414109277 1088173409659905155290979)
            ·
              refine ⟨1632260114489857732936469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088173409659905155290979 1632260114489857732936469)
              ·
                refine ⟨76512192866712081231397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1632260114489857732936469 76512192866712081231397)
                ·
                  rfl

theorem cell21_1005797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_1005797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005797 prefixEnd_1005797 := by exact prefixLift 1005797
  have htrace : WordTrace (prefixWord ++ tailWord_1005797) baseStart_1005797 baseEnd_1005797 := by
    simpa [prefixWord, tailWord_1005797, baseEnd_1005797] using wordTrace_append hprefix tailTrace_1005797
  have hstable : (prefixWord ++ tailWord_1005797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005797).length < 2 ^ (prefixWord ++ tailWord_1005797).sum := by decide
  have hdescent : baseEnd_1005797 < baseStart_1005797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005825 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1005825 : Nat := 118140960795 + 1005825 * 2 ^ 59
def prefixEnd_1005825 : Nat := 4983230072969 + 3 ^ 40 * 1005825 * 2
def baseEnd_1005825 : Nat := 229542968581614417227467

theorem tailTrace_1005825 : CollatzResearch.WordTrace tailWord_1005825 prefixEnd_1005825 229542968581614417227467 := by
  unfold tailWord_1005825
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685451581075281078906929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24456967720716854052604619 36685451581075281078906929)
  ·
    refine ⟨27514088685806460809180197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36685451581075281078906929 27514088685806460809180197)
    ·
      refine ⟨5158891628588711401721287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27514088685806460809180197 5158891628588711401721287)
      ·
        refine ⟨7738337442883067102581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158891628588711401721287 7738337442883067102581931)
        ·
          refine ⟨11607506164324600653872897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738337442883067102581931 11607506164324600653872897)
          ·
            refine ⟨8705629623243450490404673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607506164324600653872897 8705629623243450490404673)
            ·
              refine ⟨6529222217432587867803505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705629623243450490404673 6529222217432587867803505)
              ·
                refine ⟨4896916663074440900852629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529222217432587867803505 4896916663074440900852629)
                ·
                  refine ⟨229542968581614417227467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4896916663074440900852629 229542968581614417227467)
                  ·
                    rfl

theorem cell21_1005825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1005825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005825 prefixEnd_1005825 := by exact prefixLift 1005825
  have htrace : WordTrace (prefixWord ++ tailWord_1005825) baseStart_1005825 baseEnd_1005825 := by
    simpa [prefixWord, tailWord_1005825, baseEnd_1005825] using wordTrace_append hprefix tailTrace_1005825
  have hstable : (prefixWord ++ tailWord_1005825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005825).length < 2 ^ (prefixWord ++ tailWord_1005825).sum := by decide
  have hdescent : baseEnd_1005825 < baseStart_1005825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005977 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_1005977 : Nat := 118140960795 + 1005977 * 2 ^ 59
def prefixEnd_1005977 : Nat := 4983230072969 + 3 ^ 40 * 1005977 * 2
def baseEnd_1005977 : Nat := 229577657052495930693823

theorem tailTrace_1005977 : CollatzResearch.WordTrace tailWord_1005977 prefixEnd_1005977 229577657052495930693823 := by
  unfold tailWord_1005977
  simp only [CollatzResearch.WordTrace]
  refine ⟨36690995476524611038440185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24460663651016407358960123 36690995476524611038440185)
  ·
    refine ⟨27518246607393458278830139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36690995476524611038440185 27518246607393458278830139)
    ·
      refine ⟨41277369911090187418245209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27518246607393458278830139 41277369911090187418245209)
      ·
        refine ⟨30958027433317640563683907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41277369911090187418245209 30958027433317640563683907)
        ·
          refine ⟨46437041149976460845525861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30958027433317640563683907 46437041149976460845525861)
          ·
            refine ⟨8706945215620586408536099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46437041149976460845525861 8706945215620586408536099)
            ·
              refine ⟨13060417823430879612804149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706945215620586408536099 13060417823430879612804149)
              ·
                refine ⟨1224414170946644963700389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13060417823430879612804149 1224414170946644963700389)
                ·
                  refine ⟨229577657052495930693823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224414170946644963700389 229577657052495930693823)
                  ·
                    rfl

theorem cell21_1005977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_1005977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1005977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1005977 prefixEnd_1005977 := by exact prefixLift 1005977
  have htrace : WordTrace (prefixWord ++ tailWord_1005977) baseStart_1005977 baseEnd_1005977 := by
    simpa [prefixWord, tailWord_1005977, baseEnd_1005977] using wordTrace_append hprefix tailTrace_1005977
  have hstable : (prefixWord ++ tailWord_1005977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005977).length < 2 ^ (prefixWord ++ tailWord_1005977).sum := by decide
  have hdescent : baseEnd_1005977 < baseStart_1005977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006056 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_1006056 : Nat := 118140960795 + 1006056 * 2 ^ 59
def prefixEnd_1006056 : Nat := 4983230072969 + 3 ^ 40 * 1006056 * 2
def baseEnd_1006056 : Nat := 229595685928809348876995

theorem tailTrace_1006056 : CollatzResearch.WordTrace tailWord_1006056 prefixEnd_1006056 229595685928809348876995 := by
  unfold tailWord_1006056
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346938421619203765283011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24462584562158938353710681 18346938421619203765283011)
  ·
    refine ⟨27520407632428805647924517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346938421619203765283011 27520407632428805647924517)
    ·
      refine ⟨5160076431080401058985847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27520407632428805647924517 5160076431080401058985847)
      ·
        refine ⟨7740114646620601588478771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160076431080401058985847 7740114646620601588478771)
        ·
          refine ⟨11610171969930902382718157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740114646620601588478771 11610171969930902382718157)
          ·
            refine ⟨4353814488724088393519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11610171969930902382718157 4353814488724088393519309)
            ·
              refine ⟨1632680433271533147569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4353814488724088393519309 1632680433271533147569741)
              ·
                refine ⟨612255162476824930338653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632680433271533147569741 612255162476824930338653)
                ·
                  refine ⟨229595685928809348876995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612255162476824930338653 229595685928809348876995)
                  ·
                    rfl

theorem cell21_1006056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_1006056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006056 prefixEnd_1006056 := by exact prefixLift 1006056
  have htrace : WordTrace (prefixWord ++ tailWord_1006056) baseStart_1006056 baseEnd_1006056 := by
    simpa [prefixWord, tailWord_1006056, baseEnd_1006056] using wordTrace_append hprefix tailTrace_1006056
  have hstable : (prefixWord ++ tailWord_1006056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006056).length < 2 ^ (prefixWord ++ tailWord_1006056).sum := by decide
  have hdescent : baseEnd_1006056 < baseStart_1006056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006070 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1006070 : Nat := 118140960795 + 1006070 * 2 ^ 59
def prefixEnd_1006070 : Nat := 4983230072969 + 3 ^ 40 * 1006070 * 2
def baseEnd_1006070 : Nat := 229598880919548435643633

theorem tailTrace_1006070 : CollatzResearch.WordTrace tailWord_1006070 prefixEnd_1006070 229598880919548435643633 := by
  unfold tailWord_1006070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293399216574230495098479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24462924976791791947717109 2293399216574230495098479)
  ·
    refine ⟨3440098824861345742647719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2293399216574230495098479 3440098824861345742647719)
    ·
      refine ⟨5160148237292018613971579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440098824861345742647719 5160148237292018613971579)
      ·
        refine ⟨7740222355938027920957369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160148237292018613971579 7740222355938027920957369)
        ·
          refine ⟨5805166766953520940718027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7740222355938027920957369 5805166766953520940718027)
          ·
            refine ⟨8707750150430281411077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805166766953520940718027 8707750150430281411077041)
            ·
              refine ⟨6530812612822711058307781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707750150430281411077041 6530812612822711058307781)
              ·
                refine ⟨1224527364904258323432709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6530812612822711058307781 1224527364904258323432709)
                ·
                  refine ⟨229598880919548435643633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224527364904258323432709 229598880919548435643633)
                  ·
                    rfl

theorem cell21_1006070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1006070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006070 prefixEnd_1006070 := by exact prefixLift 1006070
  have htrace : WordTrace (prefixWord ++ tailWord_1006070) baseStart_1006070 baseEnd_1006070 := by
    simpa [prefixWord, tailWord_1006070, baseEnd_1006070] using wordTrace_append hprefix tailTrace_1006070
  have hstable : (prefixWord ++ tailWord_1006070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006070).length < 2 ^ (prefixWord ++ tailWord_1006070).sum := by decide
  have hdescent : baseEnd_1006070 < baseStart_1006070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006084 : List Nat := [2, 3, 2, 3, 1, 1, 1, 8]
def baseStart_1006084 : Nat := 118140960795 + 1006084 * 2 ^ 59
def prefixEnd_1006084 : Nat := 4983230072969 + 3 ^ 40 * 1006084 * 2
def baseEnd_1006084 : Nat := 76534025303429174136757

theorem tailTrace_1006084 : CollatzResearch.WordTrace tailWord_1006084 prefixEnd_1006084 76534025303429174136757 := by
  unfold tailWord_1006084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347449043568484156292653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24463265391424645541723537 18347449043568484156292653)
  ·
    refine ⟨6880293391338181558609745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18347449043568484156292653 6880293391338181558609745)
    ·
      refine ⟨5160220043503636168957309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6880293391338181558609745 5160220043503636168957309)
      ·
        refine ⟨1935082516313863563358991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5160220043503636168957309 1935082516313863563358991)
        ·
          refine ⟨2902623774470795345038487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935082516313863563358991 2902623774470795345038487)
          ·
            refine ⟨4353935661706193017557731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902623774470795345038487 4353935661706193017557731)
            ·
              refine ⟨6530903492559289526336597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353935661706193017557731 6530903492559289526336597)
              ·
                refine ⟨76534025303429174136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6530903492559289526336597 76534025303429174136757)
                ·
                  rfl

theorem cell21_1006084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_1006084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006084 prefixEnd_1006084 := by exact prefixLift 1006084
  have htrace : WordTrace (prefixWord ++ tailWord_1006084) baseStart_1006084 baseEnd_1006084 := by
    simpa [prefixWord, tailWord_1006084, baseEnd_1006084] using wordTrace_append hprefix tailTrace_1006084
  have hstable : (prefixWord ++ tailWord_1006084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006084).length < 2 ^ (prefixWord ++ tailWord_1006084).sum := by decide
  have hdescent : baseEnd_1006084 < baseStart_1006084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006129 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1006129 : Nat := 118140960795 + 1006129 * 2 ^ 59
def prefixEnd_1006129 : Nat := 4983230072969 + 3 ^ 40 * 1006129 * 2
def baseEnd_1006129 : Nat := 229612345523377444160179

theorem tailTrace_1006129 : CollatzResearch.WordTrace tailWord_1006129 prefixEnd_1006129 229612345523377444160179 := by
  unfold tailWord_1006129
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696539371973940997973441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24464359581315960665315627 36696539371973940997973441)
  ·
    refine ⟨27522404528980455748480081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36696539371973940997973441 27522404528980455748480081)
    ·
      refine ⟨20641803396735341811360061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27522404528980455748480081 20641803396735341811360061)
      ·
        refine ⟨7740676273775753179260023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20641803396735341811360061 7740676273775753179260023)
        ·
          refine ⟨11611014410663629768890035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740676273775753179260023 11611014410663629768890035)
          ·
            refine ⟨17416521615995444653335053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611014410663629768890035 17416521615995444653335053)
            ·
              refine ⟨6531195605998291745000645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17416521615995444653335053 6531195605998291745000645)
              ·
                refine ⟨1224599176124679702187621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6531195605998291745000645 1224599176124679702187621)
                ·
                  refine ⟨229612345523377444160179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224599176124679702187621 229612345523377444160179)
                  ·
                    rfl

theorem cell21_1006129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1006129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006129 prefixEnd_1006129 := by exact prefixLift 1006129
  have htrace : WordTrace (prefixWord ++ tailWord_1006129) baseStart_1006129 baseEnd_1006129 := by
    simpa [prefixWord, tailWord_1006129, baseEnd_1006129] using wordTrace_append hprefix tailTrace_1006129
  have hstable : (prefixWord ++ tailWord_1006129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006129).length < 2 ^ (prefixWord ++ tailWord_1006129).sum := by decide
  have hdescent : baseEnd_1006129 < baseStart_1006129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006191 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 3]
def baseStart_1006191 : Nat := 118140960795 + 1006191 * 2 ^ 59
def prefixEnd_1006191 : Nat := 4983230072969 + 3 ^ 40 * 1006191 * 2
def baseEnd_1006191 : Nat := 229626494768079114126719

theorem tailTrace_1006191 : CollatzResearch.WordTrace tailWord_1006191 prefixEnd_1006191 229626494768079114126719 := by
  unfold tailWord_1006191
  simp only [CollatzResearch.WordTrace]
  refine ⟨36698800697749325586730427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24465867131832883724486951 36698800697749325586730427)
  ·
    refine ⟨55048201046623988380095641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36698800697749325586730427 55048201046623988380095641)
    ·
      refine ⟨41286150784967991285071731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55048201046623988380095641 41286150784967991285071731)
      ·
        refine ⟨61929226177451986927607597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41286150784967991285071731 61929226177451986927607597)
        ·
          refine ⟨23223459816544495097852849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61929226177451986927607597 23223459816544495097852849)
          ·
            refine ⟨17417594862408371323389637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23223459816544495097852849 17417594862408371323389637)
            ·
              refine ⟨3265799036701569623135557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17417594862408371323389637 3265799036701569623135557)
              ·
                refine ⟨612337319381544304337917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3265799036701569623135557 612337319381544304337917)
                ·
                  refine ⟨229626494768079114126719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612337319381544304337917 229626494768079114126719)
                  ·
                    rfl

theorem cell21_1006191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].length) (baseStart_1006191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006191 prefixEnd_1006191 := by exact prefixLift 1006191
  have htrace : WordTrace (prefixWord ++ tailWord_1006191) baseStart_1006191 baseEnd_1006191 := by
    simpa [prefixWord, tailWord_1006191, baseEnd_1006191] using wordTrace_append hprefix tailTrace_1006191
  have hstable : (prefixWord ++ tailWord_1006191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006191).length < 2 ^ (prefixWord ++ tailWord_1006191).sum := by decide
  have hdescent : baseEnd_1006191 < baseStart_1006191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006236 : List Nat := [2, 2, 3, 2, 2, 3, 7]
def baseStart_1006236 : Nat := 118140960795 + 1006236 * 2 ^ 59
def prefixEnd_1006236 : Nat := 4983230072969 + 3 ^ 40 * 1006236 * 2
def baseEnd_1006236 : Nat := 25515196042352115097403

theorem tailTrace_1006236 : CollatzResearch.WordTrace tailWord_1006236 prefixEnd_1006236 25515196042352115097403 := by
  unfold tailWord_1006236
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350220991293149136059281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24466961321724198848079041 18350220991293149136059281)
  ·
    refine ⟨13762665743469861852044461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18350220991293149136059281 13762665743469861852044461)
    ·
      refine ⟨5160999653801198194516673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13762665743469861852044461 5160999653801198194516673)
      ·
        refine ⟨3870749740350898645887505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5160999653801198194516673 3870749740350898645887505)
        ·
          refine ⟨2903062305263173984415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870749740350898645887505 2903062305263173984415629)
          ·
            refine ⟨1088648364473690244155861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2903062305263173984415629 1088648364473690244155861)
            ·
              refine ⟨25515196042352115097403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1088648364473690244155861 25515196042352115097403)
              ·
                rfl

theorem cell21_1006236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 7].length) (baseStart_1006236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006236 prefixEnd_1006236 := by exact prefixLift 1006236
  have htrace : WordTrace (prefixWord ++ tailWord_1006236) baseStart_1006236 baseEnd_1006236 := by
    simpa [prefixWord, tailWord_1006236, baseEnd_1006236] using wordTrace_append hprefix tailTrace_1006236
  have hstable : (prefixWord ++ tailWord_1006236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006236).length < 2 ^ (prefixWord ++ tailWord_1006236).sum := by decide
  have hdescent : baseEnd_1006236 < baseStart_1006236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006416 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1006416 : Nat := 118140960795 + 1006416 * 2 ^ 59
def prefixEnd_1006416 : Nat := 4983230072969 + 3 ^ 40 * 1006416 * 2
def baseEnd_1006416 : Nat := 229677842833528722876259

theorem tailTrace_1006416 : CollatzResearch.WordTrace tailWord_1006416 prefixEnd_1006416 229677842833528722876259 := by
  unfold tailWord_1006416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353503560967094506835551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24471338081289459342447401 18353503560967094506835551)
  ·
    refine ⟨27530255341450641760253327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18353503560967094506835551 27530255341450641760253327)
    ·
      refine ⟨41295383012175962640379991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27530255341450641760253327 41295383012175962640379991)
      ·
        refine ⟨61943074518263943960569987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41295383012175962640379991 61943074518263943960569987)
        ·
          refine ⟨92914611777395915940854981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61943074518263943960569987 92914611777395915940854981)
          ·
            refine ⟨17421489708261734238910309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92914611777395915940854981 17421489708261734238910309)
            ·
              refine ⟨3266529320299075169795683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17421489708261734238910309 3266529320299075169795683)
              ·
                refine ⟨4899793980448612754693525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266529320299075169795683 4899793980448612754693525)
                ·
                  refine ⟨229677842833528722876259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4899793980448612754693525 229677842833528722876259)
                  ·
                    rfl

theorem cell21_1006416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1006416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006416 prefixEnd_1006416 := by exact prefixLift 1006416
  have htrace : WordTrace (prefixWord ++ tailWord_1006416) baseStart_1006416 baseEnd_1006416 := by
    simpa [prefixWord, tailWord_1006416, baseEnd_1006416] using wordTrace_append hprefix tailTrace_1006416
  have hstable : (prefixWord ++ tailWord_1006416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006416).length < 2 ^ (prefixWord ++ tailWord_1006416).sum := by decide
  have hdescent : baseEnd_1006416 < baseStart_1006416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006518 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1006518 : Nat := 118140960795 + 1006518 * 2 ^ 59
def prefixEnd_1006518 : Nat := 4983230072969 + 3 ^ 40 * 1006518 * 2
def baseEnd_1006518 : Nat := 229701120623199212176051

theorem tailTrace_1006518 : CollatzResearch.WordTrace tailWord_1006518 prefixEnd_1006518 229701120623199212176051 := by
  unfold tailWord_1006518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294420460472791277117763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24473818245043106955922805 2294420460472791277117763)
  ·
    refine ⟨3441630690709186915676645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294420460472791277117763 3441630690709186915676645)
    ·
      refine ⟨645305754507972546689371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3441630690709186915676645 645305754507972546689371)
      ·
        refine ⟨967958631761958820034057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645305754507972546689371 967958631761958820034057)
        ·
          refine ⟨725968973821469115025543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967958631761958820034057 725968973821469115025543)
          ·
            refine ⟨1088953460732203672538315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725968973821469115025543 1088953460732203672538315)
            ·
              refine ⟨1633430191098305508807473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088953460732203672538315 1633430191098305508807473)
              ·
                refine ⟨1225072643323729131605605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633430191098305508807473 1225072643323729131605605)
                ·
                  refine ⟨229701120623199212176051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225072643323729131605605 229701120623199212176051)
                  ·
                    rfl

theorem cell21_1006518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1006518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006518 prefixEnd_1006518 := by exact prefixLift 1006518
  have htrace : WordTrace (prefixWord ++ tailWord_1006518) baseStart_1006518 baseEnd_1006518 := by
    simpa [prefixWord, tailWord_1006518, baseEnd_1006518] using wordTrace_append hprefix tailTrace_1006518
  have hstable : (prefixWord ++ tailWord_1006518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006518).length < 2 ^ (prefixWord ++ tailWord_1006518).sum := by decide
  have hdescent : baseEnd_1006518 < baseStart_1006518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006554 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1006554 : Nat := 118140960795 + 1006554 * 2 ^ 59
def prefixEnd_1006554 : Nat := 4983230072969 + 3 ^ 40 * 1006554 * 2
def baseEnd_1006554 : Nat := 229709336313671149575977

theorem tailTrace_1006554 : CollatzResearch.WordTrace tailWord_1006554 prefixEnd_1006554 229709336313671149575977 := by
  unfold tailWord_1006554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178010098858559645548679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24474693596956159054796477 9178010098858559645548679)
  ·
    refine ⟨13767015148287839468323019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9178010098858559645548679 13767015148287839468323019)
    ·
      refine ⟨20650522722431759202484529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767015148287839468323019 20650522722431759202484529)
      ·
        refine ⟨15487892041823819401863397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20650522722431759202484529 15487892041823819401863397)
        ·
          refine ⟨2903979757841966137849387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15487892041823819401863397 2903979757841966137849387)
          ·
            refine ⟨4355969636762949206774081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903979757841966137849387 4355969636762949206774081)
            ·
              refine ⟨3266977227572211905080561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355969636762949206774081 3266977227572211905080561)
              ·
                refine ⟨2450232920679158928810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266977227572211905080561 2450232920679158928810421)
                ·
                  refine ⟨229709336313671149575977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450232920679158928810421 229709336313671149575977)
                  ·
                    rfl

theorem cell21_1006554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1006554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006554 prefixEnd_1006554 := by exact prefixLift 1006554
  have htrace : WordTrace (prefixWord ++ tailWord_1006554) baseStart_1006554 baseEnd_1006554 := by
    simpa [prefixWord, tailWord_1006554, baseEnd_1006554] using wordTrace_append hprefix tailTrace_1006554
  have hstable : (prefixWord ++ tailWord_1006554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006554).length < 2 ^ (prefixWord ++ tailWord_1006554).sum := by decide
  have hdescent : baseEnd_1006554 < baseStart_1006554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006557 : List Nat := [1, 4, 3, 1, 2, 3, 2, 5]
def baseStart_1006557 : Nat := 118140960795 + 1006557 * 2 ^ 59
def prefixEnd_1006557 : Nat := 4983230072969 + 3 ^ 40 * 1006557 * 2
def baseEnd_1006557 : Nat := 76570006984847937008657

theorem tailTrace_1006557 : CollatzResearch.WordTrace tailWord_1006557 prefixEnd_1006557 76570006984847937008657 := by
  unfold tailWord_1006557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36712149814423370094553925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24474766542948913396369283 36712149814423370094553925)
  ·
    refine ⟨6883528090204381892728861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36712149814423370094553925 6883528090204381892728861)
    ·
      refine ⟨2581323033826643209773323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6883528090204381892728861 2581323033826643209773323)
      ·
        refine ⟨3871984550739964814659985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581323033826643209773323 3871984550739964814659985)
        ·
          refine ⟨2903988413054973610994989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3871984550739964814659985 2903988413054973610994989)
          ·
            refine ⟨1088995654895615104123121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2903988413054973610994989 1088995654895615104123121)
            ·
              refine ⟨816746741171711328092341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088995654895615104123121 816746741171711328092341)
              ·
                refine ⟨76570006984847937008657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816746741171711328092341 76570006984847937008657)
                ·
                  rfl

theorem cell21_1006557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].length) (baseStart_1006557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006557 prefixEnd_1006557 := by exact prefixLift 1006557
  have htrace : WordTrace (prefixWord ++ tailWord_1006557) baseStart_1006557 baseEnd_1006557 := by
    simpa [prefixWord, tailWord_1006557, baseEnd_1006557] using wordTrace_append hprefix tailTrace_1006557
  have hstable : (prefixWord ++ tailWord_1006557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006557).length < 2 ^ (prefixWord ++ tailWord_1006557).sum := by decide
  have hdescent : baseEnd_1006557 < baseStart_1006557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006568 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1006568 : Nat := 118140960795 + 1006568 * 2 ^ 59
def prefixEnd_1006568 : Nat := 4983230072969 + 3 ^ 40 * 1006568 * 2
def baseEnd_1006568 : Nat := 229712531304410236342615

theorem tailTrace_1006568 : CollatzResearch.WordTrace tailWord_1006568 prefixEnd_1006568 229712531304410236342615 := by
  unfold tailWord_1006568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356275508691759486602179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24475034011589012648802905 18356275508691759486602179)
  ·
    refine ⟨27534413263037639229903269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18356275508691759486602179 27534413263037639229903269)
    ·
      refine ⟨5162702486819557355606863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27534413263037639229903269 5162702486819557355606863)
      ·
        refine ⟨7744053730229336033410295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162702486819557355606863 7744053730229336033410295)
        ·
          refine ⟨11616080595344004050115443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744053730229336033410295 11616080595344004050115443)
          ·
            refine ⟨17424120893016006075173165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616080595344004050115443 17424120893016006075173165)
            ·
              refine ⟨6534045334881002278189937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17424120893016006075173165 6534045334881002278189937)
              ·
                refine ⟨4900534001160751708642453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534045334881002278189937 4900534001160751708642453)
                ·
                  refine ⟨229712531304410236342615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4900534001160751708642453 229712531304410236342615)
                  ·
                    rfl

theorem cell21_1006568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1006568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006568 prefixEnd_1006568 := by exact prefixLift 1006568
  have htrace : WordTrace (prefixWord ++ tailWord_1006568) baseStart_1006568 baseEnd_1006568 := by
    simpa [prefixWord, tailWord_1006568, baseEnd_1006568] using wordTrace_append hprefix tailTrace_1006568
  have hstable : (prefixWord ++ tailWord_1006568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006568).length < 2 ^ (prefixWord ++ tailWord_1006568).sum := by decide
  have hdescent : baseEnd_1006568 < baseStart_1006568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006580 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1006580 : Nat := 118140960795 + 1006580 * 2 ^ 59
def prefixEnd_1006580 : Nat := 4983230072969 + 3 ^ 40 * 1006580 * 2
def baseEnd_1006580 : Nat := 229715269867900882142591

theorem tailTrace_1006580 : CollatzResearch.WordTrace tailWord_1006580 prefixEnd_1006580 229715269867900882142591 := by
  unfold tailWord_1006580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356494346670022511320597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24475325795560030015094129 18356494346670022511320597)
  ·
    refine ⟨860460672500157305218153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18356494346670022511320597 860460672500157305218153)
    ·
      refine ⟨645345504375117978913615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860460672500157305218153 645345504375117978913615)
      ·
        refine ⟨968018256562676968370423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645345504375117978913615 968018256562676968370423)
        ·
          refine ⟨1452027384844015452555635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968018256562676968370423 1452027384844015452555635)
          ·
            refine ⟨2178041077266023178833453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452027384844015452555635 2178041077266023178833453)
            ·
              refine ⟨816765403974758692062545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178041077266023178833453 816765403974758692062545)
              ·
                refine ⟨612574052981069019046909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816765403974758692062545 612574052981069019046909)
                ·
                  refine ⟨229715269867900882142591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612574052981069019046909 229715269867900882142591)
                  ·
                    rfl

theorem cell21_1006580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1006580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006580 prefixEnd_1006580 := by exact prefixLift 1006580
  have htrace : WordTrace (prefixWord ++ tailWord_1006580) baseStart_1006580 baseEnd_1006580 := by
    simpa [prefixWord, tailWord_1006580, baseEnd_1006580] using wordTrace_append hprefix tailTrace_1006580
  have hstable : (prefixWord ++ tailWord_1006580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006580).length < 2 ^ (prefixWord ++ tailWord_1006580).sum := by decide
  have hdescent : baseEnd_1006580 < baseStart_1006580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006588 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_1006588 : Nat := 118140960795 + 1006588 * 2 ^ 59
def prefixEnd_1006588 : Nat := 4983230072969 + 3 ^ 40 * 1006588 * 2
def baseEnd_1006588 : Nat := 229717095576894646009241

theorem tailTrace_1006588 : CollatzResearch.WordTrace tailWord_1006588 prefixEnd_1006588 229717095576894646009241 := by
  unfold tailWord_1006588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356640238655531194466209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24475520318207374925954945 18356640238655531194466209)
  ·
    refine ⟨13767480178991648395849657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18356640238655531194466209 13767480178991648395849657)
    ·
      refine ⟨10325610134243736296887243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13767480178991648395849657 10325610134243736296887243)
      ·
        refine ⟨15488415201365604445330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325610134243736296887243 15488415201365604445330865)
        ·
          refine ⟨11616311401024203333998149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15488415201365604445330865 11616311401024203333998149)
          ·
            refine ⟨2178058387692038125124653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11616311401024203333998149 2178058387692038125124653)
            ·
              refine ⟨816771895384514296921745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178058387692038125124653 816771895384514296921745)
              ·
                refine ⟨612578921538385722691309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816771895384514296921745 612578921538385722691309)
                ·
                  refine ⟨229717095576894646009241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612578921538385722691309 229717095576894646009241)
                  ·
                    rfl

theorem cell21_1006588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_1006588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006588 prefixEnd_1006588 := by exact prefixLift 1006588
  have htrace : WordTrace (prefixWord ++ tailWord_1006588) baseStart_1006588 baseEnd_1006588 := by
    simpa [prefixWord, tailWord_1006588, baseEnd_1006588] using wordTrace_append hprefix tailTrace_1006588
  have hstable : (prefixWord ++ tailWord_1006588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006588).length < 2 ^ (prefixWord ++ tailWord_1006588).sum := by decide
  have hdescent : baseEnd_1006588 < baseStart_1006588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006599 : List Nat := [1, 1, 4, 3, 1, 1, 4, 6]
def baseStart_1006599 : Nat := 118140960795 + 1006599 * 2 ^ 59
def prefixEnd_1006599 : Nat := 4983230072969 + 3 ^ 40 * 1006599 * 2
def baseEnd_1006599 : Nat := 76573201975587023775295

theorem tailTrace_1006599 : CollatzResearch.WordTrace tailWord_1006599 prefixEnd_1006599 76573201975587023775295 := by
  unfold tailWord_1006599
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713681680271211267582851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24475787786847474178388567 36713681680271211267582851)
  ·
    refine ⟨55070522520406816901374277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36713681680271211267582851 55070522520406816901374277)
    ·
      refine ⟨10325722972576278169007677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55070522520406816901374277 10325722972576278169007677)
      ·
        refine ⟨3872146114716104313377879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325722972576278169007677 3872146114716104313377879)
        ·
          refine ⟨5808219172074156470066819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872146114716104313377879 5808219172074156470066819)
          ·
            refine ⟨8712328758111234705100229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808219172074156470066819 8712328758111234705100229)
            ·
              refine ⟨1633561642145856507206293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8712328758111234705100229 1633561642145856507206293)
              ·
                refine ⟨76573201975587023775295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1633561642145856507206293 76573201975587023775295)
                ·
                  rfl

theorem cell21_1006599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_1006599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006599 prefixEnd_1006599 := by exact prefixLift 1006599
  have htrace : WordTrace (prefixWord ++ tailWord_1006599) baseStart_1006599 baseEnd_1006599 := by
    simpa [prefixWord, tailWord_1006599, baseEnd_1006599] using wordTrace_append hprefix tailTrace_1006599
  have hstable : (prefixWord ++ tailWord_1006599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006599).length < 2 ^ (prefixWord ++ tailWord_1006599).sum := by decide
  have hdescent : baseEnd_1006599 < baseStart_1006599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006602 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1006602 : Nat := 118140960795 + 1006602 * 2 ^ 59
def prefixEnd_1006602 : Nat := 4983230072969 + 3 ^ 40 * 1006602 * 2
def baseEnd_1006602 : Nat := 229720290567633732775879

theorem tailTrace_1006602 : CollatzResearch.WordTrace tailWord_1006602 prefixEnd_1006602 229720290567633732775879 := by
  unfold tailWord_1006602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178447774815085694985515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24475860732840228519961373 9178447774815085694985515)
  ·
    refine ⟨13767671662222628542478273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9178447774815085694985515 13767671662222628542478273)
    ·
      refine ⟨10325753746666971406858705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13767671662222628542478273 10325753746666971406858705)
      ·
        refine ⟨7744315310000228555144029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10325753746666971406858705 7744315310000228555144029)
        ·
          refine ⟨2904118241250085708179011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7744315310000228555144029 2904118241250085708179011)
          ·
            refine ⟨4356177361875128562268517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904118241250085708179011 4356177361875128562268517)
            ·
              refine ⟨816783255351586605425347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4356177361875128562268517 816783255351586605425347)
              ·
                refine ⟨1225174883027379908138021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816783255351586605425347 1225174883027379908138021)
                ·
                  refine ⟨229720290567633732775879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225174883027379908138021 229720290567633732775879)
                  ·
                    rfl

theorem cell21_1006602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1006602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006602 prefixEnd_1006602 := by exact prefixLift 1006602
  have htrace : WordTrace (prefixWord ++ tailWord_1006602) baseStart_1006602 baseEnd_1006602 := by
    simpa [prefixWord, tailWord_1006602, baseEnd_1006602] using wordTrace_append hprefix tailTrace_1006602
  have hstable : (prefixWord ++ tailWord_1006602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006602).length < 2 ^ (prefixWord ++ tailWord_1006602).sum := by decide
  have hdescent : baseEnd_1006602 < baseStart_1006602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006706 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1006706 : Nat := 118140960795 + 1006706 * 2 ^ 59
def prefixEnd_1006706 : Nat := 4983230072969 + 3 ^ 40 * 1006706 * 2
def baseEnd_1006706 : Nat := 229744024784552663042333

theorem tailTrace_1006706 : CollatzResearch.WordTrace tailWord_1006706 prefixEnd_1006706 229744024784552663042333 := by
  unfold tailWord_1006706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179396072720892135431993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24478389527255712361151981 9179396072720892135431993)
  ·
    refine ⟨6884547054540669101573995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9179396072720892135431993 6884547054540669101573995)
    ·
      refine ⟨10326820581811003652360993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884547054540669101573995 10326820581811003652360993)
      ·
        refine ⟨7745115436358252739270745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326820581811003652360993 7745115436358252739270745)
        ·
          refine ⟨5808836577268689554453059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7745115436358252739270745 5808836577268689554453059)
          ·
            refine ⟨8713254865903034331679589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808836577268689554453059 8713254865903034331679589)
            ·
              refine ⟨1633735287356818937189923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8713254865903034331679589 1633735287356818937189923)
              ·
                refine ⟨2450602931035228405784885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633735287356818937189923 2450602931035228405784885)
                ·
                  refine ⟨229744024784552663042333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450602931035228405784885 229744024784552663042333)
                  ·
                    rfl

theorem cell21_1006706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1006706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006706 prefixEnd_1006706 := by exact prefixLift 1006706
  have htrace : WordTrace (prefixWord ++ tailWord_1006706) baseStart_1006706 baseEnd_1006706 := by
    simpa [prefixWord, tailWord_1006706, baseEnd_1006706] using wordTrace_append hprefix tailTrace_1006706
  have hstable : (prefixWord ++ tailWord_1006706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006706).length < 2 ^ (prefixWord ++ tailWord_1006706).sum := by decide
  have hdescent : baseEnd_1006706 < baseStart_1006706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006720 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1006720 : Nat := 118140960795 + 1006720 * 2 ^ 59
def prefixEnd_1006720 : Nat := 4983230072969 + 3 ^ 40 * 1006720 * 2
def baseEnd_1006720 : Nat := 229747219775291749808971

theorem tailTrace_1006720 : CollatzResearch.WordTrace tailWord_1006720 prefixEnd_1006720 229747219775291749808971 := by
  unfold tailWord_1006720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359047456416424466368807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24478729941888565955158409 18359047456416424466368807)
  ·
    refine ⟨27538571184624636699553211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18359047456416424466368807 27538571184624636699553211)
    ·
      refine ⟨41307856776936955049329817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27538571184624636699553211 41307856776936955049329817)
      ·
        refine ⟨30980892582702716286997363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41307856776936955049329817 30980892582702716286997363)
        ·
          refine ⟨46471338874054074430496045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30980892582702716286997363 46471338874054074430496045)
          ·
            refine ⟨17426752077770277911436017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46471338874054074430496045 17426752077770277911436017)
            ·
              refine ⟨13070064058327708433577013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17426752077770277911436017 13070064058327708433577013)
              ·
                refine ⟨1225318505468222665647845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13070064058327708433577013 1225318505468222665647845)
                ·
                  refine ⟨229747219775291749808971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225318505468222665647845 229747219775291749808971)
                  ·
                    rfl

theorem cell21_1006720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1006720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006720 prefixEnd_1006720 := by exact prefixLift 1006720
  have htrace : WordTrace (prefixWord ++ tailWord_1006720) baseStart_1006720 baseEnd_1006720 := by
    simpa [prefixWord, tailWord_1006720, baseEnd_1006720] using wordTrace_append hprefix tailTrace_1006720
  have hstable : (prefixWord ++ tailWord_1006720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006720).length < 2 ^ (prefixWord ++ tailWord_1006720).sum := by decide
  have hdescent : baseEnd_1006720 < baseStart_1006720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006779 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_1006779 : Nat := 118140960795 + 1006779 * 2 ^ 59
def prefixEnd_1006779 : Nat := 4983230072969 + 3 ^ 40 * 1006779 * 2
def baseEnd_1006779 : Nat := 229760684379120758325517

theorem tailTrace_1006779 : CollatzResearch.WordTrace tailWord_1006779 prefixEnd_1006779 229760684379120758325517 := by
  unfold tailWord_1006779
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720246819619102009135391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24480164546412734672756927 36720246819619102009135391)
  ·
    refine ⟨55080370229428653013703087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36720246819619102009135391 55080370229428653013703087)
    ·
      refine ⟨82620555344142979520554631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55080370229428653013703087 82620555344142979520554631)
      ·
        refine ⟨123930833016214469280831947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82620555344142979520554631 123930833016214469280831947)
        ·
          refine ⟨185896249524321703921247921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123930833016214469280831947 185896249524321703921247921)
          ·
            refine ⟨139422187143241277940935941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185896249524321703921247921 139422187143241277940935941)
            ·
              refine ⟨26141660089357739613925489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139422187143241277940935941 26141660089357739613925489)
              ·
                refine ⟨19606245067018304710444117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26141660089357739613925489 19606245067018304710444117)
                ·
                  refine ⟨229760684379120758325517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19606245067018304710444117 229760684379120758325517)
                  ·
                    rfl

theorem cell21_1006779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_1006779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006779 prefixEnd_1006779 := by exact prefixLift 1006779
  have htrace : WordTrace (prefixWord ++ tailWord_1006779) baseStart_1006779 baseEnd_1006779 := by
    simpa [prefixWord, tailWord_1006779, baseEnd_1006779] using wordTrace_append hprefix tailTrace_1006779
  have hstable : (prefixWord ++ tailWord_1006779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006779).length < 2 ^ (prefixWord ++ tailWord_1006779).sum := by decide
  have hdescent : baseEnd_1006779 < baseStart_1006779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006816 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_1006816 : Nat := 118140960795 + 1006816 * 2 ^ 59
def prefixEnd_1006816 : Nat := 4983230072969 + 3 ^ 40 * 1006816 * 2
def baseEnd_1006816 : Nat := 229769128283216916208775

theorem tailTrace_1006816 : CollatzResearch.WordTrace tailWord_1006816 prefixEnd_1006816 229769128283216916208775 := by
  unfold tailWord_1006816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360798160242528664116151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24481064213656704885488201 18360798160242528664116151)
  ·
    refine ⟨27541197240363792996174227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18360798160242528664116151 27541197240363792996174227)
    ·
      refine ⟨41311795860545689494261341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27541197240363792996174227 41311795860545689494261341)
      ·
        refine ⟨15491923447704633560348003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41311795860545689494261341 15491923447704633560348003)
        ·
          refine ⟨23237885171556950340522005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15491923447704633560348003 23237885171556950340522005)
          ·
            refine ⟨1089275867416732047211969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23237885171556950340522005 1089275867416732047211969)
            ·
              refine ⟨816956900562549035408977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089275867416732047211969 816956900562549035408977)
              ·
                refine ⟨612717675421911776556733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816956900562549035408977 612717675421911776556733)
                ·
                  refine ⟨229769128283216916208775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612717675421911776556733 229769128283216916208775)
                  ·
                    rfl

theorem cell21_1006816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_1006816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006816 prefixEnd_1006816 := by exact prefixLift 1006816
  have htrace : WordTrace (prefixWord ++ tailWord_1006816) baseStart_1006816 baseEnd_1006816 := by
    simpa [prefixWord, tailWord_1006816, baseEnd_1006816] using wordTrace_append hprefix tailTrace_1006816
  have hstable : (prefixWord ++ tailWord_1006816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006816).length < 2 ^ (prefixWord ++ tailWord_1006816).sum := by decide
  have hdescent : baseEnd_1006816 < baseStart_1006816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006827 : List Nat := [1, 1, 1, 1, 2, 8, 1, 6]
def baseStart_1006827 : Nat := 118140960795 + 1006827 * 2 ^ 59
def prefixEnd_1006827 : Nat := 4983230072969 + 3 ^ 40 * 1006827 * 2
def baseEnd_1006827 : Nat := 76590546211027780508473

theorem tailTrace_1006827 : CollatzResearch.WordTrace tailWord_1006827 prefixEnd_1006827 76590546211027780508473 := by
  unfold tailWord_1006827
  simp only [CollatzResearch.WordTrace]
  refine ⟨36721997523445206206882735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24481331682296804137921823 36721997523445206206882735)
  ·
    refine ⟨55082996285167809310324103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36721997523445206206882735 55082996285167809310324103)
    ·
      refine ⟨82624494427751713965486155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55082996285167809310324103 82624494427751713965486155)
      ·
        refine ⟨123936741641627570948229233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82624494427751713965486155 123936741641627570948229233)
        ·
          refine ⟨92952556231220678211171925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123936741641627570948229233 92952556231220678211171925)
          ·
            refine ⟨1089287768334617322787171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 92952556231220678211171925 1089287768334617322787171)
            ·
              refine ⟨1633931652501925984180757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089287768334617322787171 1633931652501925984180757)
              ·
                refine ⟨76590546211027780508473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1633931652501925984180757 76590546211027780508473)
                ·
                  rfl

theorem cell21_1006827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_1006827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006827 prefixEnd_1006827 := by exact prefixLift 1006827
  have htrace : WordTrace (prefixWord ++ tailWord_1006827) baseStart_1006827 baseEnd_1006827 := by
    simpa [prefixWord, tailWord_1006827, baseEnd_1006827] using wordTrace_append hprefix tailTrace_1006827
  have hstable : (prefixWord ++ tailWord_1006827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006827).length < 2 ^ (prefixWord ++ tailWord_1006827).sum := by decide
  have hdescent : baseEnd_1006827 < baseStart_1006827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006841 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1006841 : Nat := 118140960795 + 1006841 * 2 ^ 59
def prefixEnd_1006841 : Nat := 4983230072969 + 3 ^ 40 * 1006841 * 2
def baseEnd_1006841 : Nat := 229774833623822428292057

theorem tailTrace_1006841 : CollatzResearch.WordTrace tailWord_1006841 prefixEnd_1006841 229774833623822428292057 := by
  unfold tailWord_1006841
  simp only [CollatzResearch.WordTrace]
  refine ⟨36722508145394486597892377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24481672096929657731928251 36722508145394486597892377)
  ·
    refine ⟨27541881109045864948419283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36722508145394486597892377 27541881109045864948419283)
    ·
      refine ⟨41312821663568797422628925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27541881109045864948419283 41312821663568797422628925)
      ·
        refine ⟨15492308123838299033485847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41312821663568797422628925 15492308123838299033485847)
        ·
          refine ⟨23238462185757448550228771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15492308123838299033485847 23238462185757448550228771)
          ·
            refine ⟨34857693278636172825343157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23238462185757448550228771 34857693278636172825343157)
            ·
              refine ⟨3267908744872141202375921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34857693278636172825343157 3267908744872141202375921)
              ·
                refine ⟨2450931558654105901781941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267908744872141202375921 2450931558654105901781941)
                ·
                  refine ⟨229774833623822428292057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450931558654105901781941 229774833623822428292057)
                  ·
                    rfl

theorem cell21_1006841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1006841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006841 prefixEnd_1006841 := by exact prefixLift 1006841
  have htrace : WordTrace (prefixWord ++ tailWord_1006841) baseStart_1006841 baseEnd_1006841 := by
    simpa [prefixWord, tailWord_1006841, baseEnd_1006841] using wordTrace_append hprefix tailTrace_1006841
  have hstable : (prefixWord ++ tailWord_1006841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006841).length < 2 ^ (prefixWord ++ tailWord_1006841).sum := by decide
  have hdescent : baseEnd_1006841 < baseStart_1006841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006844 : List Nat := [2, 2, 2, 1, 5, 1, 3, 5]
def baseStart_1006844 : Nat := 118140960795 + 1006844 * 2 ^ 59
def prefixEnd_1006844 : Nat := 4983230072969 + 3 ^ 40 * 1006844 * 2
def baseEnd_1006844 : Nat := 76591839421565029914017

theorem tailTrace_1006844 : CollatzResearch.WordTrace tailWord_1006844 prefixEnd_1006844 76591839421565029914017 := by
  unfold tailWord_1006844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361308782191809055125793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24481745042922412073501057 18361308782191809055125793)
  ·
    refine ⟨13770981586643856791344345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18361308782191809055125793 13770981586643856791344345)
    ·
      refine ⟨10328236189982892593508259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13770981586643856791344345 10328236189982892593508259)
      ·
        refine ⟨15492354284974338890262389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328236189982892593508259 15492354284974338890262389)
        ·
          refine ⟨1452408214216344270962099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15492354284974338890262389 1452408214216344270962099)
          ·
            refine ⟨2178612321324516406443149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452408214216344270962099 2178612321324516406443149)
            ·
              refine ⟨816979620496693652416181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178612321324516406443149 816979620496693652416181)
              ·
                refine ⟨76591839421565029914017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816979620496693652416181 76591839421565029914017)
                ·
                  rfl

theorem cell21_1006844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_1006844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006844 prefixEnd_1006844 := by exact prefixLift 1006844
  have htrace : WordTrace (prefixWord ++ tailWord_1006844) baseStart_1006844 baseEnd_1006844 := by
    simpa [prefixWord, tailWord_1006844, baseEnd_1006844] using wordTrace_append hprefix tailTrace_1006844
  have hstable : (prefixWord ++ tailWord_1006844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006844).length < 2 ^ (prefixWord ++ tailWord_1006844).sum := by decide
  have hdescent : baseEnd_1006844 < baseStart_1006844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006872 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1006872 : Nat := 118140960795 + 1006872 * 2 ^ 59
def prefixEnd_1006872 : Nat := 4983230072969 + 3 ^ 40 * 1006872 * 2
def baseEnd_1006872 : Nat := 229781908246173263275327

theorem tailTrace_1006872 : CollatzResearch.WordTrace tailWord_1006872 prefixEnd_1006872 229781908246173263275327 := by
  unfold tailWord_1006872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361819404141089446135435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24482425872188119261513913 18361819404141089446135435)
  ·
    refine ⟨27542729106211634169203153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18361819404141089446135435 27542729106211634169203153)
    ·
      refine ⟨20657046829658725626902365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27542729106211634169203153 20657046829658725626902365)
      ·
        refine ⟨7746392561122022110088387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20657046829658725626902365 7746392561122022110088387)
        ·
          refine ⟨11619588841683033165132581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746392561122022110088387 11619588841683033165132581)
          ·
            refine ⟨2178672907815568718462359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11619588841683033165132581 2178672907815568718462359)
            ·
              refine ⟨3268009361723353077693539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178672907815568718462359 3268009361723353077693539)
              ·
                refine ⟨4902014042585029616540309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268009361723353077693539 4902014042585029616540309)
                ·
                  refine ⟨229781908246173263275327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4902014042585029616540309 229781908246173263275327)
                  ·
                    rfl

theorem cell21_1006872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1006872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006872 prefixEnd_1006872 := by exact prefixLift 1006872
  have htrace : WordTrace (prefixWord ++ tailWord_1006872) baseStart_1006872 baseEnd_1006872 := by
    simpa [prefixWord, tailWord_1006872, baseEnd_1006872] using wordTrace_append hprefix tailTrace_1006872
  have hstable : (prefixWord ++ tailWord_1006872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006872).length < 2 ^ (prefixWord ++ tailWord_1006872).sum := by decide
  have hdescent : baseEnd_1006872 < baseStart_1006872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006909 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1006909 : Nat := 118140960795 + 1006909 * 2 ^ 59
def prefixEnd_1006909 : Nat := 4983230072969 + 3 ^ 40 * 1006909 * 2
def baseEnd_1006909 : Nat := 229790352150269421158585

theorem tailTrace_1006909 : CollatzResearch.WordTrace tailWord_1006909 prefixEnd_1006909 229790352150269421158585 := by
  unfold tailWord_1006909
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724988309148134211367781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483325539432089474245187 36724988309148134211367781)
  ·
    refine ⟨6885935307965275164631459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36724988309148134211367781 6885935307965275164631459)
    ·
      refine ⟨10328902961947912746947189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885935307965275164631459 10328902961947912746947189)
      ·
        refine ⟨968334652682616820026299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10328902961947912746947189 968334652682616820026299)
        ·
          refine ⟨1452501979023925230039449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968334652682616820026299 1452501979023925230039449)
          ·
            refine ⟨1089376484267943922529587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452501979023925230039449 1089376484267943922529587)
            ·
              refine ⟨1634064726401915883794381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089376484267943922529587 1634064726401915883794381)
              ·
                refine ⟨612774272400718456422893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634064726401915883794381 612774272400718456422893)
                ·
                  refine ⟨229790352150269421158585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612774272400718456422893 229790352150269421158585)
                  ·
                    rfl

theorem cell21_1006909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1006909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006909 prefixEnd_1006909 := by exact prefixLift 1006909
  have htrace : WordTrace (prefixWord ++ tailWord_1006909) baseStart_1006909 baseEnd_1006909 := by
    simpa [prefixWord, tailWord_1006909, baseEnd_1006909] using wordTrace_append hprefix tailTrace_1006909
  have hstable : (prefixWord ++ tailWord_1006909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006909).length < 2 ^ (prefixWord ++ tailWord_1006909).sum := by decide
  have hdescent : baseEnd_1006909 < baseStart_1006909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006931 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_1006931 : Nat := 118140960795 + 1006931 * 2 ^ 59
def prefixEnd_1006931 : Nat := 4983230072969 + 3 ^ 40 * 1006931 * 2
def baseEnd_1006931 : Nat := 229795372850002271791873

theorem tailTrace_1006931 : CollatzResearch.WordTrace tailWord_1006931 prefixEnd_1006931 229795372850002271791873 := by
  unfold tailWord_1006931
  simp only [CollatzResearch.WordTrace]
  refine ⟨36725790715068431968668647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483860476712287979112431 36725790715068431968668647)
  ·
    refine ⟨55088686072602647953002971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36725790715068431968668647 55088686072602647953002971)
    ·
      refine ⟨82633029108903971929504457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55088686072602647953002971 82633029108903971929504457)
      ·
        refine ⟨61974771831677978947128343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82633029108903971929504457 61974771831677978947128343)
        ·
          refine ⟨92962157747516968420692515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61974771831677978947128343 92962157747516968420692515)
          ·
            refine ⟨139443236621275452631038773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92962157747516968420692515 139443236621275452631038773)
            ·
              refine ⟨13072803433244573684159885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139443236621275452631038773 13072803433244573684159885)
              ·
                refine ⟨4902301287466715131559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13072803433244573684159885 4902301287466715131559957)
                ·
                  refine ⟨229795372850002271791873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4902301287466715131559957 229795372850002271791873)
                  ·
                    rfl

theorem cell21_1006931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_1006931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006931 prefixEnd_1006931 := by exact prefixLift 1006931
  have htrace : WordTrace (prefixWord ++ tailWord_1006931) baseStart_1006931 baseEnd_1006931 := by
    simpa [prefixWord, tailWord_1006931, baseEnd_1006931] using wordTrace_append hprefix tailTrace_1006931
  have hstable : (prefixWord ++ tailWord_1006931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006931).length < 2 ^ (prefixWord ++ tailWord_1006931).sum := by decide
  have hdescent : baseEnd_1006931 < baseStart_1006931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006962 : List Nat := [3, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1006962 : Nat := 118140960795 + 1006962 * 2 ^ 59
def prefixEnd_1006962 : Nat := 4983230072969 + 3 ^ 40 * 1006962 * 2
def baseEnd_1006962 : Nat := 76600815824117702258381

theorem tailTrace_1006962 : CollatzResearch.WordTrace tailWord_1006962 prefixEnd_1006962 76600815824117702258381 := by
  unfold tailWord_1006962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181730344489031065761785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24484614251970749508698093 9181730344489031065761785)
  ·
    refine ⟨6886297758366773299321339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9181730344489031065761785 6886297758366773299321339)
    ·
      refine ⟨10329446637550159948982009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886297758366773299321339 10329446637550159948982009)
      ·
        refine ⟨7747084978162619961736507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10329446637550159948982009 7747084978162619961736507)
        ·
          refine ⟨11620627467243929942604761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747084978162619961736507 11620627467243929942604761)
          ·
            refine ⟨8715470600432947456953571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620627467243929942604761 8715470600432947456953571)
            ·
              refine ⟨13073205900649421185430357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715470600432947456953571 13073205900649421185430357)
              ·
                refine ⟨76600815824117702258381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13073205900649421185430357 76600815824117702258381)
                ·
                  rfl

theorem cell21_1006962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1006962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006962 prefixEnd_1006962 := by exact prefixLift 1006962
  have htrace : WordTrace (prefixWord ++ tailWord_1006962) baseStart_1006962 baseEnd_1006962 := by
    simpa [prefixWord, tailWord_1006962, baseEnd_1006962] using wordTrace_append hprefix tailTrace_1006962
  have hstable : (prefixWord ++ tailWord_1006962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006962).length < 2 ^ (prefixWord ++ tailWord_1006962).sum := by decide
  have hdescent : baseEnd_1006962 < baseStart_1006962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006985 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 3]
def baseStart_1006985 : Nat := 118140960795 + 1006985 * 2 ^ 59
def prefixEnd_1006985 : Nat := 4983230072969 + 3 ^ 40 * 1006985 * 2
def baseEnd_1006985 : Nat := 229807696385710177891763

theorem tailTrace_1006985 : CollatzResearch.WordTrace tailWord_1006985 prefixEnd_1006985 229807696385710177891763 := by
  unfold tailWord_1006985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36727760256872799191134409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485173504581866127422939 36727760256872799191134409)
  ·
    refine ⟨27545820192654599393350807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36727760256872799191134409 27545820192654599393350807)
    ·
      refine ⟨41318730288981899090026211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545820192654599393350807 41318730288981899090026211)
      ·
        refine ⟨61978095433472848635039317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41318730288981899090026211 61978095433472848635039317)
        ·
          refine ⟨726305805861009944941867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 61978095433472848635039317 726305805861009944941867)
          ·
            refine ⟨1089458708791514917412801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726305805861009944941867 1089458708791514917412801)
            ·
              refine ⟨817094031593636188059601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089458708791514917412801 817094031593636188059601)
              ·
                refine ⟨612820523695227141044701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817094031593636188059601 612820523695227141044701)
                ·
                  refine ⟨229807696385710177891763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612820523695227141044701 229807696385710177891763)
                  ·
                    rfl

theorem cell21_1006985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_1006985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006985 prefixEnd_1006985 := by exact prefixLift 1006985
  have htrace : WordTrace (prefixWord ++ tailWord_1006985) baseStart_1006985 baseEnd_1006985 := by
    simpa [prefixWord, tailWord_1006985, baseEnd_1006985] using wordTrace_append hprefix tailTrace_1006985
  have hstable : (prefixWord ++ tailWord_1006985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006985).length < 2 ^ (prefixWord ++ tailWord_1006985).sum := by decide
  have hdescent : baseEnd_1006985 < baseStart_1006985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006996 : List Nat := [2, 4, 2, 1, 2, 3, 1, 6]
def baseStart_1006996 : Nat := 118140960795 + 1006996 * 2 ^ 59
def prefixEnd_1006996 : Nat := 4983230072969 + 3 ^ 40 * 1006996 * 2
def baseEnd_1006996 : Nat := 76603402245192201069469

theorem tailTrace_1006996 : CollatzResearch.WordTrace tailWord_1006996 prefixEnd_1006996 76603402245192201069469 := by
  unfold tailWord_1006996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364080729916474034892421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24485440973221965379856561 18364080729916474034892421)
  ·
    refine ⟨3443265136859338881542329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18364080729916474034892421 3443265136859338881542329)
    ·
      refine ⟨2582448852644504161156747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443265136859338881542329 2582448852644504161156747)
      ·
        refine ⟨3873673278966756241735121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582448852644504161156747 3873673278966756241735121)
        ·
          refine ⟨2905254959225067181301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3873673278966756241735121 2905254959225067181301341)
          ·
            refine ⟨1089470609709400192988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2905254959225067181301341 1089470609709400192988003)
            ·
              refine ⟨1634205914564100289482005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089470609709400192988003 1634205914564100289482005)
              ·
                refine ⟨76603402245192201069469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1634205914564100289482005 76603402245192201069469)
                ·
                  rfl

theorem cell21_1006996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_1006996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1006996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1006996 prefixEnd_1006996 := by exact prefixLift 1006996
  have htrace : WordTrace (prefixWord ++ tailWord_1006996) baseStart_1006996 baseEnd_1006996 := by
    simpa [prefixWord, tailWord_1006996, baseEnd_1006996] using wordTrace_append hprefix tailTrace_1006996
  have hstable : (prefixWord ++ tailWord_1006996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006996).length < 2 ^ (prefixWord ++ tailWord_1006996).sum := by decide
  have hdescent : baseEnd_1006996 < baseStart_1006996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007010 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1007010 : Nat := 118140960795 + 1007010 * 2 ^ 59
def prefixEnd_1007010 : Nat := 4983230072969 + 3 ^ 40 * 1007010 * 2
def baseEnd_1007010 : Nat := 229813401726315689975045

theorem tailTrace_1007010 : CollatzResearch.WordTrace tailWord_1007010 prefixEnd_1007010 229813401726315689975045 := by
  unfold tailWord_1007010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182168020445557115198621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24485781387854818973862989 9182168020445557115198621)
  ·
    refine ⟨3443313007667083918199483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9182168020445557115198621 3443313007667083918199483)
    ·
      refine ⟨5164969511500625877299225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443313007667083918199483 5164969511500625877299225)
      ·
        refine ⟨3873727133625469407974419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5164969511500625877299225 3873727133625469407974419)
        ·
          refine ⟨5810590700438204111961629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873727133625469407974419 5810590700438204111961629)
          ·
            refine ⟨2178971512664326541985611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5810590700438204111961629 2178971512664326541985611)
            ·
              refine ⟨3268457268996489812978417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178971512664326541985611 3268457268996489812978417)
              ·
                refine ⟨2451342951747367359733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268457268996489812978417 2451342951747367359733813)
                ·
                  refine ⟨229813401726315689975045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2451342951747367359733813 229813401726315689975045)
                  ·
                    rfl

theorem cell21_1007010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1007010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007010 prefixEnd_1007010 := by exact prefixLift 1007010
  have htrace : WordTrace (prefixWord ++ tailWord_1007010) baseStart_1007010 baseEnd_1007010 := by
    simpa [prefixWord, tailWord_1007010, baseEnd_1007010] using wordTrace_append hprefix tailTrace_1007010
  have hstable : (prefixWord ++ tailWord_1007010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007010).length < 2 ^ (prefixWord ++ tailWord_1007010).sum := by decide
  have hdescent : baseEnd_1007010 < baseStart_1007010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007114 : List Nat := [3, 1, 2, 2, 2, 2, 1, 8]
def baseStart_1007114 : Nat := 118140960795 + 1007114 * 2 ^ 59
def prefixEnd_1007114 : Nat := 4983230072969 + 3 ^ 40 * 1007114 * 2
def baseEnd_1007114 : Nat := 76612378647744873413833

theorem tailTrace_1007114 : CollatzResearch.WordTrace tailWord_1007114 prefixEnd_1007114 76612378647744873413833 := by
  unfold tailWord_1007114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183116318351363555645099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24488310182270302815053597 9183116318351363555645099)
  ·
    refine ⟨13774674477527045333467649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9183116318351363555645099 13774674477527045333467649)
    ·
      refine ⟨10331005858145284000100737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13774674477527045333467649 10331005858145284000100737)
      ·
        refine ⟨7748254393608963000075553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10331005858145284000100737 7748254393608963000075553)
        ·
          refine ⟨5811190795206722250056665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748254393608963000075553 5811190795206722250056665)
          ·
            refine ⟨4358393096405041687542499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5811190795206722250056665 4358393096405041687542499)
            ·
              refine ⟨6537589644607562531313749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358393096405041687542499 6537589644607562531313749)
              ·
                refine ⟨76612378647744873413833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6537589644607562531313749 76612378647744873413833)
                ·
                  rfl

theorem cell21_1007114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_1007114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007114 prefixEnd_1007114 := by exact prefixLift 1007114
  have htrace : WordTrace (prefixWord ++ tailWord_1007114) baseStart_1007114 baseEnd_1007114 := by
    simpa [prefixWord, tailWord_1007114, baseEnd_1007114] using wordTrace_append hprefix tailTrace_1007114
  have hstable : (prefixWord ++ tailWord_1007114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007114).length < 2 ^ (prefixWord ++ tailWord_1007114).sum := by decide
  have hdescent : baseEnd_1007114 < baseStart_1007114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007162 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_1007162 : Nat := 118140960795 + 1007162 * 2 ^ 59
def prefixEnd_1007162 : Nat := 4983230072969 + 3 ^ 40 * 1007162 * 2
def baseEnd_1007162 : Nat := 229848090197197203441401

theorem tailTrace_1007162 : CollatzResearch.WordTrace tailWord_1007162 prefixEnd_1007162 229848090197197203441401 := by
  unfold tailWord_1007162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183553994307889605081935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24489477318154372280218493 9183553994307889605081935)
  ·
    refine ⟨13775330991461834407622903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9183553994307889605081935 13775330991461834407622903)
    ·
      refine ⟨20662996487192751611434355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13775330991461834407622903 20662996487192751611434355)
      ·
        refine ⟨30994494730789127417151533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662996487192751611434355 30994494730789127417151533)
        ·
          refine ⟨11622935524045922781431825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30994494730789127417151533 11622935524045922781431825)
          ·
            refine ⟨8717201643034442086073869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11622935524045922781431825 8717201643034442086073869)
            ·
              refine ⟨3268950616137915782277701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8717201643034442086073869 3268950616137915782277701)
              ·
                refine ⟨612928240525859209177069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3268950616137915782277701 612928240525859209177069)
                ·
                  refine ⟨229848090197197203441401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612928240525859209177069 229848090197197203441401)
                  ·
                    rfl

theorem cell21_1007162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_1007162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007162 prefixEnd_1007162 := by exact prefixLift 1007162
  have htrace : WordTrace (prefixWord ++ tailWord_1007162) baseStart_1007162 baseEnd_1007162 := by
    simpa [prefixWord, tailWord_1007162, baseEnd_1007162] using wordTrace_append hprefix tailTrace_1007162
  have hstable : (prefixWord ++ tailWord_1007162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007162).length < 2 ^ (prefixWord ++ tailWord_1007162).sum := by decide
  have hdescent : baseEnd_1007162 < baseStart_1007162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007255 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 3]
def baseStart_1007255 : Nat := 118140960795 + 1007255 * 2 ^ 59
def prefixEnd_1007255 : Nat := 4983230072969 + 3 ^ 40 * 1007255 * 2
def baseEnd_1007255 : Nat := 229869314064249708391211

theorem tailTrace_1007255 : CollatzResearch.WordTrace tailWord_1007255 prefixEnd_1007255 229869314064249708391211 := by
  unfold tailWord_1007255
  simp only [CollatzResearch.WordTrace]
  refine ⟨36737607965894635303463219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24491738643929756868975479 36737607965894635303463219)
  ·
    refine ⟨55106411948841952955194829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36737607965894635303463219 55106411948841952955194829)
    ·
      refine ⟨20664904480815732358198061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55106411948841952955194829 20664904480815732358198061)
      ·
        refine ⟨7749339180305899634324273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20664904480815732358198061 7749339180305899634324273)
        ·
          refine ⟨5812004385229424725743205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7749339180305899634324273 5812004385229424725743205)
          ·
            refine ⟨1089750822230517136076851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5812004385229424725743205 1089750822230517136076851)
            ·
              refine ⟨1634626233345775704115277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089750822230517136076851 1634626233345775704115277)
              ·
                refine ⟨612984837504665889043229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634626233345775704115277 612984837504665889043229)
                ·
                  refine ⟨229869314064249708391211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612984837504665889043229 229869314064249708391211)
                  ·
                    rfl

theorem cell21_1007255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].length) (baseStart_1007255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007255 prefixEnd_1007255 := by exact prefixLift 1007255
  have htrace : WordTrace (prefixWord ++ tailWord_1007255) baseStart_1007255 baseEnd_1007255 := by
    simpa [prefixWord, tailWord_1007255, baseEnd_1007255] using wordTrace_append hprefix tailTrace_1007255
  have hstable : (prefixWord ++ tailWord_1007255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007255).length < 2 ^ (prefixWord ++ tailWord_1007255).sum := by decide
  have hdescent : baseEnd_1007255 < baseStart_1007255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007286 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1007286 : Nat := 118140960795 + 1007286 * 2 ^ 59
def prefixEnd_1007286 : Nat := 4983230072969 + 3 ^ 40 * 1007286 * 2
def baseEnd_1007286 : Nat := 229876388686600543374481

theorem tailTrace_1007286 : CollatzResearch.WordTrace tailWord_1007286 prefixEnd_1007286 229876388686600543374481 := by
  unfold tailWord_1007286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296171164298895474865107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24492492419188218398561141 2296171164298895474865107)
  ·
    refine ⟨3444256746448343212297661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296171164298895474865107 3444256746448343212297661)
    ·
      refine ⟨1291596279918128704611623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3444256746448343212297661 1291596279918128704611623)
      ·
        refine ⟨1937394419877193056917435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291596279918128704611623 1937394419877193056917435)
        ·
          refine ⟨2906091629815789585376153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937394419877193056917435 2906091629815789585376153)
          ·
            refine ⟨2179568722361842189032115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906091629815789585376153 2179568722361842189032115)
            ·
              refine ⟨3269353083542763283548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179568722361842189032115 3269353083542763283548173)
              ·
                refine ⟨1226007406328536231330565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269353083542763283548173 1226007406328536231330565)
                ·
                  refine ⟨229876388686600543374481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226007406328536231330565 229876388686600543374481)
                  ·
                    rfl

theorem cell21_1007286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1007286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007286 prefixEnd_1007286 := by exact prefixLift 1007286
  have htrace : WordTrace (prefixWord ++ tailWord_1007286) baseStart_1007286 baseEnd_1007286 := by
    simpa [prefixWord, tailWord_1007286, baseEnd_1007286] using wordTrace_append hprefix tailTrace_1007286
  have hstable : (prefixWord ++ tailWord_1007286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007286).length < 2 ^ (prefixWord ++ tailWord_1007286).sum := by decide
  have hdescent : baseEnd_1007286 < baseStart_1007286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007331 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 3]
def baseStart_1007331 : Nat := 118140960795 + 1007331 * 2 ^ 59
def prefixEnd_1007331 : Nat := 4983230072969 + 3 ^ 40 * 1007331 * 2
def baseEnd_1007331 : Nat := 229886658299690465124389

theorem tailTrace_1007331 : CollatzResearch.WordTrace tailWord_1007331 prefixEnd_1007331 229886658299690465124389 := by
  unfold tailWord_1007331
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740379913619300283229847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24493586609079533522153231 36740379913619300283229847)
  ·
    refine ⟨55110569870428950424844771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36740379913619300283229847 55110569870428950424844771)
    ·
      refine ⟨82665854805643425637267157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55110569870428950424844771 82665854805643425637267157)
      ·
        refine ⟨1937480972007267788373449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82665854805643425637267157 1937480972007267788373449)
        ·
          refine ⟨1453110729005450841280087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937480972007267788373449 1453110729005450841280087)
          ·
            refine ⟨2179666093508176261920131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453110729005450841280087 2179666093508176261920131)
            ·
              refine ⟨3269499140262264392880197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179666093508176261920131 3269499140262264392880197)
              ·
                refine ⟨613031088799174573665037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3269499140262264392880197 613031088799174573665037)
                ·
                  refine ⟨229886658299690465124389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613031088799174573665037 229886658299690465124389)
                  ·
                    rfl

theorem cell21_1007331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].length) (baseStart_1007331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007331 prefixEnd_1007331 := by exact prefixLift 1007331
  have htrace : WordTrace (prefixWord ++ tailWord_1007331) baseStart_1007331 baseEnd_1007331 := by
    simpa [prefixWord, tailWord_1007331, baseEnd_1007331] using wordTrace_append hprefix tailTrace_1007331
  have hstable : (prefixWord ++ tailWord_1007331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007331).length < 2 ^ (prefixWord ++ tailWord_1007331).sum := by decide
  have hdescent : baseEnd_1007331 < baseStart_1007331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007418 : List Nat := [3, 1, 1, 1, 5, 2, 1, 7]
def baseStart_1007418 : Nat := 118140960795 + 1007418 * 2 ^ 59
def prefixEnd_1007418 : Nat := 4983230072969 + 3 ^ 40 * 1007418 * 2
def baseEnd_1007418 : Nat := 76635504294999215724737

theorem tailTrace_1007418 : CollatzResearch.WordTrace tailWord_1007418 prefixEnd_1007418 76635504294999215724737 := by
  unfold tailWord_1007418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9185888266076028535411727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24495702042869409427764605 9185888266076028535411727)
  ·
    refine ⟨13778832399114042803117591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9185888266076028535411727 13778832399114042803117591)
    ·
      refine ⟨20668248598671064204676387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13778832399114042803117591 20668248598671064204676387)
      ·
        refine ⟨31002372898006596307014581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668248598671064204676387 31002372898006596307014581)
        ·
          refine ⟨2906472459188118403782617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31002372898006596307014581 2906472459188118403782617)
          ·
            refine ⟨2179854344391088802836963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906472459188118403782617 2179854344391088802836963)
            ·
              refine ⟨3269781516586633204255445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179854344391088802836963 3269781516586633204255445)
              ·
                refine ⟨76635504294999215724737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3269781516586633204255445 76635504294999215724737)
                ·
                  rfl

theorem cell21_1007418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_1007418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007418 prefixEnd_1007418 := by exact prefixLift 1007418
  have htrace : WordTrace (prefixWord ++ tailWord_1007418) baseStart_1007418 baseEnd_1007418 := by
    simpa [prefixWord, tailWord_1007418, baseEnd_1007418] using wordTrace_append hprefix tailTrace_1007418
  have hstable : (prefixWord ++ tailWord_1007418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007418).length < 2 ^ (prefixWord ++ tailWord_1007418).sum := by decide
  have hdescent : baseEnd_1007418 < baseStart_1007418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007573 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1007573 : Nat := 118140960795 + 1007573 * 2 ^ 59
def prefixEnd_1007573 : Nat := 4983230072969 + 3 ^ 40 * 1007573 * 2
def baseEnd_1007573 : Nat := 229941885996751822090561

theorem tailTrace_1007573 : CollatzResearch.WordTrace tailWord_1007573 prefixEnd_1007573 229941885996751822090561 := by
  unfold tailWord_1007573
  simp only [CollatzResearch.WordTrace]
  refine ⟨36749206378742575613539373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24499470919161717075692915 36749206378742575613539373)
  ·
    refine ⟨13780952392028465855077265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36749206378742575613539373 13780952392028465855077265)
    ·
      refine ⟨10335714294021349391307949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13780952392028465855077265 10335714294021349391307949)
      ·
        refine ⟨3875892860258006021740481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10335714294021349391307949 3875892860258006021740481)
        ·
          refine ⟨2906919645193504516305361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875892860258006021740481 2906919645193504516305361)
          ·
            refine ⟨2180189733895128387229021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906919645193504516305361 2180189733895128387229021)
            ·
              refine ⟨817571150210673145210883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2180189733895128387229021 817571150210673145210883)
              ·
                refine ⟨1226356725316009717816325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817571150210673145210883 1226356725316009717816325)
                ·
                  refine ⟨229941885996751822090561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226356725316009717816325 229941885996751822090561)
                  ·
                    rfl

theorem cell21_1007573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1007573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007573 prefixEnd_1007573 := by exact prefixLift 1007573
  have htrace : WordTrace (prefixWord ++ tailWord_1007573) baseStart_1007573 baseEnd_1007573 := by
    simpa [prefixWord, tailWord_1007573, baseEnd_1007573] using wordTrace_append hprefix tailTrace_1007573
  have hstable : (prefixWord ++ tailWord_1007573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007573).length < 2 ^ (prefixWord ++ tailWord_1007573).sum := by decide
  have hdescent : baseEnd_1007573 < baseStart_1007573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007587 : List Nat := [1, 1, 1, 6, 1, 4, 2, 5]
def baseStart_1007587 : Nat := 118140960795 + 1007587 * 2 ^ 59
def prefixEnd_1007587 : Nat := 4983230072969 + 3 ^ 40 * 1007587 * 2
def baseEnd_1007587 : Nat := 76648360329163636285733

theorem tailTrace_1007587 : CollatzResearch.WordTrace tailWord_1007587 prefixEnd_1007587 76648360329163636285733 := by
  unfold tailWord_1007587
  simp only [CollatzResearch.WordTrace]
  refine ⟨36749717000691856004549015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24499811333794570669699343 36749717000691856004549015)
  ·
    refine ⟨55124575501037784006823523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36749717000691856004549015 55124575501037784006823523)
    ·
      refine ⟨82686863251556676010235285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124575501037784006823523 82686863251556676010235285)
      ·
        refine ⟨3875946714916719187979779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82686863251556676010235285 3875946714916719187979779)
        ·
          refine ⟨5813920072375078781969669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875946714916719187979779 5813920072375078781969669)
          ·
            refine ⟨1090110013570327271619313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5813920072375078781969669 1090110013570327271619313)
            ·
              refine ⟨817582510177745453714485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090110013570327271619313 817582510177745453714485)
              ·
                refine ⟨76648360329163636285733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 817582510177745453714485 76648360329163636285733)
                ·
                  rfl

theorem cell21_1007587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].length) (baseStart_1007587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007587 prefixEnd_1007587 := by exact prefixLift 1007587
  have htrace : WordTrace (prefixWord ++ tailWord_1007587) baseStart_1007587 baseEnd_1007587 := by
    simpa [prefixWord, tailWord_1007587, baseEnd_1007587] using wordTrace_append hprefix tailTrace_1007587
  have hstable : (prefixWord ++ tailWord_1007587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007587).length < 2 ^ (prefixWord ++ tailWord_1007587).sum := by decide
  have hdescent : baseEnd_1007587 < baseStart_1007587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007722 : List Nat := [3, 1, 3, 2, 3, 1, 8]
def baseStart_1007722 : Nat := 118140960795 + 1007722 * 2 ^ 59
def prefixEnd_1007722 : Nat := 4983230072969 + 3 ^ 40 * 1007722 * 2
def baseEnd_1007722 : Nat := 25552876647417852678547

theorem tailTrace_1007722 : CollatzResearch.WordTrace tailWord_1007722 prefixEnd_1007722 25552876647417852678547 := by
  unfold tailWord_1007722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188660213800693515178355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24503093903468516040475613 9188660213800693515178355)
  ·
    refine ⟨13782990320701040272767533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9188660213800693515178355 13782990320701040272767533)
    ·
      refine ⟨5168621370262890102287825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13782990320701040272767533 5168621370262890102287825)
      ·
        refine ⟨3876466027697167576715869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5168621370262890102287825 3876466027697167576715869)
        ·
          refine ⟨1453674760386437841268451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3876466027697167576715869 1453674760386437841268451)
          ·
            refine ⟨2180512140579656761902677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453674760386437841268451 2180512140579656761902677)
            ·
              refine ⟨25552876647417852678547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2180512140579656761902677 25552876647417852678547)
              ·
                rfl

theorem cell21_1007722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 8].length) (baseStart_1007722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007722 prefixEnd_1007722 := by exact prefixLift 1007722
  have htrace : WordTrace (prefixWord ++ tailWord_1007722) baseStart_1007722 baseEnd_1007722 := by
    simpa [prefixWord, tailWord_1007722, baseEnd_1007722] using wordTrace_append hprefix tailTrace_1007722
  have hstable : (prefixWord ++ tailWord_1007722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007722).length < 2 ^ (prefixWord ++ tailWord_1007722).sum := by decide
  have hdescent : baseEnd_1007722 < baseStart_1007722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
