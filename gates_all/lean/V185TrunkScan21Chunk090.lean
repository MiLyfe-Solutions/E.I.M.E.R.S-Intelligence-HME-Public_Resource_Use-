import V185TrunkScan21Chunk089

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1091566 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1091566 : Nat := 118140960795 + 1091566 * 2 ^ 59
def prefixEnd_1091566 : Nat := 4983230072969 + 3 ^ 40 * 1091566 * 2
def baseEnd_1091566 : Nat := 249110232935902878535549

theorem tailTrace_1091566 : CollatzResearch.WordTrace tailWord_1091566 prefixEnd_1091566 249110232935902878535549 := by
  unfold tailWord_1091566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976585345431285184485819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26541788508966854317257701 4976585345431285184485819)
  ·
    refine ⟨7464878018146927776728729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976585345431285184485819 7464878018146927776728729)
    ·
      refine ⟨5598658513610195832546547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7464878018146927776728729 5598658513610195832546547)
      ·
        refine ⟨8397987770415293748819821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598658513610195832546547 8397987770415293748819821)
        ·
          refine ⟨3149245413905735155807433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8397987770415293748819821 3149245413905735155807433)
          ·
            refine ⟨2361934060429301366855575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149245413905735155807433 2361934060429301366855575)
            ·
              refine ⟨3542901090643952050283363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361934060429301366855575 3542901090643952050283363)
              ·
                refine ⟨5314351635965928075425045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542901090643952050283363 5314351635965928075425045)
                ·
                  refine ⟨249110232935902878535549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5314351635965928075425045 249110232935902878535549)
                  ·
                    rfl

theorem cell21_1091566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1091566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091566 prefixEnd_1091566 := by exact prefixLift 1091566
  have htrace : WordTrace (prefixWord ++ tailWord_1091566) baseStart_1091566 baseEnd_1091566 := by
    simpa [prefixWord, tailWord_1091566, baseEnd_1091566] using wordTrace_append hprefix tailTrace_1091566
  have hstable : (prefixWord ++ tailWord_1091566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091566).length < 2 ^ (prefixWord ++ tailWord_1091566).sum := by decide
  have hdescent : baseEnd_1091566 < baseStart_1091566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091611 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 3]
def baseStart_1091611 : Nat := 118140960795 + 1091611 * 2 ^ 59
def prefixEnd_1091611 : Nat := 4983230072969 + 3 ^ 40 * 1091611 * 2
def baseEnd_1091611 : Nat := 249120502548992800285457

theorem tailTrace_1091611 : CollatzResearch.WordTrace tailWord_1091611 prefixEnd_1091611 249120502548992800285457 := by
  unfold tailWord_1091611
  simp only [CollatzResearch.WordTrace]
  refine ⟨39814324048287254161274687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26542882698858169440849791 39814324048287254161274687)
  ·
    refine ⟨59721486072430881241912031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39814324048287254161274687 59721486072430881241912031)
    ·
      refine ⟨89582229108646321862868047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59721486072430881241912031 89582229108646321862868047)
      ·
        refine ⟨134373343662969482794302071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89582229108646321862868047 134373343662969482794302071)
        ·
          refine ⟨201560015494454224191453107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134373343662969482794302071 201560015494454224191453107)
          ·
            refine ⟨302340023241681336287179661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201560015494454224191453107 302340023241681336287179661)
            ·
              refine ⟨113377508715630501107692373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302340023241681336287179661 113377508715630501107692373)
              ·
                refine ⟨664321340130647467427885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 113377508715630501107692373 664321340130647467427885)
                ·
                  refine ⟨249120502548992800285457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664321340130647467427885 249120502548992800285457)
                  ·
                    rfl

theorem cell21_1091611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].length) (baseStart_1091611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091611 prefixEnd_1091611 := by exact prefixLift 1091611
  have htrace : WordTrace (prefixWord ++ tailWord_1091611) baseStart_1091611 baseEnd_1091611 := by
    simpa [prefixWord, tailWord_1091611, baseEnd_1091611] using wordTrace_append hprefix tailTrace_1091611
  have hstable : (prefixWord ++ tailWord_1091611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091611).length < 2 ^ (prefixWord ++ tailWord_1091611).sum := by decide
  have hdescent : baseEnd_1091611 < baseStart_1091611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091639 : List Nat := [1, 1, 3, 1, 2, 2, 3, 8]
def baseStart_1091639 : Nat := 118140960795 + 1091639 * 2 ^ 59
def prefixEnd_1091639 : Nat := 4983230072969 + 3 ^ 40 * 1091639 * 2
def baseEnd_1091639 : Nat := 83042297510156991272911

theorem tailTrace_1091639 : CollatzResearch.WordTrace tailWord_1091639 prefixEnd_1091639 83042297510156991272911 := by
  unfold tailWord_1091639
  simp only [CollatzResearch.WordTrace]
  refine ⟨39815345292185814943293971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26543563528123876628862647 39815345292185814943293971)
  ·
    refine ⟨59723017938278722414940957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39815345292185814943293971 59723017938278722414940957)
    ·
      refine ⟨22396131726854520905602859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59723017938278722414940957 22396131726854520905602859)
      ·
        refine ⟨33594197590281781358404289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22396131726854520905602859 33594197590281781358404289)
        ·
          refine ⟨25195648192711336018803217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33594197590281781358404289 25195648192711336018803217)
          ·
            refine ⟨18896736144533502014102413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25195648192711336018803217 18896736144533502014102413)
            ·
              refine ⟨7086276054200063255288405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18896736144533502014102413 7086276054200063255288405)
              ·
                refine ⟨83042297510156991272911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7086276054200063255288405 83042297510156991272911)
                ·
                  rfl

theorem cell21_1091639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_1091639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091639 prefixEnd_1091639 := by exact prefixLift 1091639
  have htrace : WordTrace (prefixWord ++ tailWord_1091639) baseStart_1091639 baseEnd_1091639 := by
    simpa [prefixWord, tailWord_1091639, baseEnd_1091639] using wordTrace_append hprefix tailTrace_1091639
  have hstable : (prefixWord ++ tailWord_1091639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091639).length < 2 ^ (prefixWord ++ tailWord_1091639).sum := by decide
  have hdescent : baseEnd_1091639 < baseStart_1091639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091690 : List Nat := [3, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1091690 : Nat := 118140960795 + 1091690 * 2 ^ 59
def prefixEnd_1091690 : Nat := 4983230072969 + 3 ^ 40 * 1091690 * 2
def baseEnd_1091690 : Nat := 83046177141768739489543

theorem tailTrace_1091690 : CollatzResearch.WordTrace tailWord_1091690 prefixEnd_1091690 83046177141768739489543 := by
  unfold tailWord_1091690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954301353750262663350131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26544803610000700435600349 9954301353750262663350131)
  ·
    refine ⟨14931452030625393995025197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9954301353750262663350131 14931452030625393995025197)
    ·
      refine ⟨5599294511484522748134449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14931452030625393995025197 5599294511484522748134449)
      ·
        refine ⟨4199470883613392061100837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5599294511484522748134449 4199470883613392061100837)
        ·
          refine ⟨787400790677511011456407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4199470883613392061100837 787400790677511011456407)
          ·
            refine ⟨1181101186016266517184611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787400790677511011456407 1181101186016266517184611)
            ·
              refine ⟨1771651779024399775776917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181101186016266517184611 1771651779024399775776917)
              ·
                refine ⟨83046177141768739489543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771651779024399775776917 83046177141768739489543)
                ·
                  rfl

theorem cell21_1091690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1091690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091690 prefixEnd_1091690 := by exact prefixLift 1091690
  have htrace : WordTrace (prefixWord ++ tailWord_1091690) baseStart_1091690 baseEnd_1091690 := by
    simpa [prefixWord, tailWord_1091690, baseEnd_1091690] using wordTrace_append hprefix tailTrace_1091690
  have hstable : (prefixWord ++ tailWord_1091690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091690).length < 2 ^ (prefixWord ++ tailWord_1091690).sum := by decide
  have hdescent : baseEnd_1091690 < baseStart_1091690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091735 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_1091735 : Nat := 118140960795 + 1091735 * 2 ^ 59
def prefixEnd_1091735 : Nat := 4983230072969 + 3 ^ 40 * 1091735 * 2
def baseEnd_1091735 : Nat := 249148801038396140218537

theorem tailTrace_1091735 : CollatzResearch.WordTrace tailWord_1091735 prefixEnd_1091735 249148801038396140218537 := by
  unfold tailWord_1091735
  simp only [CollatzResearch.WordTrace]
  refine ⟨39818846699838023338788659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26545897799892015559192439 39818846699838023338788659)
  ·
    refine ⟨59728270049757035008182989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39818846699838023338788659 59728270049757035008182989)
    ·
      refine ⟨22398101268658888128068621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59728270049757035008182989 22398101268658888128068621)
      ·
        refine ⟨8399287975747083048025733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22398101268658888128068621 8399287975747083048025733)
        ·
          refine ⟨1574866495452578071504825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8399287975747083048025733 1574866495452578071504825)
          ·
            refine ⟨1181149871589433553628619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574866495452578071504825 1181149871589433553628619)
            ·
              refine ⟨1771724807384150330442929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181149871589433553628619 1771724807384150330442929)
              ·
                refine ⟨1328793605538112747832197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771724807384150330442929 1328793605538112747832197)
                ·
                  refine ⟨249148801038396140218537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328793605538112747832197 249148801038396140218537)
                  ·
                    rfl

theorem cell21_1091735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_1091735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091735 prefixEnd_1091735 := by exact prefixLift 1091735
  have htrace : WordTrace (prefixWord ++ tailWord_1091735) baseStart_1091735 baseEnd_1091735 := by
    simpa [prefixWord, tailWord_1091735, baseEnd_1091735] using wordTrace_append hprefix tailTrace_1091735
  have hstable : (prefixWord ++ tailWord_1091735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091735).length < 2 ^ (prefixWord ++ tailWord_1091735).sum := by decide
  have hdescent : baseEnd_1091735 < baseStart_1091735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091760 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1091760 : Nat := 118140960795 + 1091760 * 2 ^ 59
def prefixEnd_1091760 : Nat := 4983230072969 + 3 ^ 40 * 1091760 * 2
def baseEnd_1091760 : Nat := 249154506379001652301819

theorem tailTrace_1091760 : CollatzResearch.WordTrace tailWord_1091760 prefixEnd_1091760 249154506379001652301819 := by
  unfold tailWord_1091760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19909879262373726304224367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26546505683164968405632489 19909879262373726304224367)
  ·
    refine ⟨29864818893560589456336551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19909879262373726304224367 29864818893560589456336551)
    ·
      refine ⟨44797228340340884184504827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29864818893560589456336551 44797228340340884184504827)
      ·
        refine ⟨67195842510511326276757241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44797228340340884184504827 67195842510511326276757241)
        ·
          refine ⟨50396881882883494707567931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67195842510511326276757241 50396881882883494707567931)
          ·
            refine ⟨75595322824325242061351897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50396881882883494707567931 75595322824325242061351897)
            ·
              refine ⟨56696492118243931546013923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75595322824325242061351897 56696492118243931546013923)
              ·
                refine ⟨85044738177365897319020885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56696492118243931546013923 85044738177365897319020885)
                ·
                  refine ⟨249154506379001652301819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85044738177365897319020885 249154506379001652301819)
                  ·
                    rfl

theorem cell21_1091760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1091760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091760 prefixEnd_1091760 := by exact prefixLift 1091760
  have htrace : WordTrace (prefixWord ++ tailWord_1091760) baseStart_1091760 baseEnd_1091760 := by
    simpa [prefixWord, tailWord_1091760, baseEnd_1091760] using wordTrace_append hprefix tailTrace_1091760
  have hstable : (prefixWord ++ tailWord_1091760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091760).length < 2 ^ (prefixWord ++ tailWord_1091760).sum := by decide
  have hdescent : baseEnd_1091760 < baseStart_1091760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091797 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1091797 : Nat := 118140960795 + 1091797 * 2 ^ 59
def prefixEnd_1091797 : Nat := 4983230072969 + 3 ^ 40 * 1091797 * 2
def baseEnd_1091797 : Nat := 249162950283097810185077

theorem tailTrace_1091797 : CollatzResearch.WordTrace tailWord_1091797 prefixEnd_1091797 249162950283097810185077 := by
  unfold tailWord_1091797
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821108025613407927545645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547405350408938618363763 39821108025613407927545645)
  ·
    refine ⟨14932915509605027972829617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39821108025613407927545645 14932915509605027972829617)
    ·
      refine ⟨11199686632203770979622213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14932915509605027972829617 11199686632203770979622213)
      ·
        refine ⟨2099941243538207058679165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11199686632203770979622213 2099941243538207058679165)
        ·
          refine ⟨787477966326827647004687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2099941243538207058679165 787477966326827647004687)
          ·
            refine ⟨1181216949490241470507031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787477966326827647004687 1181216949490241470507031)
            ·
              refine ⟨1771825424235362205760547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181216949490241470507031 1771825424235362205760547)
              ·
                refine ⟨2657738136353043308640821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771825424235362205760547 2657738136353043308640821)
                ·
                  refine ⟨249162950283097810185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2657738136353043308640821 249162950283097810185077)
                  ·
                    rfl

theorem cell21_1091797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1091797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091797 prefixEnd_1091797 := by exact prefixLift 1091797
  have htrace : WordTrace (prefixWord ++ tailWord_1091797) baseStart_1091797 baseEnd_1091797 := by
    simpa [prefixWord, tailWord_1091797, baseEnd_1091797] using wordTrace_append hprefix tailTrace_1091797
  have hstable : (prefixWord ++ tailWord_1091797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091797).length < 2 ^ (prefixWord ++ tailWord_1091797).sum := by decide
  have hdescent : baseEnd_1091797 < baseStart_1091797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091811 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_1091811 : Nat := 118140960795 + 1091811 * 2 ^ 59
def prefixEnd_1091811 : Nat := 4983230072969 + 3 ^ 40 * 1091811 * 2
def baseEnd_1091811 : Nat := 249166145273836896951715

theorem tailTrace_1091811 : CollatzResearch.WordTrace tailWord_1091811 prefixEnd_1091811 249166145273836896951715 := by
  unfold tailWord_1091811
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821618647562688318555287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547745765041792212370191 39821618647562688318555287)
  ·
    refine ⟨59732427971344032477832931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39821618647562688318555287 59732427971344032477832931)
    ·
      refine ⟨89598641957016048716749397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59732427971344032477832931 89598641957016048716749397)
      ·
        refine ⟨1049984085433781820899407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 89598641957016048716749397 1049984085433781820899407)
        ·
          refine ⟨1574976128150672731349111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049984085433781820899407 1574976128150672731349111)
          ·
            refine ⟨2362464192226009097023667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574976128150672731349111 2362464192226009097023667)
            ·
              refine ⟨3543696288339013645535501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362464192226009097023667 3543696288339013645535501)
              ·
                refine ⟨1328886108127130117075813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3543696288339013645535501 1328886108127130117075813)
                ·
                  refine ⟨249166145273836896951715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328886108127130117075813 249166145273836896951715)
                  ·
                    rfl

theorem cell21_1091811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_1091811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091811 prefixEnd_1091811 := by exact prefixLift 1091811
  have htrace : WordTrace (prefixWord ++ tailWord_1091811) baseStart_1091811 baseEnd_1091811 := by
    simpa [prefixWord, tailWord_1091811, baseEnd_1091811] using wordTrace_append hprefix tailTrace_1091811
  have hstable : (prefixWord ++ tailWord_1091811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091811).length < 2 ^ (prefixWord ++ tailWord_1091811).sum := by decide
  have hdescent : baseEnd_1091811 < baseStart_1091811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091822 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1091822 : Nat := 118140960795 + 1091822 * 2 ^ 59
def prefixEnd_1091822 : Nat := 4983230072969 + 3 ^ 40 * 1091822 * 2
def baseEnd_1091822 : Nat := 249168655623703322268359

theorem tailTrace_1091822 : CollatzResearch.WordTrace tailWord_1091822 prefixEnd_1091822 249168655623703322268359 := by
  unfold tailWord_1091822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977752481315354649650715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26548013233681891464803813 4977752481315354649650715)
  ·
    refine ⟨7466628721973031974476073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4977752481315354649650715 7466628721973031974476073)
    ·
      refine ⟨5599971541479773980857055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7466628721973031974476073 5599971541479773980857055)
      ·
        refine ⟨8399957312219660971285583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599971541479773980857055 8399957312219660971285583)
        ·
          refine ⟨12599935968329491456928375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399957312219660971285583 12599935968329491456928375)
          ·
            refine ⟨18899903952494237185392563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599935968329491456928375 18899903952494237185392563)
            ·
              refine ⟨28349855928741355778088845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899903952494237185392563 28349855928741355778088845)
              ·
                refine ⟨10631195973278008416783317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28349855928741355778088845 10631195973278008416783317)
                ·
                  refine ⟨249168655623703322268359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10631195973278008416783317 249168655623703322268359)
                  ·
                    rfl

theorem cell21_1091822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1091822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091822 prefixEnd_1091822 := by exact prefixLift 1091822
  have htrace : WordTrace (prefixWord ++ tailWord_1091822) baseStart_1091822 baseEnd_1091822 := by
    simpa [prefixWord, tailWord_1091822, baseEnd_1091822] using wordTrace_append hprefix tailTrace_1091822
  have hstable : (prefixWord ++ tailWord_1091822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091822).length < 2 ^ (prefixWord ++ tailWord_1091822).sum := by decide
  have hdescent : baseEnd_1091822 < baseStart_1091822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091839 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 3]
def baseStart_1091839 : Nat := 118140960795 + 1091839 * 2 ^ 59
def prefixEnd_1091839 : Nat := 4983230072969 + 3 ^ 40 * 1091839 * 2
def baseEnd_1091839 : Nat := 249172535255315070484991

theorem tailTrace_1091839 : CollatzResearch.WordTrace tailWord_1091839 prefixEnd_1091839 249172535255315070484991 := by
  unfold tailWord_1091839
  simp only [CollatzResearch.WordTrace]
  refine ⟨39822639891461249100574571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26548426594307499400383047 39822639891461249100574571)
  ·
    refine ⟨59733959837191873650861857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39822639891461249100574571 59733959837191873650861857)
    ·
      refine ⟨44800469877893905238146393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59733959837191873650861857 44800469877893905238146393)
      ·
        refine ⟨33600352408420428928609795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44800469877893905238146393 33600352408420428928609795)
        ·
          refine ⟨50400528612630643392914693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33600352408420428928609795 50400528612630643392914693)
          ·
            refine ⟨9450099114868245636171505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50400528612630643392914693 9450099114868245636171505)
            ·
              refine ⟨7087574336151184227128629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9450099114868245636171505 7087574336151184227128629)
              ·
                refine ⟨664460094014173521293309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7087574336151184227128629 664460094014173521293309)
                ·
                  refine ⟨249172535255315070484991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664460094014173521293309 249172535255315070484991)
                  ·
                    rfl

theorem cell21_1091839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].length) (baseStart_1091839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091839 prefixEnd_1091839 := by exact prefixLift 1091839
  have htrace : WordTrace (prefixWord ++ tailWord_1091839) baseStart_1091839 baseEnd_1091839 := by
    simpa [prefixWord, tailWord_1091839, baseEnd_1091839] using wordTrace_append hprefix tailTrace_1091839
  have hstable : (prefixWord ++ tailWord_1091839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091839).length < 2 ^ (prefixWord ++ tailWord_1091839).sum := by decide
  have hdescent : baseEnd_1091839 < baseStart_1091839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091867 : List Nat := [1, 1, 1, 1, 1, 1, 9, 6]
def baseStart_1091867 : Nat := 118140960795 + 1091867 * 2 ^ 59
def prefixEnd_1091867 : Nat := 4983230072969 + 3 ^ 40 * 1091867 * 2
def baseEnd_1091867 : Nat := 83059641745597748006089

theorem tailTrace_1091867 : CollatzResearch.WordTrace tailWord_1091867 prefixEnd_1091867 83059641745597748006089 := by
  unfold tailWord_1091867
  simp only [CollatzResearch.WordTrace]
  refine ⟨39823661135359809882593855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26549107423573206588395903 39823661135359809882593855)
  ·
    refine ⟨59735491703039714823890783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39823661135359809882593855 59735491703039714823890783)
    ·
      refine ⟨89603237554559572235836175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59735491703039714823890783 89603237554559572235836175)
      ·
        refine ⟨134404856331839358353754263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89603237554559572235836175 134404856331839358353754263)
        ·
          refine ⟨201607284497759037530631395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134404856331839358353754263 201607284497759037530631395)
          ·
            refine ⟨302410926746638556295947093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201607284497759037530631395 302410926746638556295947093)
            ·
              refine ⟨1771939023906085290796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 302410926746638556295947093 1771939023906085290796565)
              ·
                refine ⟨83059641745597748006089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771939023906085290796565 83059641745597748006089)
                ·
                  rfl

theorem cell21_1091867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_1091867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091867 prefixEnd_1091867 := by exact prefixLift 1091867
  have htrace : WordTrace (prefixWord ++ tailWord_1091867) baseStart_1091867 baseEnd_1091867 := by
    simpa [prefixWord, tailWord_1091867, baseEnd_1091867] using wordTrace_append hprefix tailTrace_1091867
  have hstable : (prefixWord ++ tailWord_1091867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091867).length < 2 ^ (prefixWord ++ tailWord_1091867).sum := by decide
  have hdescent : baseEnd_1091867 < baseStart_1091867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092025 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 3]
def baseStart_1092025 : Nat := 118140960795 + 1092025 * 2 ^ 59
def prefixEnd_1092025 : Nat := 4983230072969 + 3 ^ 40 * 1092025 * 2
def baseEnd_1092025 : Nat := 249214982989420080384611

theorem tailTrace_1092025 : CollatzResearch.WordTrace tailWord_1092025 prefixEnd_1092025 249214982989420080384611 := by
  unfold tailWord_1092025
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829423868787402866845529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26552949245858268577897019 39829423868787402866845529)
  ·
    refine ⟨29872067901590552150134147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39829423868787402866845529 29872067901590552150134147)
    ·
      refine ⟨44808101852385828225201221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29872067901590552150134147 44808101852385828225201221)
      ·
        refine ⟨8401519097322342792225229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44808101852385828225201221 8401519097322342792225229)
        ·
          refine ⟨3150569661495878547084461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8401519097322342792225229 3150569661495878547084461)
          ·
            refine ⟨1181463623060954455156673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3150569661495878547084461 1181463623060954455156673)
            ·
              refine ⟨886097717295715841367505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181463623060954455156673 886097717295715841367505)
              ·
                refine ⟨664573287971786881025629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886097717295715841367505 664573287971786881025629)
                ·
                  refine ⟨249214982989420080384611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664573287971786881025629 249214982989420080384611)
                  ·
                    rfl

theorem cell21_1092025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_1092025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092025 prefixEnd_1092025 := by exact prefixLift 1092025
  have htrace : WordTrace (prefixWord ++ tailWord_1092025) baseStart_1092025 baseEnd_1092025 := by
    simpa [prefixWord, tailWord_1092025, baseEnd_1092025] using wordTrace_append hprefix tailTrace_1092025
  have hstable : (prefixWord ++ tailWord_1092025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092025).length < 2 ^ (prefixWord ++ tailWord_1092025).sum := by decide
  have hdescent : baseEnd_1092025 < baseStart_1092025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092064 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1092064 : Nat := 118140960795 + 1092064 * 2 ^ 59
def prefixEnd_1092064 : Nat := 4983230072969 + 3 ^ 40 * 1092064 * 2
def baseEnd_1092064 : Nat := 249223883320764679234531

theorem tailTrace_1092064 : CollatzResearch.WordTrace tailWord_1092064 prefixEnd_1092064 249223883320764679234531 := by
  unfold tailWord_1092064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19915423157823056263757623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26553897543764075018343497 19915423157823056263757623)
  ·
    refine ⟨29873134736734584395636435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19915423157823056263757623 29873134736734584395636435)
    ·
      refine ⟨44809702105101876593454653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29873134736734584395636435 44809702105101876593454653)
      ·
        refine ⟨16803638289413203722545495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44809702105101876593454653 16803638289413203722545495)
        ·
          refine ⟨25205457434119805583818243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16803638289413203722545495 25205457434119805583818243)
          ·
            refine ⟨37808186151179708375727365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25205457434119805583818243 37808186151179708375727365)
            ·
              refine ⟨7089034903346195320448881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37808186151179708375727365 7089034903346195320448881)
              ·
                refine ⟨5316776177509646490336661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089034903346195320448881 5316776177509646490336661)
                ·
                  refine ⟨249223883320764679234531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5316776177509646490336661 249223883320764679234531)
                  ·
                    rfl

theorem cell21_1092064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1092064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092064 prefixEnd_1092064 := by exact prefixLift 1092064
  have htrace : WordTrace (prefixWord ++ tailWord_1092064) baseStart_1092064 baseEnd_1092064 := by
    simpa [prefixWord, tailWord_1092064, baseEnd_1092064] using wordTrace_append hprefix tailTrace_1092064
  have hstable : (prefixWord ++ tailWord_1092064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092064).length < 2 ^ (prefixWord ++ tailWord_1092064).sum := by decide
  have hdescent : baseEnd_1092064 < baseStart_1092064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092188 : List Nat := [2, 2, 4, 1, 4, 8]
def baseStart_1092188 : Nat := 118140960795 + 1092188 * 2 ^ 59
def prefixEnd_1092188 : Nat := 4983230072969 + 3 ^ 40 * 1092188 * 2
def baseEnd_1092188 : Nat := 9231562289265482191393

theorem tailTrace_1092188 : CollatzResearch.WordTrace tailWord_1092188 prefixEnd_1092188 9231562289265482191393 := by
  unfold tailWord_1092188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917684483598440852514609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26556912644797921136686145 19917684483598440852514609)
  ·
    refine ⟨14938263362698830639385957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19917684483598440852514609 14938263362698830639385957)
    ·
      refine ⟨2800924380506030744884867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14938263362698830639385957 2800924380506030744884867)
      ·
        refine ⟨4201386570759046117327301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800924380506030744884867 4201386570759046117327301)
        ·
          refine ⟨787759982017321146998869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4201386570759046117327301 787759982017321146998869)
          ·
            refine ⟨9231562289265482191393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 787759982017321146998869 9231562289265482191393)
            ·
              rfl

theorem cell21_1092188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 8].length) (baseStart_1092188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092188 prefixEnd_1092188 := by exact prefixLift 1092188
  have htrace : WordTrace (prefixWord ++ tailWord_1092188) baseStart_1092188 baseEnd_1092188 := by
    simpa [prefixWord, tailWord_1092188, baseEnd_1092188] using wordTrace_append hprefix tailTrace_1092188
  have hstable : (prefixWord ++ tailWord_1092188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092188).length < 2 ^ (prefixWord ++ tailWord_1092188).sum := by decide
  have hdescent : baseEnd_1092188 < baseStart_1092188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092202 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1092202 : Nat := 118140960795 + 1092202 * 2 ^ 59
def prefixEnd_1092202 : Nat := 4983230072969 + 3 ^ 40 * 1092202 * 2
def baseEnd_1092202 : Nat := 249255376800907105934249

theorem tailTrace_1092202 : CollatzResearch.WordTrace tailWord_1092202 prefixEnd_1092202 249255376800907105934249 := by
  unfold tailWord_1092202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958969897286540524009715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26557253059430774730692573 9958969897286540524009715)
  ·
    refine ⟨14938454845929810786014573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9958969897286540524009715 14938454845929810786014573)
    ·
      refine ⟨5601920567223679044755465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14938454845929810786014573 5601920567223679044755465)
      ·
        refine ⟨4201440425417759283566599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5601920567223679044755465 4201440425417759283566599)
        ·
          refine ⟨6302160638126638925349899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201440425417759283566599 6302160638126638925349899)
          ·
            refine ⟨9453240957189958388024849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302160638126638925349899 9453240957189958388024849)
            ·
              refine ⟨7089930717892468791018637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9453240957189958388024849 7089930717892468791018637)
              ·
                refine ⟨2658724019209675796631989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7089930717892468791018637 2658724019209675796631989)
                ·
                  refine ⟨249255376800907105934249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658724019209675796631989 249255376800907105934249)
                  ·
                    rfl

theorem cell21_1092202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1092202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092202 prefixEnd_1092202 := by exact prefixLift 1092202
  have htrace : WordTrace (prefixWord ++ tailWord_1092202) baseStart_1092202 baseEnd_1092202 := by
    simpa [prefixWord, tailWord_1092202, baseEnd_1092202] using wordTrace_append hprefix tailTrace_1092202
  have hstable : (prefixWord ++ tailWord_1092202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092202).length < 2 ^ (prefixWord ++ tailWord_1092202).sum := by decide
  have hdescent : baseEnd_1092202 < baseStart_1092202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092250 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1092250 : Nat := 118140960795 + 1092250 * 2 ^ 59
def prefixEnd_1092250 : Nat := 4983230072969 + 3 ^ 40 * 1092250 * 2
def baseEnd_1092250 : Nat := 249266331054869689134151

theorem tailTrace_1092250 : CollatzResearch.WordTrace tailWord_1092250 prefixEnd_1092250 249266331054869689134151 := by
  unfold tailWord_1092250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959407573243066573446551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26558420195314844195857469 9959407573243066573446551)
  ·
    refine ⟨14939111359864599860169827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959407573243066573446551 14939111359864599860169827)
    ·
      refine ⟨22408667039796899790254741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939111359864599860169827 22408667039796899790254741)
      ·
        refine ⟨1050406267490479677668191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22408667039796899790254741 1050406267490479677668191)
        ·
          refine ⟨1575609401235719516502287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050406267490479677668191 1575609401235719516502287)
          ·
            refine ⟨2363414101853579274753431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575609401235719516502287 2363414101853579274753431)
            ·
              refine ⟨3545121152780368912130147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363414101853579274753431 3545121152780368912130147)
              ·
                refine ⟨5317681729170553368195221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545121152780368912130147 5317681729170553368195221)
                ·
                  refine ⟨249266331054869689134151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5317681729170553368195221 249266331054869689134151)
                  ·
                    rfl

theorem cell21_1092250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1092250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092250 prefixEnd_1092250 := by exact prefixLift 1092250
  have htrace : WordTrace (prefixWord ++ tailWord_1092250) baseStart_1092250 baseEnd_1092250 := by
    simpa [prefixWord, tailWord_1092250, baseEnd_1092250] using wordTrace_append hprefix tailTrace_1092250
  have hstable : (prefixWord ++ tailWord_1092250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092250).length < 2 ^ (prefixWord ++ tailWord_1092250).sum := by decide
  have hdescent : baseEnd_1092250 < baseStart_1092250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092312 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_1092312 : Nat := 118140960795 + 1092312 * 2 ^ 59
def prefixEnd_1092312 : Nat := 4983230072969 + 3 ^ 40 * 1092312 * 2
def baseEnd_1092312 : Nat := 249280480299571359100691

theorem tailTrace_1092312 : CollatzResearch.WordTrace tailWord_1092312 prefixEnd_1092312 249280480299571359100691 := by
  unfold tailWord_1092312
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919945809373825441271595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26559927745831767255028793 19919945809373825441271595)
  ·
    refine ⟨29879918714060738161907393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19919945809373825441271595 29879918714060738161907393)
    ·
      refine ⟨22409939035545553621430545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29879918714060738161907393 22409939035545553621430545)
      ·
        refine ⟨16807454276659165216072909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22409939035545553621430545 16807454276659165216072909)
        ·
          refine ⟨6302795353747186956027341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16807454276659165216072909 6302795353747186956027341)
          ·
            refine ⟨2363548257655195108510253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6302795353747186956027341 2363548257655195108510253)
            ·
              refine ⟨886330596620698165691345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2363548257655195108510253 886330596620698165691345)
              ·
                refine ⟨664747947465523624268509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886330596620698165691345 664747947465523624268509)
                ·
                  refine ⟨249280480299571359100691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664747947465523624268509 249280480299571359100691)
                  ·
                    rfl

theorem cell21_1092312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_1092312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092312 prefixEnd_1092312 := by exact prefixLift 1092312
  have htrace : WordTrace (prefixWord ++ tailWord_1092312) baseStart_1092312 baseEnd_1092312 := by
    simpa [prefixWord, tailWord_1092312, baseEnd_1092312] using wordTrace_append hprefix tailTrace_1092312
  have hstable : (prefixWord ++ tailWord_1092312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092312).length < 2 ^ (prefixWord ++ tailWord_1092312).sum := by decide
  have hdescent : baseEnd_1092312 < baseStart_1092312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092323 : List Nat := [1, 1, 1, 7, 1, 1, 1, 8]
def baseStart_1092323 : Nat := 118140960795 + 1092323 * 2 ^ 59
def prefixEnd_1092323 : Nat := 4983230072969 + 3 ^ 40 * 1092323 * 2
def baseEnd_1092323 : Nat := 83094330216479261472445

theorem tailTrace_1092323 : CollatzResearch.WordTrace tailWord_1092323 prefixEnd_1092323 83094330216479261472445 := by
  unfold tailWord_1092323
  simp only [CollatzResearch.WordTrace]
  refine ⟨39840292821707799761193623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26560195214471866507462415 39840292821707799761193623)
  ·
    refine ⟨59760439232561699641790435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39840292821707799761193623 59760439232561699641790435)
    ·
      refine ⟨89640658848842549462685653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59760439232561699641790435 89640658848842549462685653)
      ·
        refine ⟨2100952941769747253031695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 89640658848842549462685653 2100952941769747253031695)
        ·
          refine ⟨3151429412654620879547543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100952941769747253031695 3151429412654620879547543)
          ·
            refine ⟨4727144118981931319321315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151429412654620879547543 4727144118981931319321315)
            ·
              refine ⟨7090716178472896978981973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727144118981931319321315 7090716178472896978981973)
              ·
                refine ⟨83094330216479261472445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7090716178472896978981973 83094330216479261472445)
                ·
                  rfl

theorem cell21_1092323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_1092323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092323 prefixEnd_1092323 := by exact prefixLift 1092323
  have htrace : WordTrace (prefixWord ++ tailWord_1092323) baseStart_1092323 baseEnd_1092323 := by
    simpa [prefixWord, tailWord_1092323, baseEnd_1092323] using wordTrace_append hprefix tailTrace_1092323
  have hstable : (prefixWord ++ tailWord_1092323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092323).length < 2 ^ (prefixWord ++ tailWord_1092323).sum := by decide
  have hdescent : baseEnd_1092323 < baseStart_1092323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092337 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_1092337 : Nat := 118140960795 + 1092337 * 2 ^ 59
def prefixEnd_1092337 : Nat := 4983230072969 + 3 ^ 40 * 1092337 * 2
def baseEnd_1092337 : Nat := 249286185640176871183973

theorem tailTrace_1092337 : CollatzResearch.WordTrace tailWord_1092337 prefixEnd_1092337 249286185640176871183973 := by
  unfold tailWord_1092337
  simp only [CollatzResearch.WordTrace]
  refine ⟨39840803443657080152203265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26560535629104720101468843 39840803443657080152203265)
  ·
    refine ⟨29880602582742810114152449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39840803443657080152203265 29880602582742810114152449)
    ·
      refine ⟨22410451937057107585614337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29880602582742810114152449 22410451937057107585614337)
      ·
        refine ⟨16807838952792830689210753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22410451937057107585614337 16807838952792830689210753)
        ·
          refine ⟨12605879214594623016908065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16807838952792830689210753 12605879214594623016908065)
          ·
            refine ⟨9454409410945967262681049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605879214594623016908065 9454409410945967262681049)
            ·
              refine ⟨7090807058209475447010787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454409410945967262681049 7090807058209475447010787)
              ·
                refine ⟨10636210587314213170516181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090807058209475447010787 10636210587314213170516181)
                ·
                  refine ⟨249286185640176871183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10636210587314213170516181 249286185640176871183973)
                  ·
                    rfl

theorem cell21_1092337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_1092337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092337 prefixEnd_1092337 := by exact prefixLift 1092337
  have htrace : WordTrace (prefixWord ++ tailWord_1092337) baseStart_1092337 baseEnd_1092337 := by
    simpa [prefixWord, tailWord_1092337, baseEnd_1092337] using wordTrace_append hprefix tailTrace_1092337
  have hstable : (prefixWord ++ tailWord_1092337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092337).length < 2 ^ (prefixWord ++ tailWord_1092337).sum := by decide
  have hdescent : baseEnd_1092337 < baseStart_1092337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092450 : List Nat := [3, 3, 2, 1, 4, 1, 2, 5]
def baseStart_1092450 : Nat := 118140960795 + 1092450 * 2 ^ 59
def prefixEnd_1092450 : Nat := 4983230072969 + 3 ^ 40 * 1092450 * 2
def baseEnd_1092450 : Nat := 83103991259904595266803

theorem tailTrace_1092450 : CollatzResearch.WordTrace tailWord_1092450 prefixEnd_1092450 83103991259904595266803 := by
  unfold tailWord_1092450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961231223061925112766701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26563283261498466967377869 9961231223061925112766701)
  ·
    refine ⟨3735461708648221917287513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9961231223061925112766701 3735461708648221917287513)
    ·
      refine ⟨2801596281486166437965635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3735461708648221917287513 2801596281486166437965635)
      ·
        refine ⟨4202394422229249656948453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801596281486166437965635 4202394422229249656948453)
        ·
          refine ⟨787948954167984310677835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4202394422229249656948453 787948954167984310677835)
          ·
            refine ⟨1181923431251976466016753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787948954167984310677835 1181923431251976466016753)
            ·
              refine ⟨886442573438982349512565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181923431251976466016753 886442573438982349512565)
              ·
                refine ⟨83103991259904595266803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 886442573438982349512565 83103991259904595266803)
                ·
                  rfl

theorem cell21_1092450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_1092450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092450 prefixEnd_1092450 := by exact prefixLift 1092450
  have htrace : WordTrace (prefixWord ++ tailWord_1092450) baseStart_1092450 baseEnd_1092450 := by
    simpa [prefixWord, tailWord_1092450, baseEnd_1092450] using wordTrace_append hprefix tailTrace_1092450
  have hstable : (prefixWord ++ tailWord_1092450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092450).length < 2 ^ (prefixWord ++ tailWord_1092450).sum := by decide
  have hdescent : baseEnd_1092450 < baseStart_1092450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092537 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1092537 : Nat := 118140960795 + 1092537 * 2 ^ 59
def prefixEnd_1092537 : Nat := 4983230072969 + 3 ^ 40 * 1092537 * 2
def baseEnd_1092537 : Nat := 249331828365020967850231

theorem tailTrace_1092537 : CollatzResearch.WordTrace tailWord_1092537 prefixEnd_1092537 249331828365020967850231 := by
  unfold tailWord_1092537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39848098042932514309483865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26565398695288342872989243 39848098042932514309483865)
  ·
    refine ⟨29886073532199385732112899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39848098042932514309483865 29886073532199385732112899)
    ·
      refine ⟨44829110298299078598169349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29886073532199385732112899 44829110298299078598169349)
      ·
        refine ⟨8405458180931077237156753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44829110298299078598169349 8405458180931077237156753)
        ·
          refine ⟨6304093635698307927867565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8405458180931077237156753 6304093635698307927867565)
          ·
            refine ⟨2364035113386865472950337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6304093635698307927867565 2364035113386865472950337)
            ·
              refine ⟨1773026335040149104712753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364035113386865472950337 1773026335040149104712753)
              ·
                refine ⟨1329769751280111828534565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773026335040149104712753 1329769751280111828534565)
                ·
                  refine ⟨249331828365020967850231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329769751280111828534565 249331828365020967850231)
                  ·
                    rfl

theorem cell21_1092537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1092537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092537 prefixEnd_1092537 := by exact prefixLift 1092537
  have htrace : WordTrace (prefixWord ++ tailWord_1092537) baseStart_1092537 baseEnd_1092537 := by
    simpa [prefixWord, tailWord_1092537, baseEnd_1092537] using wordTrace_append hprefix tailTrace_1092537
  have hstable : (prefixWord ++ tailWord_1092537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092537).length < 2 ^ (prefixWord ++ tailWord_1092537).sum := by decide
  have hdescent : baseEnd_1092537 < baseStart_1092537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092557 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1092557 : Nat := 118140960795 + 1092557 * 2 ^ 59
def prefixEnd_1092557 : Nat := 4983230072969 + 3 ^ 40 * 1092557 * 2
def baseEnd_1092557 : Nat := 249336392637505377516857

theorem tailTrace_1092557 : CollatzResearch.WordTrace tailWord_1092557 prefixEnd_1092557 249336392637505377516857 := by
  unfold tailWord_1092557
  simp only [CollatzResearch.WordTrace]
  refine ⟨39848827502860057725211925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26565885001906705150141283 39848827502860057725211925)
  ·
    refine ⟨1867913789196565205869309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39848827502860057725211925 1867913789196565205869309)
    ·
      refine ⟨700467670948711952200991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1867913789196565205869309 700467670948711952200991)
      ·
        refine ⟨1050701506423067928301487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700467670948711952200991 1050701506423067928301487)
        ·
          refine ⟨1576052259634601892452231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050701506423067928301487 1576052259634601892452231)
          ·
            refine ⟨2364078389451902838678347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576052259634601892452231 2364078389451902838678347)
            ·
              refine ⟨3546117584177854258017521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364078389451902838678347 3546117584177854258017521)
              ·
                refine ⟨2659588188133390693513141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546117584177854258017521 2659588188133390693513141)
                ·
                  refine ⟨249336392637505377516857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2659588188133390693513141 249336392637505377516857)
                  ·
                    rfl

theorem cell21_1092557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1092557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092557 prefixEnd_1092557 := by exact prefixLift 1092557
  have htrace : WordTrace (prefixWord ++ tailWord_1092557) baseStart_1092557 baseEnd_1092557 := by
    simpa [prefixWord, tailWord_1092557, baseEnd_1092557] using wordTrace_append hprefix tailTrace_1092557
  have hstable : (prefixWord ++ tailWord_1092557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092557).length < 2 ^ (prefixWord ++ tailWord_1092557).sum := by decide
  have hdescent : baseEnd_1092557 < baseStart_1092557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092613 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1092613 : Nat := 118140960795 + 1092613 * 2 ^ 59
def prefixEnd_1092613 : Nat := 4983230072969 + 3 ^ 40 * 1092613 * 2
def baseEnd_1092613 : Nat := 249349172600461724583409

theorem tailTrace_1092613 : CollatzResearch.WordTrace tailWord_1092613 prefixEnd_1092613 249349172600461724583409 := by
  unfold tailWord_1092613
  simp only [CollatzResearch.WordTrace]
  refine ⟨39850869990657179289250493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26567246660438119526166995 39850869990657179289250493)
  ·
    refine ⟨14944076246496442233468935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39850869990657179289250493 14944076246496442233468935)
    ·
      refine ⟨22416114369744663350203403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14944076246496442233468935 22416114369744663350203403)
      ·
        refine ⟨33624171554616995025305105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22416114369744663350203403 33624171554616995025305105)
        ·
          refine ⟨25218128665962746268978829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33624171554616995025305105 25218128665962746268978829)
          ·
            refine ⟨9456798249736029850867061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25218128665962746268978829 9456798249736029850867061)
            ·
              refine ⟨886574835912752798518787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9456798249736029850867061 886574835912752798518787)
              ·
                refine ⟨1329862253869129197778181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886574835912752798518787 1329862253869129197778181)
                ·
                  refine ⟨249349172600461724583409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329862253869129197778181 249349172600461724583409)
                  ·
                    rfl

theorem cell21_1092613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1092613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092613 prefixEnd_1092613 := by exact prefixLift 1092613
  have htrace : WordTrace (prefixWord ++ tailWord_1092613) baseStart_1092613 baseEnd_1092613 := by
    simpa [prefixWord, tailWord_1092613, baseEnd_1092613] using wordTrace_append hprefix tailTrace_1092613
  have hstable : (prefixWord ++ tailWord_1092613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092613).length < 2 ^ (prefixWord ++ tailWord_1092613).sum := by decide
  have hdescent : baseEnd_1092613 < baseStart_1092613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092672 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_1092672 : Nat := 118140960795 + 1092672 * 2 ^ 59
def prefixEnd_1092672 : Nat := 4983230072969 + 3 ^ 40 * 1092672 * 2
def baseEnd_1092672 : Nat := 249362637204290733099955

theorem tailTrace_1092672 : CollatzResearch.WordTrace tailWord_1092672 prefixEnd_1092672 249362637204290733099955 := by
  unfold tailWord_1092672
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926510948721716182824135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26568681264962288243765513 19926510948721716182824135)
  ·
    refine ⟨29889766423082574274236203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19926510948721716182824135 29889766423082574274236203)
    ·
      refine ⟨44834649634623861411354305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29889766423082574274236203 44834649634623861411354305)
      ·
        refine ⟨33625987225967896058515729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44834649634623861411354305 33625987225967896058515729)
        ·
          refine ⟨25219490419475922043886797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33625987225967896058515729 25219490419475922043886797)
          ·
            refine ⟨9457308907303470766457549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25219490419475922043886797 9457308907303470766457549)
            ·
              refine ⟨3546490840238801537421581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9457308907303470766457549 3546490840238801537421581)
              ·
                refine ⟨1329934065089550576533093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3546490840238801537421581 1329934065089550576533093)
                ·
                  refine ⟨249362637204290733099955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329934065089550576533093 249362637204290733099955)
                  ·
                    rfl

theorem cell21_1092672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_1092672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092672 prefixEnd_1092672 := by exact prefixLift 1092672
  have htrace : WordTrace (prefixWord ++ tailWord_1092672) baseStart_1092672 baseEnd_1092672 := by
    simpa [prefixWord, tailWord_1092672, baseEnd_1092672] using wordTrace_append hprefix tailTrace_1092672
  have hstable : (prefixWord ++ tailWord_1092672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092672).length < 2 ^ (prefixWord ++ tailWord_1092672).sum := by decide
  have hdescent : baseEnd_1092672 < baseStart_1092672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092686 : List Nat := [4, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1092686 : Nat := 118140960795 + 1092686 * 2 ^ 59
def prefixEnd_1092686 : Nat := 4983230072969 + 3 ^ 40 * 1092686 * 2
def baseEnd_1092686 : Nat := 83121944065009939955531

theorem tailTrace_1092686 : CollatzResearch.WordTrace tailWord_1092686 prefixEnd_1092686 83121944065009939955531 := by
  unfold tailWord_1092686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981691564924089094582239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26569021679595141837771941 4981691564924089094582239)
  ·
    refine ⟨7472537347386133641873359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981691564924089094582239 7472537347386133641873359)
    ·
      refine ⟨11208806021079200462810039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7472537347386133641873359 11208806021079200462810039)
      ·
        refine ⟨16813209031618800694215059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11208806021079200462810039 16813209031618800694215059)
        ·
          refine ⟨25219813547428201041322589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16813209031618800694215059 25219813547428201041322589)
          ·
            refine ⟨9457430080285575390495971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25219813547428201041322589 9457430080285575390495971)
            ·
              refine ⟨14186145120428363085743957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457430080285575390495971 14186145120428363085743957)
              ·
                refine ⟨83121944065009939955531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14186145120428363085743957 83121944065009939955531)
                ·
                  rfl

theorem cell21_1092686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1092686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092686 prefixEnd_1092686 := by exact prefixLift 1092686
  have htrace : WordTrace (prefixWord ++ tailWord_1092686) baseStart_1092686 baseEnd_1092686 := by
    simpa [prefixWord, tailWord_1092686, baseEnd_1092686] using wordTrace_append hprefix tailTrace_1092686
  have hstable : (prefixWord ++ tailWord_1092686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092686).length < 2 ^ (prefixWord ++ tailWord_1092686).sum := by decide
  have hdescent : baseEnd_1092686 < baseStart_1092686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092706 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1092706 : Nat := 118140960795 + 1092706 * 2 ^ 59
def prefixEnd_1092706 : Nat := 4983230072969 + 3 ^ 40 * 1092706 * 2
def baseEnd_1092706 : Nat := 249370396467514229533219

theorem tailTrace_1092706 : CollatzResearch.WordTrace tailWord_1092706 prefixEnd_1092706 249370396467514229533219 := by
  unfold tailWord_1092706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963565494830064043096493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26569507986213504114923981 9963565494830064043096493)
  ·
    refine ⟨3736337060561274016161185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9963565494830064043096493 3736337060561274016161185)
    ·
      refine ⟨2802252795420955512120889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3736337060561274016161185 2802252795420955512120889)
      ·
        refine ⟨2101689596565716634090667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802252795420955512120889 2101689596565716634090667)
        ·
          refine ⟨3152534394848574951136001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101689596565716634090667 3152534394848574951136001)
          ·
            refine ⟨2364400796136431213352001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152534394848574951136001 2364400796136431213352001)
            ·
              refine ⟨1773300597102323410014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364400796136431213352001 1773300597102323410014001)
              ·
                refine ⟨1329975447826742557510501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773300597102323410014001 1329975447826742557510501)
                ·
                  refine ⟨249370396467514229533219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329975447826742557510501 249370396467514229533219)
                  ·
                    rfl

theorem cell21_1092706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1092706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092706 prefixEnd_1092706 := by exact prefixLift 1092706
  have htrace : WordTrace (prefixWord ++ tailWord_1092706) baseStart_1092706 baseEnd_1092706 := by
    simpa [prefixWord, tailWord_1092706, baseEnd_1092706] using wordTrace_append hprefix tailTrace_1092706
  have hstable : (prefixWord ++ tailWord_1092706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092706).length < 2 ^ (prefixWord ++ tailWord_1092706).sum := by decide
  have hdescent : baseEnd_1092706 < baseStart_1092706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092793 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_1092793 : Nat := 118140960795 + 1092793 * 2 ^ 59
def prefixEnd_1092793 : Nat := 4983230072969 + 3 ^ 40 * 1092793 * 2
def baseEnd_1092793 : Nat := 249390251052821411583041

theorem tailTrace_1092793 : CollatzResearch.WordTrace tailWord_1092793 prefixEnd_1092793 249390251052821411583041 := by
  unfold tailWord_1092793
  simp only [CollatzResearch.WordTrace]
  refine ⟨39857435130005070030803033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26571623420003380020535355 39857435130005070030803033)
  ·
    refine ⟨29893076347503802523102275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39857435130005070030803033 29893076347503802523102275)
    ·
      refine ⟨44839614521255703784653413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29893076347503802523102275 44839614521255703784653413)
      ·
        refine ⟨8407427722735444459622515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44839614521255703784653413 8407427722735444459622515)
        ·
          refine ⟨12611141584103166689433773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8407427722735444459622515 12611141584103166689433773)
          ·
            refine ⟨4729178094038687508537665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12611141584103166689433773 4729178094038687508537665)
            ·
              refine ⟨3546883570529015631403249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729178094038687508537665 3546883570529015631403249)
              ·
                refine ⟨2660162677896761723552437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546883570529015631403249 2660162677896761723552437)
                ·
                  refine ⟨249390251052821411583041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660162677896761723552437 249390251052821411583041)
                  ·
                    rfl

theorem cell21_1092793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_1092793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092793 prefixEnd_1092793 := by exact prefixLift 1092793
  have htrace : WordTrace (prefixWord ++ tailWord_1092793) baseStart_1092793 baseEnd_1092793 := by
    simpa [prefixWord, tailWord_1092793, baseEnd_1092793] using wordTrace_append hprefix tailTrace_1092793
  have hstable : (prefixWord ++ tailWord_1092793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092793).length < 2 ^ (prefixWord ++ tailWord_1092793).sum := by decide
  have hdescent : baseEnd_1092793 < baseStart_1092793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092796 : List Nat := [2, 2, 2, 3, 2, 3, 2, 5]
def baseStart_1092796 : Nat := 118140960795 + 1092796 * 2 ^ 59
def prefixEnd_1092796 : Nat := 4983230072969 + 3 ^ 40 * 1092796 * 2
def baseEnd_1092796 : Nat := 83130311897898024344345

theorem tailTrace_1092796 : CollatzResearch.WordTrace tailWord_1092796 prefixEnd_1092796 83130311897898024344345 := by
  unfold tailWord_1092796
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928772274497100771581121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26571696365996134362108161 19928772274497100771581121)
  ·
    refine ⟨14946579205872825578685841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19928772274497100771581121 14946579205872825578685841)
    ·
      refine ⟨11209934404404619184014381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14946579205872825578685841 11209934404404619184014381)
      ·
        refine ⟨4203725401651732194005393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11209934404404619184014381 4203725401651732194005393)
        ·
          refine ⟨3152794051238799145504045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4203725401651732194005393 3152794051238799145504045)
          ·
            refine ⟨1182297769214549679564017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3152794051238799145504045 1182297769214549679564017)
            ·
              refine ⟨886723326910912259673013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182297769214549679564017 886723326910912259673013)
              ·
                refine ⟨83130311897898024344345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 886723326910912259673013 83130311897898024344345)
                ·
                  rfl

theorem cell21_1092796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_1092796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092796 prefixEnd_1092796 := by exact prefixLift 1092796
  have htrace : WordTrace (prefixWord ++ tailWord_1092796) baseStart_1092796 baseEnd_1092796 := by
    simpa [prefixWord, tailWord_1092796, baseEnd_1092796] using wordTrace_append hprefix tailTrace_1092796
  have hstable : (prefixWord ++ tailWord_1092796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092796).length < 2 ^ (prefixWord ++ tailWord_1092796).sum := by decide
  have hdescent : baseEnd_1092796 < baseStart_1092796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092802 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1092802 : Nat := 118140960795 + 1092802 * 2 ^ 59
def prefixEnd_1092802 : Nat := 4983230072969 + 3 ^ 40 * 1092802 * 2
def baseEnd_1092802 : Nat := 249392304975439395933023

theorem tailTrace_1092802 : CollatzResearch.WordTrace tailWord_1092802 prefixEnd_1092802 249392304975439395933023 := by
  unfold tailWord_1092802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9964440846743116141970165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26571842257981643045253773 9964440846743116141970165)
  ·
    refine ⟨934166329382167138309703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9964440846743116141970165 934166329382167138309703)
    ·
      refine ⟨1401249494073250707464555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934166329382167138309703 1401249494073250707464555)
      ·
        refine ⟨2101874241109876061196833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401249494073250707464555 2101874241109876061196833)
        ·
          refine ⟨1576405680832407045897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101874241109876061196833 1576405680832407045897625)
          ·
            refine ⟨1182304260624305284423219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576405680832407045897625 1182304260624305284423219)
            ·
              refine ⟨1773456390936457926634829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182304260624305284423219 1773456390936457926634829)
              ·
                refine ⟨665046146601171722488061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773456390936457926634829 665046146601171722488061)
                ·
                  refine ⟨249392304975439395933023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665046146601171722488061 249392304975439395933023)
                  ·
                    rfl

theorem cell21_1092802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1092802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092802 prefixEnd_1092802 := by exact prefixLift 1092802
  have htrace : WordTrace (prefixWord ++ tailWord_1092802) baseStart_1092802 baseEnd_1092802 := by
    simpa [prefixWord, tailWord_1092802, baseEnd_1092802] using wordTrace_append hprefix tailTrace_1092802
  have hstable : (prefixWord ++ tailWord_1092802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092802).length < 2 ^ (prefixWord ++ tailWord_1092802).sum := by decide
  have hdescent : baseEnd_1092802 < baseStart_1092802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092813 : List Nat := [1, 6, 2, 2, 1, 2, 7]
def baseStart_1092813 : Nat := 118140960795 + 1092813 * 2 ^ 59
def prefixEnd_1092813 : Nat := 4983230072969 + 3 ^ 40 * 1092813 * 2
def baseEnd_1092813 : Nat := 27710535036145091249963

theorem tailTrace_1092813 : CollatzResearch.WordTrace tailWord_1092813 prefixEnd_1092813 27710535036145091249963 := by
  unfold tailWord_1092813
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858164589932613446531093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26572109726621742297687395 39858164589932613446531093)
  ·
    refine ⟨1868351465153091255306145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39858164589932613446531093 1868351465153091255306145)
    ·
      refine ⟨1401263598864818441479609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1868351465153091255306145 1401263598864818441479609)
      ·
        refine ⟨1050947699148613831109707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1401263598864818441479609 1050947699148613831109707)
        ·
          refine ⟨1576421548722920746664561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050947699148613831109707 1576421548722920746664561)
          ·
            refine ⟨1182316161542190559998421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576421548722920746664561 1182316161542190559998421)
            ·
              refine ⟨27710535036145091249963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1182316161542190559998421 27710535036145091249963)
              ·
                rfl

theorem cell21_1092813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 7].length) (baseStart_1092813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092813 prefixEnd_1092813 := by exact prefixLift 1092813
  have htrace : WordTrace (prefixWord ++ tailWord_1092813) baseStart_1092813 baseEnd_1092813 := by
    simpa [prefixWord, tailWord_1092813, baseEnd_1092813] using wordTrace_append hprefix tailTrace_1092813
  have hstable : (prefixWord ++ tailWord_1092813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092813).length < 2 ^ (prefixWord ++ tailWord_1092813).sum := by decide
  have hdescent : baseEnd_1092813 < baseStart_1092813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092900 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1092900 : Nat := 118140960795 + 1092900 * 2 ^ 59
def prefixEnd_1092900 : Nat := 4983230072969 + 3 ^ 40 * 1092900 * 2
def baseEnd_1092900 : Nat := 249414669910613003299489

theorem tailTrace_1092900 : CollatzResearch.WordTrace tailWord_1092900 prefixEnd_1092900 249414669910613003299489 := by
  unfold tailWord_1092900
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930668870308713652474077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26574225160411618203298769 19930668870308713652474077)
  ·
    refine ⟨7474000826365767619677779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19930668870308713652474077 7474000826365767619677779)
    ·
      refine ⟨11211001239548651429516669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474000826365767619677779 11211001239548651429516669)
      ·
        refine ⟨4204125464830744286068751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11211001239548651429516669 4204125464830744286068751)
        ·
          refine ⟨6306188197246116429103127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204125464830744286068751 6306188197246116429103127)
          ·
            refine ⟨9459282295869174643654691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306188197246116429103127 9459282295869174643654691)
            ·
              refine ⟨14188923443803761965482037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459282295869174643654691 14188923443803761965482037)
              ·
                refine ⟨1330211572856602684263941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14188923443803761965482037 1330211572856602684263941)
                ·
                  refine ⟨249414669910613003299489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330211572856602684263941 249414669910613003299489)
                  ·
                    rfl

theorem cell21_1092900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1092900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092900 prefixEnd_1092900 := by exact prefixLift 1092900
  have htrace : WordTrace (prefixWord ++ tailWord_1092900) baseStart_1092900 baseEnd_1092900 := by
    simpa [prefixWord, tailWord_1092900, baseEnd_1092900] using wordTrace_append hprefix tailTrace_1092900
  have hstable : (prefixWord ++ tailWord_1092900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092900).length < 2 ^ (prefixWord ++ tailWord_1092900).sum := by decide
  have hdescent : baseEnd_1092900 < baseStart_1092900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092928 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1092928 : Nat := 118140960795 + 1092928 * 2 ^ 59
def prefixEnd_1092928 : Nat := 4983230072969 + 3 ^ 40 * 1092928 * 2
def baseEnd_1092928 : Nat := 249421059892091176832765

theorem tailTrace_1092928 : CollatzResearch.WordTrace tailWord_1092928 prefixEnd_1092928 249421059892091176832765 := by
  unfold tailWord_1092928
  simp only [CollatzResearch.WordTrace]
  refine ⟨19931179492257994043483719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26574905989677325391311625 19931179492257994043483719)
  ·
    refine ⟨29896769238386991065225579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19931179492257994043483719 29896769238386991065225579)
    ·
      refine ⟨44845153857580486597838369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29896769238386991065225579 44845153857580486597838369)
      ·
        refine ⟨33633865393185364948378777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44845153857580486597838369 33633865393185364948378777)
        ·
          refine ⟨25225399044889023711284083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33633865393185364948378777 25225399044889023711284083)
          ·
            refine ⟨37838098567333535566926125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25225399044889023711284083 37838098567333535566926125)
            ·
              refine ⟨14189286962750075837597297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37838098567333535566926125 14189286962750075837597297)
              ·
                refine ⟨10641965222062556878197973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14189286962750075837597297 10641965222062556878197973)
                ·
                  refine ⟨249421059892091176832765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10641965222062556878197973 249421059892091176832765)
                  ·
                    rfl

theorem cell21_1092928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1092928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092928 prefixEnd_1092928 := by exact prefixLift 1092928
  have htrace : WordTrace (prefixWord ++ tailWord_1092928) baseStart_1092928 baseEnd_1092928 := by
    simpa [prefixWord, tailWord_1092928, baseEnd_1092928] using wordTrace_append hprefix tailTrace_1092928
  have hstable : (prefixWord ++ tailWord_1092928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092928).length < 2 ^ (prefixWord ++ tailWord_1092928).sum := by decide
  have hdescent : baseEnd_1092928 < baseStart_1092928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092945 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1092945 : Nat := 118140960795 + 1092945 * 2 ^ 59
def prefixEnd_1092945 : Nat := 4983230072969 + 3 ^ 40 * 1092945 * 2
def baseEnd_1092945 : Nat := 249424939523702925049397

theorem tailTrace_1092945 : CollatzResearch.WordTrace tailWord_1092945 prefixEnd_1092945 249424939523702925049397 := by
  unfold tailWord_1092945
  simp only [CollatzResearch.WordTrace]
  refine ⟨39862979025454399990336289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26575319350302933326890859 39862979025454399990336289)
  ·
    refine ⟨29897234269090799992752217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39862979025454399990336289 29897234269090799992752217)
    ·
      refine ⟨22422925701818099994564163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29897234269090799992752217 22422925701818099994564163)
      ·
        refine ⟨33634388552727149991846245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22422925701818099994564163 33634388552727149991846245)
        ·
          refine ⟨6306447853636340623471171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33634388552727149991846245 6306447853636340623471171)
          ·
            refine ⟨9459671780454510935206757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306447853636340623471171 9459671780454510935206757)
            ·
              refine ⟨1773688458835220800351267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9459671780454510935206757 1773688458835220800351267)
              ·
                refine ⟨2660532688252831200526901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773688458835220800351267 2660532688252831200526901)
                ·
                  refine ⟨249424939523702925049397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660532688252831200526901 249424939523702925049397)
                  ·
                    rfl

theorem cell21_1092945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1092945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1092945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1092945 prefixEnd_1092945 := by exact prefixLift 1092945
  have htrace : WordTrace (prefixWord ++ tailWord_1092945) baseStart_1092945 baseEnd_1092945 := by
    simpa [prefixWord, tailWord_1092945, baseEnd_1092945] using wordTrace_append hprefix tailTrace_1092945
  have hstable : (prefixWord ++ tailWord_1092945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092945).length < 2 ^ (prefixWord ++ tailWord_1092945).sum := by decide
  have hdescent : baseEnd_1092945 < baseStart_1092945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093010 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1093010 : Nat := 118140960795 + 1093010 * 2 ^ 59
def prefixEnd_1093010 : Nat := 4983230072969 + 3 ^ 40 * 1093010 * 2
def baseEnd_1093010 : Nat := 249439773409277256465931

theorem tailTrace_1093010 : CollatzResearch.WordTrace tailWord_1093010 prefixEnd_1093010 249439773409277256465931 := by
  unfold tailWord_1093010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966337442554729022863121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26576899846812610727634989 9966337442554729022863121)
  ·
    refine ⟨7474753081916046767147341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9966337442554729022863121 7474753081916046767147341)
    ·
      refine ⟨2803032405718517537680253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7474753081916046767147341 2803032405718517537680253)
      ·
        refine ⟨1051137152144444076630095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2803032405718517537680253 1051137152144444076630095)
        ·
          refine ⟨1576705728216666114945143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051137152144444076630095 1576705728216666114945143)
          ·
            refine ⟨2365058592324999172417715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576705728216666114945143 2365058592324999172417715)
            ·
              refine ⟨3547587888487498758626573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365058592324999172417715 3547587888487498758626573)
              ·
                refine ⟨1330345458182812034484965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3547587888487498758626573 1330345458182812034484965)
                ·
                  refine ⟨249439773409277256465931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330345458182812034484965 249439773409277256465931)
                  ·
                    rfl

theorem cell21_1093010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1093010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093010 prefixEnd_1093010 := by exact prefixLift 1093010
  have htrace : WordTrace (prefixWord ++ tailWord_1093010) baseStart_1093010 baseEnd_1093010 := by
    simpa [prefixWord, tailWord_1093010, baseEnd_1093010] using wordTrace_append hprefix tailTrace_1093010
  have hstable : (prefixWord ++ tailWord_1093010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093010).length < 2 ^ (prefixWord ++ tailWord_1093010).sum := by decide
  have hdescent : baseEnd_1093010 < baseStart_1093010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093049 : List Nat := [1, 2, 1, 4, 13]
def baseStart_1093049 : Nat := 118140960795 + 1093049 * 2 ^ 59
def prefixEnd_1093049 : Nat := 4983230072969 + 3 ^ 40 * 1093049 * 2
def baseEnd_1093049 : Nat := 3079613256057059942171

theorem tailTrace_1093049 : CollatzResearch.WordTrace tailWord_1093049 prefixEnd_1093049 3079613256057059942171 := by
  unfold tailWord_1093049
  simp only [CollatzResearch.WordTrace]
  refine ⟨39866772217077625752122201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26577848144718417168081467 39866772217077625752122201)
  ·
    refine ⟨29900079162808219314091651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39866772217077625752122201 29900079162808219314091651)
    ·
      refine ⟨44850118744212328971137477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29900079162808219314091651 44850118744212328971137477)
      ·
        refine ⟨8409397264539811682088277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44850118744212328971137477 8409397264539811682088277)
        ·
          refine ⟨3079613256057059942171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8409397264539811682088277 3079613256057059942171)
          ·
            rfl

theorem cell21_1093049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 13].length) (baseStart_1093049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093049 prefixEnd_1093049 := by exact prefixLift 1093049
  have htrace : WordTrace (prefixWord ++ tailWord_1093049) baseStart_1093049 baseEnd_1093049 := by
    simpa [prefixWord, tailWord_1093049, baseEnd_1093049] using wordTrace_append hprefix tailTrace_1093049
  have hstable : (prefixWord ++ tailWord_1093049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093049).length < 2 ^ (prefixWord ++ tailWord_1093049).sum := by decide
  have hdescent : baseEnd_1093049 < baseStart_1093049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093066 : List Nat := [3, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1093066 : Nat := 118140960795 + 1093066 * 2 ^ 59
def prefixEnd_1093066 : Nat := 4983230072969 + 3 ^ 40 * 1093066 * 2
def baseEnd_1093066 : Nat := 83150851124077867844161

theorem tailTrace_1093066 : CollatzResearch.WordTrace tailWord_1093066 prefixEnd_1093066 83150851124077867844161 := by
  unfold tailWord_1093066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966848064504009413872763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26578261505344025103660701 9966848064504009413872763)
  ·
    refine ⟨14950272096756014120809145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9966848064504009413872763 14950272096756014120809145)
    ·
      refine ⟨11212704072567010590606859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14950272096756014120809145 11212704072567010590606859)
      ·
        refine ⟨16819056108850515885910289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212704072567010590606859 16819056108850515885910289)
        ·
          refine ⟨12614292081637886914432717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16819056108850515885910289 12614292081637886914432717)
          ·
            refine ⟨4730359530614207592912269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12614292081637886914432717 4730359530614207592912269)
            ·
              refine ⟨1773884823980327847342101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4730359530614207592912269 1773884823980327847342101)
              ·
                refine ⟨83150851124077867844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1773884823980327847342101 83150851124077867844161)
                ·
                  rfl

theorem cell21_1093066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1093066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093066 prefixEnd_1093066 := by exact prefixLift 1093066
  have htrace : WordTrace (prefixWord ++ tailWord_1093066) baseStart_1093066 baseEnd_1093066 := by
    simpa [prefixWord, tailWord_1093066, baseEnd_1093066] using wordTrace_append hprefix tailTrace_1093066
  have hstable : (prefixWord ++ tailWord_1093066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093066).length < 2 ^ (prefixWord ++ tailWord_1093066).sum := by decide
  have hdescent : baseEnd_1093066 < baseStart_1093066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093080 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1093080 : Nat := 118140960795 + 1093080 * 2 ^ 59
def prefixEnd_1093080 : Nat := 4983230072969 + 3 ^ 40 * 1093080 * 2
def baseEnd_1093080 : Nat := 249455748362972690299121

theorem tailTrace_1093080 : CollatzResearch.WordTrace tailWord_1093080 prefixEnd_1093080 249455748362972690299121 := by
  unfold tailWord_1093080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933951439982659023250347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26578601919976878697667129 19933951439982659023250347)
  ·
    refine ⟨29900927159973988534875521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933951439982659023250347 29900927159973988534875521)
    ·
      refine ⟨22425695369980491401156641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29900927159973988534875521 22425695369980491401156641)
      ·
        refine ⟨16819271527485368550867481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22425695369980491401156641 16819271527485368550867481)
        ·
          refine ⟨12614453645614026413150611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16819271527485368550867481 12614453645614026413150611)
          ·
            refine ⟨18921680468421039619725917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12614453645614026413150611 18921680468421039619725917)
            ·
              refine ⟨7095630175657889857397219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18921680468421039619725917 7095630175657889857397219)
              ·
                refine ⟨10643445263486834786095829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095630175657889857397219 10643445263486834786095829)
                ·
                  refine ⟨249455748362972690299121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10643445263486834786095829 249455748362972690299121)
                  ·
                    rfl

theorem cell21_1093080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1093080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093080 prefixEnd_1093080 := by exact prefixLift 1093080
  have htrace : WordTrace (prefixWord ++ tailWord_1093080) baseStart_1093080 baseEnd_1093080 := by
    simpa [prefixWord, tailWord_1093080, baseEnd_1093080] using wordTrace_append hprefix tailTrace_1093080
  have hstable : (prefixWord ++ tailWord_1093080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093080).length < 2 ^ (prefixWord ++ tailWord_1093080).sum := by decide
  have hdescent : baseEnd_1093080 < baseStart_1093080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093111 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_1093111 : Nat := 118140960795 + 1093111 * 2 ^ 59
def prefixEnd_1093111 : Nat := 4983230072969 + 3 ^ 40 * 1093111 * 2
def baseEnd_1093111 : Nat := 249462822985323525282391

theorem tailTrace_1093111 : CollatzResearch.WordTrace tailWord_1093111 prefixEnd_1093111 249462822985323525282391 := by
  unfold tailWord_1093111
  simp only [CollatzResearch.WordTrace]
  refine ⟨39869033542853010340879187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26579355695235340227252791 39869033542853010340879187)
  ·
    refine ⟨59803550314279515511318781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39869033542853010340879187 59803550314279515511318781)
    ·
      refine ⟨22426331367854818316744543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59803550314279515511318781 22426331367854818316744543)
      ·
        refine ⟨33639497051782227475116815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22426331367854818316744543 33639497051782227475116815)
        ·
          refine ⟨50459245577673341212675223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33639497051782227475116815 50459245577673341212675223)
          ·
            refine ⟨75688868366510011819012835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50459245577673341212675223 75688868366510011819012835)
            ·
              refine ⟨113533302549765017728519253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75688868366510011819012835 113533302549765017728519253)
              ·
                refine ⟨1330468389255058801506085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 113533302549765017728519253 1330468389255058801506085)
                ·
                  refine ⟨249462822985323525282391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330468389255058801506085 249462822985323525282391)
                  ·
                    rfl

theorem cell21_1093111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_1093111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093111 prefixEnd_1093111 := by exact prefixLift 1093111
  have htrace : WordTrace (prefixWord ++ tailWord_1093111) baseStart_1093111 baseEnd_1093111 := by
    simpa [prefixWord, tailWord_1093111, baseEnd_1093111] using wordTrace_append hprefix tailTrace_1093111
  have hstable : (prefixWord ++ tailWord_1093111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093111).length < 2 ^ (prefixWord ++ tailWord_1093111).sum := by decide
  have hdescent : baseEnd_1093111 < baseStart_1093111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093125 : List Nat := [1, 3, 1, 1, 2, 2, 1, 10]
def baseStart_1093125 : Nat := 118140960795 + 1093125 * 2 ^ 59
def prefixEnd_1093125 : Nat := 4983230072969 + 3 ^ 40 * 1093125 * 2
def baseEnd_1093125 : Nat := 83155339325354204016343

theorem tailTrace_1093125 : CollatzResearch.WordTrace tailWord_1093125 prefixEnd_1093125 83155339325354204016343 := by
  unfold tailWord_1093125
  simp only [CollatzResearch.WordTrace]
  refine ⟨39869544164802290731888829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26579696109868193821259219 39869544164802290731888829)
  ·
    refine ⟨14951079061800859024458311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39869544164802290731888829 14951079061800859024458311)
    ·
      refine ⟨22426618592701288536687467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951079061800859024458311 22426618592701288536687467)
      ·
        refine ⟨33639927889051932805031201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22426618592701288536687467 33639927889051932805031201)
        ·
          refine ⟨25229945916788949603773401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33639927889051932805031201 25229945916788949603773401)
          ·
            refine ⟨18922459437591712202830051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25229945916788949603773401 18922459437591712202830051)
            ·
              refine ⟨28383689156387568304245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18922459437591712202830051 28383689156387568304245077)
              ·
                refine ⟨83155339325354204016343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28383689156387568304245077 83155339325354204016343)
                ·
                  rfl

theorem cell21_1093125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_1093125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093125 prefixEnd_1093125 := by exact prefixLift 1093125
  have htrace : WordTrace (prefixWord ++ tailWord_1093125) baseStart_1093125 baseEnd_1093125 := by
    simpa [prefixWord, tailWord_1093125, baseEnd_1093125] using wordTrace_append hprefix tailTrace_1093125
  have hstable : (prefixWord ++ tailWord_1093125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093125).length < 2 ^ (prefixWord ++ tailWord_1093125).sum := by decide
  have hdescent : baseEnd_1093125 < baseStart_1093125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093173 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1093173 : Nat := 118140960795 + 1093173 * 2 ^ 59
def prefixEnd_1093173 : Nat := 4983230072969 + 3 ^ 40 * 1093173 * 2
def baseEnd_1093173 : Nat := 249476972230025195248931

theorem tailTrace_1093173 : CollatzResearch.WordTrace tailWord_1093173 prefixEnd_1093173 249476972230025195248931 := by
  unfold tailWord_1093173
  simp only [CollatzResearch.WordTrace]
  refine ⟨39871294868628394929636173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26580863245752263286424115 39871294868628394929636173)
  ·
    refine ⟨14951735575735648098613565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39871294868628394929636173 14951735575735648098613565)
    ·
      refine ⟨5606900840900868036980087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14951735575735648098613565 5606900840900868036980087)
      ·
        refine ⟨8410351261351302055470131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606900840900868036980087 8410351261351302055470131)
        ·
          refine ⟨12615526892026953083205197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410351261351302055470131 12615526892026953083205197)
          ·
            refine ⟨4730822584510107406201949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12615526892026953083205197 4730822584510107406201949)
            ·
              refine ⟨1774058469191290277325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4730822584510107406201949 1774058469191290277325731)
              ·
                refine ⟨2661087703786935415988597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774058469191290277325731 2661087703786935415988597)
                ·
                  refine ⟨249476972230025195248931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661087703786935415988597 249476972230025195248931)
                  ·
                    rfl

theorem cell21_1093173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1093173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093173 prefixEnd_1093173 := by exact prefixLift 1093173
  have htrace : WordTrace (prefixWord ++ tailWord_1093173) baseStart_1093173 baseEnd_1093173 := by
    simpa [prefixWord, tailWord_1093173, baseEnd_1093173] using wordTrace_append hprefix tailTrace_1093173
  have hstable : (prefixWord ++ tailWord_1093173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093173).length < 2 ^ (prefixWord ++ tailWord_1093173).sum := by decide
  have hdescent : baseEnd_1093173 < baseStart_1093173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093201 : List Nat := [1, 2, 2, 1, 3, 2, 1, 9]
def baseStart_1093201 : Nat := 118140960795 + 1093201 * 2 ^ 59
def prefixEnd_1093201 : Nat := 4983230072969 + 3 ^ 40 * 1093201 * 2
def baseEnd_1093201 : Nat := 83161120737167789594069

theorem tailTrace_1093201 : CollatzResearch.WordTrace tailWord_1093201 prefixEnd_1093201 83161120737167789594069 := by
  unfold tailWord_1093201
  simp only [CollatzResearch.WordTrace]
  refine ⟨39872316112526955711655457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26581544075017970474436971 39872316112526955711655457)
  ·
    refine ⟨29904237084395216783741593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39872316112526955711655457 29904237084395216783741593)
    ·
      refine ⟨22428177813296412587806195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29904237084395216783741593 22428177813296412587806195)
      ·
        refine ⟨33642266719944618881709293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22428177813296412587806195 33642266719944618881709293)
        ·
          refine ⟨12615850019979232080640985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33642266719944618881709293 12615850019979232080640985)
          ·
            refine ⟨9461887514984424060480739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12615850019979232080640985 9461887514984424060480739)
            ·
              refine ⟨14192831272476636090721109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461887514984424060480739 14192831272476636090721109)
              ·
                refine ⟨83161120737167789594069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14192831272476636090721109 83161120737167789594069)
                ·
                  rfl

theorem cell21_1093201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_1093201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093201 prefixEnd_1093201 := by exact prefixLift 1093201
  have htrace : WordTrace (prefixWord ++ tailWord_1093201) baseStart_1093201 baseEnd_1093201 := by
    simpa [prefixWord, tailWord_1093201, baseEnd_1093201] using wordTrace_append hprefix tailTrace_1093201
  have hstable : (prefixWord ++ tailWord_1093201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093201).length < 2 ^ (prefixWord ++ tailWord_1093201).sum := by decide
  have hdescent : baseEnd_1093201 < baseStart_1093201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093224 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_1093224 : Nat := 118140960795 + 1093224 * 2 ^ 59
def prefixEnd_1093224 : Nat := 4983230072969 + 3 ^ 40 * 1093224 * 2
def baseEnd_1093224 : Nat := 249488611124860439898827

theorem tailTrace_1093224 : CollatzResearch.WordTrace tailWord_1093224 prefixEnd_1093224 249488611124860439898827 := by
  unfold tailWord_1093224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936577495721815319871363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26582103327629087093161817 19936577495721815319871363)
  ·
    refine ⟨29904866243582722979807045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19936577495721815319871363 29904866243582722979807045)
    ·
      refine ⟨5607162420671760558713821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29904866243582722979807045 5607162420671760558713821)
      ·
        refine ⟨2102685907751910209517683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5607162420671760558713821 2102685907751910209517683)
        ·
          refine ⟨3154028861627865314276525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102685907751910209517683 3154028861627865314276525)
          ·
            refine ⟨1182760823110449492853697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3154028861627865314276525 1182760823110449492853697)
            ·
              refine ⟨887070617332837119640273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182760823110449492853697 887070617332837119640273)
              ·
                refine ⟨665302962999627839730205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887070617332837119640273 665302962999627839730205)
                ·
                  refine ⟨249488611124860439898827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665302962999627839730205 249488611124860439898827)
                  ·
                    rfl

theorem cell21_1093224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_1093224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093224 prefixEnd_1093224 := by exact prefixLift 1093224
  have htrace : WordTrace (prefixWord ++ tailWord_1093224) baseStart_1093224 baseEnd_1093224 := by
    simpa [prefixWord, tailWord_1093224, baseEnd_1093224] using wordTrace_append hprefix tailTrace_1093224
  have hstable : (prefixWord ++ tailWord_1093224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093224).length < 2 ^ (prefixWord ++ tailWord_1093224).sum := by decide
  have hdescent : baseEnd_1093224 < baseStart_1093224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093249 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_1093249 : Nat := 118140960795 + 1093249 * 2 ^ 59
def prefixEnd_1093249 : Nat := 4983230072969 + 3 ^ 40 * 1093249 * 2
def baseEnd_1093249 : Nat := 249494316465465951982109

theorem tailTrace_1093249 : CollatzResearch.WordTrace tailWord_1093249 prefixEnd_1093249 249494316465465951982109 := by
  unfold tailWord_1093249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39874066816353059909402801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26582711210902039939601867 39874066816353059909402801)
  ·
    refine ⟨29905550112264794932052101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39874066816353059909402801 29905550112264794932052101)
    ·
      refine ⟨5607290646049649049759769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29905550112264794932052101 5607290646049649049759769)
      ·
        refine ⟨4205467984537236787319827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5607290646049649049759769 4205467984537236787319827)
        ·
          refine ⟨6308201976805855180979741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205467984537236787319827 6308201976805855180979741)
          ·
            refine ⟨2365575741302195692867403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6308201976805855180979741 2365575741302195692867403)
            ·
              refine ⟨3548363611953293539301105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365575741302195692867403 3548363611953293539301105)
              ·
                refine ⟨2661272708964970154475829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548363611953293539301105 2661272708964970154475829)
                ·
                  refine ⟨249494316465465951982109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661272708964970154475829 249494316465465951982109)
                  ·
                    rfl

theorem cell21_1093249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_1093249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093249 prefixEnd_1093249 := by exact prefixLift 1093249
  have htrace : WordTrace (prefixWord ++ tailWord_1093249) baseStart_1093249 baseEnd_1093249 := by
    simpa [prefixWord, tailWord_1093249, baseEnd_1093249] using wordTrace_append hprefix tailTrace_1093249
  have hstable : (prefixWord ++ tailWord_1093249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093249).length < 2 ^ (prefixWord ++ tailWord_1093249).sum := by decide
  have hdescent : baseEnd_1093249 < baseStart_1093249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093280 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_1093280 : Nat := 118140960795 + 1093280 * 2 ^ 59
def prefixEnd_1093280 : Nat := 4983230072969 + 3 ^ 40 * 1093280 * 2
def baseEnd_1093280 : Nat := 249501391087816786965379

theorem tailTrace_1093280 : CollatzResearch.WordTrace tailWord_1093280 prefixEnd_1093280 249501391087816786965379 := by
  unfold tailWord_1093280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19937598739620376101890647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26583464986160501469187529 19937598739620376101890647)
  ·
    refine ⟨29906398109430564152835971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19937598739620376101890647 29906398109430564152835971)
    ·
      refine ⟨44859597164145846229253957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29906398109430564152835971 44859597164145846229253957)
      ·
        refine ⟨8411174468277346167985117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44859597164145846229253957 8411174468277346167985117)
        ·
          refine ⟨3154190425604004812994419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8411174468277346167985117 3154190425604004812994419)
          ·
            refine ⟨4731285638406007219491629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154190425604004812994419 4731285638406007219491629)
            ·
              refine ⟨1774232114402252707309361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4731285638406007219491629 1774232114402252707309361)
              ·
                refine ⟨1330674085801689530482021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774232114402252707309361 1330674085801689530482021)
                ·
                  refine ⟨249501391087816786965379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330674085801689530482021 249501391087816786965379)
                  ·
                    rfl

theorem cell21_1093280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_1093280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093280 prefixEnd_1093280 := by exact prefixLift 1093280
  have htrace : WordTrace (prefixWord ++ tailWord_1093280) baseStart_1093280 baseEnd_1093280 := by
    simpa [prefixWord, tailWord_1093280, baseEnd_1093280] using wordTrace_append hprefix tailTrace_1093280
  have hstable : (prefixWord ++ tailWord_1093280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093280).length < 2 ^ (prefixWord ++ tailWord_1093280).sum := by decide
  have hdescent : baseEnd_1093280 < baseStart_1093280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093356 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1093356 : Nat := 118140960795 + 1093356 * 2 ^ 59
def prefixEnd_1093356 : Nat := 4983230072969 + 3 ^ 40 * 1093356 * 2
def baseEnd_1093356 : Nat := 249518735323257543698557

theorem tailTrace_1093356 : CollatzResearch.WordTrace tailWord_1093356 prefixEnd_1093356 249518735323257543698557 := by
  unfold tailWord_1093356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938984713482708591773961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26585312951310278122365281 19938984713482708591773961)
  ·
    refine ⟨14954238535112031443830471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19938984713482708591773961 14954238535112031443830471)
    ·
      refine ⟨22431357802668047165745707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14954238535112031443830471 22431357802668047165745707)
      ·
        refine ⟨33647036704002070748618561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22431357802668047165745707 33647036704002070748618561)
        ·
          refine ⟨25235277528001553061463921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33647036704002070748618561 25235277528001553061463921)
          ·
            refine ⟨18926458146001164796097941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25235277528001553061463921 18926458146001164796097941)
            ·
              refine ⟨887177725593804599817091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18926458146001164796097941 887177725593804599817091)
              ·
                refine ⟨1330766588390706899725637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887177725593804599817091 1330766588390706899725637)
                ·
                  refine ⟨249518735323257543698557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330766588390706899725637 249518735323257543698557)
                  ·
                    rfl

theorem cell21_1093356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1093356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093356 prefixEnd_1093356 := by exact prefixLift 1093356
  have htrace : WordTrace (prefixWord ++ tailWord_1093356) baseStart_1093356 baseEnd_1093356 := by
    simpa [prefixWord, tailWord_1093356, baseEnd_1093356] using wordTrace_append hprefix tailTrace_1093356
  have hstable : (prefixWord ++ tailWord_1093356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093356).length < 2 ^ (prefixWord ++ tailWord_1093356).sum := by decide
  have hdescent : baseEnd_1093356 < baseStart_1093356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093511 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 3]
def baseStart_1093511 : Nat := 118140960795 + 1093511 * 2 ^ 59
def prefixEnd_1093511 : Nat := 4983230072969 + 3 ^ 40 * 1093511 * 2
def baseEnd_1093511 : Nat := 249554108435011718614907

theorem tailTrace_1093511 : CollatzResearch.WordTrace tailWord_1093511 prefixEnd_1093511 249554108435011718614907 := by
  unfold tailWord_1093511
  simp only [CollatzResearch.WordTrace]
  refine ⟨39883622741403878655440387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26589081827602585770293591 39883622741403878655440387)
  ·
    refine ⟨59825434112105817983160581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39883622741403878655440387 59825434112105817983160581)
    ·
      refine ⟨11217268896019840871842609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59825434112105817983160581 11217268896019840871842609)
      ·
        refine ⟨8412951672014880653881957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11217268896019840871842609 8412951672014880653881957)
        ·
          refine ⟨1577428438502790122602867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8412951672014880653881957 1577428438502790122602867)
          ·
            refine ⟨2366142657754185183904301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577428438502790122602867 2366142657754185183904301)
            ·
              refine ⟨887303496657819443964113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2366142657754185183904301 887303496657819443964113)
              ·
                refine ⟨665477622493364582973085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887303496657819443964113 665477622493364582973085)
                ·
                  refine ⟨249554108435011718614907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665477622493364582973085 249554108435011718614907)
                  ·
                    rfl

theorem cell21_1093511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].length) (baseStart_1093511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093511 prefixEnd_1093511 := by exact prefixLift 1093511
  have htrace : WordTrace (prefixWord ++ tailWord_1093511) baseStart_1093511 baseEnd_1093511 := by
    simpa [prefixWord, tailWord_1093511, baseEnd_1093511] using wordTrace_append hprefix tailTrace_1093511
  have hstable : (prefixWord ++ tailWord_1093511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093511).length < 2 ^ (prefixWord ++ tailWord_1093511).sum := by decide
  have hdescent : baseEnd_1093511 < baseStart_1093511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093522 : List Nat := [3, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1093522 : Nat := 118140960795 + 1093522 * 2 ^ 59
def prefixEnd_1093522 : Nat := 4983230072969 + 3 ^ 40 * 1093522 * 2
def baseEnd_1093522 : Nat := 83185539594959381310517

theorem tailTrace_1093522 : CollatzResearch.WordTrace tailWord_1093522 prefixEnd_1093522 83185539594959381310517 := by
  unfold tailWord_1093522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971005986091006883522705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26589349296242685022727213 9971005986091006883522705)
  ·
    refine ⟨7478254489568255162642029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9971005986091006883522705 7478254489568255162642029)
    ·
      refine ⟨2804345433588095685990761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7478254489568255162642029 2804345433588095685990761)
      ·
        refine ⟨2103259075191071764493071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2804345433588095685990761 2103259075191071764493071)
        ·
          refine ⟨3154888612786607646739607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103259075191071764493071 3154888612786607646739607)
          ·
            refine ⟨4732332919179911470109411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154888612786607646739607 4732332919179911470109411)
            ·
              refine ⟨7098499378769867205164117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732332919179911470109411 7098499378769867205164117)
              ·
                refine ⟨83185539594959381310517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7098499378769867205164117 83185539594959381310517)
                ·
                  rfl

theorem cell21_1093522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1093522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093522 prefixEnd_1093522 := by exact prefixLift 1093522
  have htrace : WordTrace (prefixWord ++ tailWord_1093522) baseStart_1093522 baseEnd_1093522 := by
    simpa [prefixWord, tailWord_1093522, baseEnd_1093522] using wordTrace_append hprefix tailTrace_1093522
  have hstable : (prefixWord ++ tailWord_1093522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093522).length < 2 ^ (prefixWord ++ tailWord_1093522).sum := by decide
  have hdescent : baseEnd_1093522 < baseStart_1093522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093567 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_1093567 : Nat := 118140960795 + 1093567 * 2 ^ 59
def prefixEnd_1093567 : Nat := 4983230072969 + 3 ^ 40 * 1093567 * 2
def baseEnd_1093567 : Nat := 249566888397968065681459

theorem tailTrace_1093567 : CollatzResearch.WordTrace tailWord_1093567 prefixEnd_1093567 249566888397968065681459 := by
  unfold tailWord_1093567
  simp only [CollatzResearch.WordTrace]
  refine ⟨39885665229201000219478955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26590443486134000146319303 39885665229201000219478955)
  ·
    refine ⟨59828497843801500329218433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39885665229201000219478955 59828497843801500329218433)
    ·
      refine ⟨44871373382851125246913825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59828497843801500329218433 44871373382851125246913825)
      ·
        refine ⟨33653530037138343935185369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44871373382851125246913825 33653530037138343935185369)
        ·
          refine ⟨25240147527853757951389027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33653530037138343935185369 25240147527853757951389027)
          ·
            refine ⟨37860221291780636927083541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25240147527853757951389027 37860221291780636927083541)
            ·
              refine ⟨1774697873052217355957041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37860221291780636927083541 1774697873052217355957041)
              ·
                refine ⟨1331023404789163016967781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774697873052217355957041 1331023404789163016967781)
                ·
                  refine ⟨249566888397968065681459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331023404789163016967781 249566888397968065681459)
                  ·
                    rfl

theorem cell21_1093567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_1093567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093567 prefixEnd_1093567 := by exact prefixLift 1093567
  have htrace : WordTrace (prefixWord ++ tailWord_1093567) baseStart_1093567 baseEnd_1093567 := by
    simpa [prefixWord, tailWord_1093567, baseEnd_1093567] using wordTrace_append hprefix tailTrace_1093567
  have hstable : (prefixWord ++ tailWord_1093567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093567).length < 2 ^ (prefixWord ++ tailWord_1093567).sum := by decide
  have hdescent : baseEnd_1093567 < baseStart_1093567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093629 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1093629 : Nat := 118140960795 + 1093629 * 2 ^ 59
def prefixEnd_1093629 : Nat := 4983230072969 + 3 ^ 40 * 1093629 * 2
def baseEnd_1093629 : Nat := 249581037642669735647999

theorem tailTrace_1093629 : CollatzResearch.WordTrace tailWord_1093629 prefixEnd_1093629 249581037642669735647999 := by
  unfold tailWord_1093629
  simp only [CollatzResearch.WordTrace]
  refine ⟨39887926554976384808235941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26591951036650923205490627 39887926554976384808235941)
  ·
    refine ⟨7478986229058072151544239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39887926554976384808235941 7478986229058072151544239)
    ·
      refine ⟨11218479343587108227316359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478986229058072151544239 11218479343587108227316359)
      ·
        refine ⟨16827719015380662340974539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218479343587108227316359 16827719015380662340974539)
        ·
          refine ⟨25241578523070993511461809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16827719015380662340974539 25241578523070993511461809)
          ·
            refine ⟨18931183892303245133596357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25241578523070993511461809 18931183892303245133596357)
            ·
              refine ⟨3549596979806858462549317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18931183892303245133596357 3549596979806858462549317)
              ·
                refine ⟨665549433713785961727997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3549596979806858462549317 665549433713785961727997)
                ·
                  refine ⟨249581037642669735647999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665549433713785961727997 249581037642669735647999)
                  ·
                    rfl

theorem cell21_1093629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1093629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093629 prefixEnd_1093629 := by exact prefixLift 1093629
  have htrace : WordTrace (prefixWord ++ tailWord_1093629) baseStart_1093629 baseEnd_1093629 := by
    simpa [prefixWord, tailWord_1093629, baseEnd_1093629] using wordTrace_append hprefix tailTrace_1093629
  have hstable : (prefixWord ++ tailWord_1093629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093629).length < 2 ^ (prefixWord ++ tailWord_1093629).sum := by decide
  have hdescent : baseEnd_1093629 < baseStart_1093629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093674 : List Nat := [3, 1, 4, 1, 2, 3, 7]
def baseStart_1093674 : Nat := 118140960795 + 1093674 * 2 ^ 59
def prefixEnd_1093674 : Nat := 4983230072969 + 3 ^ 40 * 1093674 * 2
def baseEnd_1093674 : Nat := 27732367472862184155323

theorem tailTrace_1093674 : CollatzResearch.WordTrace tailWord_1093674 prefixEnd_1093674 27732367472862184155323 := by
  unfold tailWord_1093674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972391959953339373406019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26593045226542238329082717 9972391959953339373406019)
  ·
    refine ⟨14958587939930009060109029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9972391959953339373406019 14958587939930009060109029)
    ·
      refine ⟨2804735238736876698770443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14958587939930009060109029 2804735238736876698770443)
      ·
        refine ⟨4207102858105315048155665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804735238736876698770443 4207102858105315048155665)
        ·
          refine ⟨3155327143578986286116749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207102858105315048155665 3155327143578986286116749)
          ·
            refine ⟨1183247678842119857293781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155327143578986286116749 1183247678842119857293781)
            ·
              refine ⟨27732367472862184155323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1183247678842119857293781 27732367472862184155323)
              ·
                rfl

theorem cell21_1093674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 7].length) (baseStart_1093674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093674 prefixEnd_1093674 := by exact prefixLift 1093674
  have htrace : WordTrace (prefixWord ++ tailWord_1093674) baseStart_1093674 baseEnd_1093674 := by
    simpa [prefixWord, tailWord_1093674, baseEnd_1093674] using wordTrace_append hprefix tailTrace_1093674
  have hstable : (prefixWord ++ tailWord_1093674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093674).length < 2 ^ (prefixWord ++ tailWord_1093674).sum := by decide
  have hdescent : baseEnd_1093674 < baseStart_1093674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093694 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1093694 : Nat := 118140960795 + 1093694 * 2 ^ 59
def prefixEnd_1093694 : Nat := 4983230072969 + 3 ^ 40 * 1093694 * 2
def baseEnd_1093694 : Nat := 249595871528244067064533

theorem tailTrace_1093694 : CollatzResearch.WordTrace tailWord_1093694 prefixEnd_1093694 249595871528244067064533 := by
  unfold tailWord_1093694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986287162467612613669017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26593531533160600606234757 4986287162467612613669017)
  ·
    refine ⟨3739715371850709460251763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4986287162467612613669017 3739715371850709460251763)
    ·
      refine ⟨5609573057776064190377645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739715371850709460251763 5609573057776064190377645)
      ·
        refine ⟨2103589896666024071391617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5609573057776064190377645 2103589896666024071391617)
        ·
          refine ⟨1577692422499518053543713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103589896666024071391617 1577692422499518053543713)
          ·
            refine ⟨1183269316874638540157785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577692422499518053543713 1183269316874638540157785)
            ·
              refine ⟨887451987655978905118339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183269316874638540157785 887451987655978905118339)
              ·
                refine ⟨1331177981483968357677509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887451987655978905118339 1331177981483968357677509)
                ·
                  refine ⟨249595871528244067064533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331177981483968357677509 249595871528244067064533)
                  ·
                    rfl

theorem cell21_1093694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1093694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093694 prefixEnd_1093694 := by exact prefixLift 1093694
  have htrace : WordTrace (prefixWord ++ tailWord_1093694) baseStart_1093694 baseEnd_1093694 := by
    simpa [prefixWord, tailWord_1093694, baseEnd_1093694] using wordTrace_append hprefix tailTrace_1093694
  have hstable : (prefixWord ++ tailWord_1093694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093694).length < 2 ^ (prefixWord ++ tailWord_1093694).sum := by decide
  have hdescent : baseEnd_1093694 < baseStart_1093694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093750 : List Nat := [5, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1093750 : Nat := 118140960795 + 1093750 * 2 ^ 59
def prefixEnd_1093750 : Nat := 4983230072969 + 3 ^ 40 * 1093750 * 2
def baseEnd_1093750 : Nat := 83202883830400138043695

theorem tailTrace_1093750 : CollatzResearch.WordTrace tailWord_1093750 prefixEnd_1093750 83202883830400138043695 := by
  unfold tailWord_1093750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493271236721126404586919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26594893191692014982260469 2493271236721126404586919)
  ·
    refine ⟨3739906855081689606880379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493271236721126404586919 3739906855081689606880379)
    ·
      refine ⟨5609860282622534410320569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739906855081689606880379 5609860282622534410320569)
      ·
        refine ⟨4207395211966900807740427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5609860282622534410320569 4207395211966900807740427)
        ·
          refine ⟨6311092817950351211610641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207395211966900807740427 6311092817950351211610641)
          ·
            refine ⟨4733319613462763408707981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311092817950351211610641 4733319613462763408707981)
            ·
              refine ⟨1774994855048536278265493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4733319613462763408707981 1774994855048536278265493)
              ·
                refine ⟨83202883830400138043695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1774994855048536278265493 83202883830400138043695)
                ·
                  rfl

theorem cell21_1093750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1093750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093750 prefixEnd_1093750 := by exact prefixLift 1093750
  have htrace : WordTrace (prefixWord ++ tailWord_1093750) baseStart_1093750 baseEnd_1093750 := by
    simpa [prefixWord, tailWord_1093750, baseEnd_1093750] using wordTrace_append hprefix tailTrace_1093750
  have hstable : (prefixWord ++ tailWord_1093750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093750).length < 2 ^ (prefixWord ++ tailWord_1093750).sum := by decide
  have hdescent : baseEnd_1093750 < baseStart_1093750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093764 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1093764 : Nat := 118140960795 + 1093764 * 2 ^ 59
def prefixEnd_1093764 : Nat := 4983230072969 + 3 ^ 40 * 1093764 * 2
def baseEnd_1093764 : Nat := 249611846481939500897723

theorem tailTrace_1093764 : CollatzResearch.WordTrace tailWord_1093764 prefixEnd_1093764 249611846481939500897723 := by
  unfold tailWord_1093764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19946425204743651432200173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26595233606324868576266897 19946425204743651432200173)
  ·
    refine ⟨7479909451778869287075065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19946425204743651432200173 7479909451778869287075065)
    ·
      refine ⟨5609932088834151965306299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7479909451778869287075065 5609932088834151965306299)
      ·
        refine ⟨8414898133251227947959449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609932088834151965306299 8414898133251227947959449)
        ·
          refine ⟨6311173599938420960969587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414898133251227947959449 6311173599938420960969587)
          ·
            refine ⟨9466760399907631441454381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311173599938420960969587 9466760399907631441454381)
            ·
              refine ⟨3550035149965361790545393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9466760399907631441454381 3550035149965361790545393)
              ·
                refine ⟨2662526362474021342909045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550035149965361790545393 2662526362474021342909045)
                ·
                  refine ⟨249611846481939500897723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2662526362474021342909045 249611846481939500897723)
                  ·
                    rfl

theorem cell21_1093764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1093764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093764 prefixEnd_1093764 := by exact prefixLift 1093764
  have htrace : WordTrace (prefixWord ++ tailWord_1093764) baseStart_1093764 baseEnd_1093764 := by
    simpa [prefixWord, tailWord_1093764, baseEnd_1093764] using wordTrace_append hprefix tailTrace_1093764
  have hstable : (prefixWord ++ tailWord_1093764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093764).length < 2 ^ (prefixWord ++ tailWord_1093764).sum := by decide
  have hdescent : baseEnd_1093764 < baseStart_1093764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093781 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 3]
def baseStart_1093781 : Nat := 118140960795 + 1093781 * 2 ^ 59
def prefixEnd_1093781 : Nat := 4983230072969 + 3 ^ 40 * 1093781 * 2
def baseEnd_1093781 : Nat := 249615726113551249114355

theorem tailTrace_1093781 : CollatzResearch.WordTrace tailWord_1093781 prefixEnd_1093781 249615726113551249114355 := by
  unfold tailWord_1093781
  simp only [CollatzResearch.WordTrace]
  refine ⟨39893470450425714767769197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26595646966950476511846131 39893470450425714767769197)
  ·
    refine ⟨14960051418909643037913449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39893470450425714767769197 14960051418909643037913449)
    ·
      refine ⟨11220038564182232278435087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14960051418909643037913449 11220038564182232278435087)
      ·
        refine ⟨16830057846273348417652631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11220038564182232278435087 16830057846273348417652631)
        ·
          refine ⟨25245086769410022626478947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16830057846273348417652631 25245086769410022626478947)
          ·
            refine ⟨37867630154115033939718421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25245086769410022626478947 37867630154115033939718421)
            ·
              refine ⟨1775045163474142215924301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37867630154115033939718421 1775045163474142215924301)
              ·
                refine ⟨665641936302803330971613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775045163474142215924301 665641936302803330971613)
                ·
                  refine ⟨249615726113551249114355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665641936302803330971613 249615726113551249114355)
                  ·
                    rfl

theorem cell21_1093781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_1093781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093781 prefixEnd_1093781 := by exact prefixLift 1093781
  have htrace : WordTrace (prefixWord ++ tailWord_1093781) baseStart_1093781 baseEnd_1093781 := by
    simpa [prefixWord, tailWord_1093781, baseEnd_1093781] using wordTrace_append hprefix tailTrace_1093781
  have hstable : (prefixWord ++ tailWord_1093781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093781).length < 2 ^ (prefixWord ++ tailWord_1093781).sum := by decide
  have hdescent : baseEnd_1093781 < baseStart_1093781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093871 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_1093871 : Nat := 118140960795 + 1093871 * 2 ^ 59
def prefixEnd_1093871 : Nat := 4983230072969 + 3 ^ 40 * 1093871 * 2
def baseEnd_1093871 : Nat := 249636265339731092614171

theorem tailTrace_1093871 : CollatzResearch.WordTrace tailWord_1093871 prefixEnd_1093871 249636265339731092614171 := by
  unfold tailWord_1093871
  simp only [CollatzResearch.WordTrace]
  refine ⟨39896753020099660138545467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26597835346733106759030311 39896753020099660138545467)
  ·
    refine ⟨59845129530149490207818201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39896753020099660138545467 59845129530149490207818201)
    ·
      refine ⟨44883847147612117655863651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59845129530149490207818201 44883847147612117655863651)
      ·
        refine ⟨67325770721418176483795477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44883847147612117655863651 67325770721418176483795477)
        ·
          refine ⟨3155895502566477022677913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67325770721418176483795477 3155895502566477022677913)
          ·
            refine ⟨2366921626924857767008435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155895502566477022677913 2366921626924857767008435)
            ·
              refine ⟨3550382440387286650512653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366921626924857767008435 3550382440387286650512653)
              ·
                refine ⟨1331393415145232493942245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3550382440387286650512653 1331393415145232493942245)
                ·
                  refine ⟨249636265339731092614171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331393415145232493942245 249636265339731092614171)
                  ·
                    rfl

theorem cell21_1093871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_1093871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093871 prefixEnd_1093871 := by exact prefixLift 1093871
  have htrace : WordTrace (prefixWord ++ tailWord_1093871) baseStart_1093871 baseEnd_1093871 := by
    simpa [prefixWord, tailWord_1093871, baseEnd_1093871] using wordTrace_append hprefix tailTrace_1093871
  have hstable : (prefixWord ++ tailWord_1093871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093871).length < 2 ^ (prefixWord ++ tailWord_1093871).sum := by decide
  have hdescent : baseEnd_1093871 < baseStart_1093871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093944 : List Nat := [2, 1, 2, 1, 3, 1, 2, 9]
def baseStart_1093944 : Nat := 118140960795 + 1093944 * 2 ^ 59
def prefixEnd_1093944 : Nat := 4983230072969 + 3 ^ 40 * 1093944 * 2
def baseEnd_1093944 : Nat := 83217641644766395965785

theorem tailTrace_1093944 : CollatzResearch.WordTrace tailWord_1093944 prefixEnd_1093944 83217641644766395965785 := by
  unfold tailWord_1093944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949707774417596802976443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26599610365890129070635257 19949707774417596802976443)
  ·
    refine ⟨29924561661626395204464665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19949707774417596802976443 29924561661626395204464665)
    ·
      refine ⟨22443421246219796403348499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29924561661626395204464665 22443421246219796403348499)
      ·
        refine ⟨33665131869329694605022749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22443421246219796403348499 33665131869329694605022749)
        ·
          refine ⟨12624424450998635476883531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33665131869329694605022749 12624424450998635476883531)
          ·
            refine ⟨18936636676497953215325297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12624424450998635476883531 18936636676497953215325297)
            ·
              refine ⟨14202477507373464911493973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18936636676497953215325297 14202477507373464911493973)
              ·
                refine ⟨83217641644766395965785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14202477507373464911493973 83217641644766395965785)
                ·
                  rfl

theorem cell21_1093944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_1093944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093944 prefixEnd_1093944 := by exact prefixLift 1093944
  have htrace : WordTrace (prefixWord ++ tailWord_1093944) baseStart_1093944 baseEnd_1093944 := by
    simpa [prefixWord, tailWord_1093944, baseEnd_1093944] using wordTrace_append hprefix tailTrace_1093944
  have hstable : (prefixWord ++ tailWord_1093944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093944).length < 2 ^ (prefixWord ++ tailWord_1093944).sum := by decide
  have hdescent : baseEnd_1093944 < baseStart_1093944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093950 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1093950 : Nat := 118140960795 + 1093950 * 2 ^ 59
def prefixEnd_1093950 : Nat := 4983230072969 + 3 ^ 40 * 1093950 * 2
def baseEnd_1093950 : Nat := 249654294216044510797343

theorem tailTrace_1093950 : CollatzResearch.WordTrace tailWord_1093950 prefixEnd_1093950 249654294216044510797343 := by
  unfold tailWord_1093950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987454298351682078833913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26599756257875637753780869 4987454298351682078833913)
  ·
    refine ⟨3740590723763761559125435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4987454298351682078833913 3740590723763761559125435)
    ·
      refine ⟨5610886085645642338688153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740590723763761559125435 5610886085645642338688153)
      ·
        refine ⟨4208164564234231754016115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5610886085645642338688153 4208164564234231754016115)
        ·
          refine ⟨6312246846351347631024173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208164564234231754016115 6312246846351347631024173)
          ·
            refine ⟨2367092567381755361634065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6312246846351347631024173 2367092567381755361634065)
            ·
              refine ⟨1775319425536316521225549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367092567381755361634065 1775319425536316521225549)
              ·
                refine ⟨665744784576118695459581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775319425536316521225549 665744784576118695459581)
                ·
                  refine ⟨249654294216044510797343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665744784576118695459581 249654294216044510797343)
                  ·
                    rfl

theorem cell21_1093950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1093950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093950 prefixEnd_1093950 := by exact prefixLift 1093950
  have htrace : WordTrace (prefixWord ++ tailWord_1093950) baseStart_1093950 baseEnd_1093950 := by
    simpa [prefixWord, tailWord_1093950, baseEnd_1093950] using wordTrace_append hprefix tailTrace_1093950
  have hstable : (prefixWord ++ tailWord_1093950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093950).length < 2 ^ (prefixWord ++ tailWord_1093950).sum := by decide
  have hdescent : baseEnd_1093950 < baseStart_1093950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093992 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1093992 : Nat := 118140960795 + 1093992 * 2 ^ 59
def prefixEnd_1093992 : Nat := 4983230072969 + 3 ^ 40 * 1093992 * 2
def baseEnd_1093992 : Nat := 249663879188261771097257

theorem tailTrace_1093992 : CollatzResearch.WordTrace tailWord_1093992 prefixEnd_1093992 249663879188261771097257 := by
  unfold tailWord_1093992
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950583126330648901850115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26600777501774198535800153 19950583126330648901850115)
  ·
    refine ⟨29925874689495973352775173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19950583126330648901850115 29925874689495973352775173)
    ·
      refine ⟨5611101504280495003645345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29925874689495973352775173 5611101504280495003645345)
      ·
        refine ⟨4208326128210371252734009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5611101504280495003645345 4208326128210371252734009)
        ·
          refine ⟨3156244596157778439550507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4208326128210371252734009 3156244596157778439550507)
          ·
            refine ⟨4734366894236667659325761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156244596157778439550507 4734366894236667659325761)
            ·
              refine ⟨3550775170677500744494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734366894236667659325761 3550775170677500744494321)
              ·
                refine ⟨2663081378008125558370741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550775170677500744494321 2663081378008125558370741)
                ·
                  refine ⟨249663879188261771097257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663081378008125558370741 249663879188261771097257)
                  ·
                    rfl

theorem cell21_1093992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1093992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1093992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1093992 prefixEnd_1093992 := by exact prefixLift 1093992
  have htrace : WordTrace (prefixWord ++ tailWord_1093992) baseStart_1093992 baseEnd_1093992 := by
    simpa [prefixWord, tailWord_1093992, baseEnd_1093992] using wordTrace_append hprefix tailTrace_1093992
  have hstable : (prefixWord ++ tailWord_1093992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093992).length < 2 ^ (prefixWord ++ tailWord_1093992).sum := by decide
  have hdescent : baseEnd_1093992 < baseStart_1093992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094026 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1094026 : Nat := 118140960795 + 1094026 * 2 ^ 59
def prefixEnd_1094026 : Nat := 4983230072969 + 3 ^ 40 * 1094026 * 2
def baseEnd_1094026 : Nat := 249671638451485267530521

theorem tailTrace_1094026 : CollatzResearch.WordTrace tailWord_1094026 prefixEnd_1094026 249671638451485267530521 := by
  unfold tailWord_1094026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9975601583634530402609483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26601604223025414406958621 9975601583634530402609483)
  ·
    refine ⟨14963402375451795603914225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9975601583634530402609483 14963402375451795603914225)
    ·
      refine ⟨11222551781588846702935669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14963402375451795603914225 11222551781588846702935669)
      ·
        refine ⟨1052114229523954378400219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11222551781588846702935669 1052114229523954378400219)
        ·
          refine ⟨1578171344285931567600329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052114229523954378400219 1578171344285931567600329)
          ·
            refine ⟨1183628508214448675700247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578171344285931567600329 1183628508214448675700247)
            ·
              refine ⟨1775442762321673013550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183628508214448675700247 1775442762321673013550371)
              ·
                refine ⟨2663164143482509520325557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775442762321673013550371 2663164143482509520325557)
                ·
                  refine ⟨249671638451485267530521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663164143482509520325557 249671638451485267530521)
                  ·
                    rfl

theorem cell21_1094026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1094026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094026 prefixEnd_1094026 := by exact prefixLift 1094026
  have htrace : WordTrace (prefixWord ++ tailWord_1094026) baseStart_1094026 baseEnd_1094026 := by
    simpa [prefixWord, tailWord_1094026, baseEnd_1094026] using wordTrace_append hprefix tailTrace_1094026
  have hstable : (prefixWord ++ tailWord_1094026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094026).length < 2 ^ (prefixWord ++ tailWord_1094026).sum := by decide
  have hdescent : baseEnd_1094026 < baseStart_1094026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094040 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_1094040 : Nat := 118140960795 + 1094040 * 2 ^ 59
def prefixEnd_1094040 : Nat := 4983230072969 + 3 ^ 40 * 1094040 * 2
def baseEnd_1094040 : Nat := 249674833442224354297159

theorem tailTrace_1094040 : CollatzResearch.WordTrace tailWord_1094040 prefixEnd_1094040 249674833442224354297159 := by
  unfold tailWord_1094040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19951458478243701000723787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26601944637658268000965049 19951458478243701000723787)
  ·
    refine ⟨29927187717365551501085681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19951458478243701000723787 29927187717365551501085681)
    ·
      refine ⟨22445390788024163625814261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29927187717365551501085681 22445390788024163625814261)
      ·
        refine ⟨2104255386377265339920087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22445390788024163625814261 2104255386377265339920087)
        ·
          refine ⟨3156383079565898009880131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104255386377265339920087 3156383079565898009880131)
          ·
            refine ⟨4734574619348847014820197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156383079565898009880131 4734574619348847014820197)
            ·
              refine ⟨887732741127908815278787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4734574619348847014820197 887732741127908815278787)
              ·
                refine ⟨1331599111691863222918181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887732741127908815278787 1331599111691863222918181)
                ·
                  refine ⟨249674833442224354297159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331599111691863222918181 249674833442224354297159)
                  ·
                    rfl

theorem cell21_1094040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_1094040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094040 prefixEnd_1094040 := by exact prefixLift 1094040
  have htrace : WordTrace (prefixWord ++ tailWord_1094040) baseStart_1094040 baseEnd_1094040 := by
    simpa [prefixWord, tailWord_1094040, baseEnd_1094040] using wordTrace_append hprefix tailTrace_1094040
  have hstable : (prefixWord ++ tailWord_1094040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094040).length < 2 ^ (prefixWord ++ tailWord_1094040).sum := by decide
  have hdescent : baseEnd_1094040 < baseStart_1094040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094113 : List Nat := [1, 2, 3, 1, 2, 2, 5, 5]
def baseStart_1094113 : Nat := 118140960795 + 1094113 * 2 ^ 59
def prefixEnd_1094113 : Nat := 4983230072969 + 3 ^ 40 * 1094113 * 2
def baseEnd_1094113 : Nat := 83230497678930816526781

theorem tailTrace_1094113 : CollatzResearch.WordTrace tailWord_1094113 prefixEnd_1094113 83230497678930816526781 := by
  unfold tailWord_1094113
  simp only [CollatzResearch.WordTrace]
  refine ⟨39905579485222935468854993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26603719656815290312569995 39905579485222935468854993)
  ·
    refine ⟨29929184613917201601641245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39905579485222935468854993 29929184613917201601641245)
    ·
      refine ⟨11223444230218950600615467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29929184613917201601641245 11223444230218950600615467)
      ·
        refine ⟨16835166345328425900923201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11223444230218950600615467 16835166345328425900923201)
        ·
          refine ⟨12626374758996319425692401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16835166345328425900923201 12626374758996319425692401)
          ·
            refine ⟨9469781069247239569269301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12626374758996319425692401 9469781069247239569269301)
            ·
              refine ⟨887791975241928709618997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9469781069247239569269301 887791975241928709618997)
              ·
                refine ⟨83230497678930816526781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887791975241928709618997 83230497678930816526781)
                ·
                  rfl

theorem cell21_1094113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].length) (baseStart_1094113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094113 prefixEnd_1094113 := by exact prefixLift 1094113
  have htrace : WordTrace (prefixWord ++ tailWord_1094113) baseStart_1094113 baseEnd_1094113 := by
    simpa [prefixWord, tailWord_1094113, baseEnd_1094113] using wordTrace_append hprefix tailTrace_1094113
  have hstable : (prefixWord ++ tailWord_1094113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094113).length < 2 ^ (prefixWord ++ tailWord_1094113).sum := by decide
  have hdescent : baseEnd_1094113 < baseStart_1094113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094133 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1094133 : Nat := 118140960795 + 1094133 * 2 ^ 59
def prefixEnd_1094133 : Nat := 4983230072969 + 3 ^ 40 * 1094133 * 2
def baseEnd_1094133 : Nat := 249696057309276859246969

theorem tailTrace_1094133 : CollatzResearch.WordTrace tailWord_1094133 prefixEnd_1094133 249696057309276859246969 := by
  unfold tailWord_1094133
  simp only [CollatzResearch.WordTrace]
  refine ⟨39906308945150478884583053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604205963433652589722035 39906308945150478884583053)
  ·
    refine ⟨14964865854431429581718645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39906308945150478884583053 14964865854431429581718645)
    ·
      refine ⟨1402956173852946523286123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14964865854431429581718645 1402956173852946523286123)
      ·
        refine ⟨2104434260779419784929185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402956173852946523286123 2104434260779419784929185)
        ·
          refine ⟨1578325695584564838696889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104434260779419784929185 1578325695584564838696889)
          ·
            refine ⟨1183744271688423629022667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578325695584564838696889 1183744271688423629022667)
            ·
              refine ⟨1775616407532635443534001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183744271688423629022667 1775616407532635443534001)
              ·
                refine ⟨1331712305649476582650501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1775616407532635443534001 1331712305649476582650501)
                ·
                  refine ⟨249696057309276859246969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331712305649476582650501 249696057309276859246969)
                  ·
                    rfl

theorem cell21_1094133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1094133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094133 prefixEnd_1094133 := by exact prefixLift 1094133
  have htrace : WordTrace (prefixWord ++ tailWord_1094133) baseStart_1094133 baseEnd_1094133 := by
    simpa [prefixWord, tailWord_1094133, baseEnd_1094133] using wordTrace_append hprefix tailTrace_1094133
  have hstable : (prefixWord ++ tailWord_1094133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094133).length < 2 ^ (prefixWord ++ tailWord_1094133).sum := by decide
  have hdescent : baseEnd_1094133 < baseStart_1094133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094248 : List Nat := [2, 1, 4, 3, 11]
def baseStart_1094248 : Nat := 118140960795 + 1094248 * 2 ^ 59
def prefixEnd_1094248 : Nat := 4983230072969 + 3 ^ 40 * 1094248 * 2
def baseEnd_1094248 : Nat := 3082991381185953269507

theorem tailTrace_1094248 : CollatzResearch.WordTrace tailWord_1094248 prefixEnd_1094248 3082991381185953269507 := by
  unfold tailWord_1094248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19955251669866926762509699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26607002226489235683346265 19955251669866926762509699)
  ·
    refine ⟨29932877504800390143764549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19955251669866926762509699 29932877504800390143764549)
    ·
      refine ⟨5612414532150073151955853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29932877504800390143764549 5612414532150073151955853)
      ·
        refine ⟨2104655449556277431983445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5612414532150073151955853 2104655449556277431983445)
        ·
          refine ⟨3082991381185953269507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2104655449556277431983445 3082991381185953269507)
          ·
            rfl

theorem cell21_1094248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 11].length) (baseStart_1094248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094248 prefixEnd_1094248 := by exact prefixLift 1094248
  have htrace : WordTrace (prefixWord ++ tailWord_1094248) baseStart_1094248 baseEnd_1094248 := by
    simpa [prefixWord, tailWord_1094248, baseEnd_1094248] using wordTrace_append hprefix tailTrace_1094248
  have hstable : (prefixWord ++ tailWord_1094248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094248).length < 2 ^ (prefixWord ++ tailWord_1094248).sum := by decide
  have hdescent : baseEnd_1094248 < baseStart_1094248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094254 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1094254 : Nat := 118140960795 + 1094254 * 2 ^ 59
def prefixEnd_1094254 : Nat := 4983230072969 + 3 ^ 40 * 1094254 * 2
def baseEnd_1094254 : Nat := 249723671157807537730055

theorem tailTrace_1094254 : CollatzResearch.WordTrace tailWord_1094254 prefixEnd_1094254 249723671157807537730055 := by
  unfold tailWord_1094254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988840272214014568717227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26607148118474744366491877 4988840272214014568717227)
  ·
    refine ⟨7483260408321021853075841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988840272214014568717227 7483260408321021853075841)
    ·
      refine ⟨5612445306240766389806881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7483260408321021853075841 5612445306240766389806881)
      ·
        refine ⟨4209333979680574792355161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5612445306240766389806881 4209333979680574792355161)
        ·
          refine ⟨3157000484760431094266371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209333979680574792355161 3157000484760431094266371)
          ·
            refine ⟨4735500727140646641399557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157000484760431094266371 4735500727140646641399557)
            ·
              refine ⟨887906386338871245262417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4735500727140646641399557 887906386338871245262417)
              ·
                refine ⟨665929789754153433946813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887906386338871245262417 665929789754153433946813)
                ·
                  refine ⟨249723671157807537730055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665929789754153433946813 249723671157807537730055)
                  ·
                    rfl

theorem cell21_1094254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1094254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094254 prefixEnd_1094254 := by exact prefixLift 1094254
  have htrace : WordTrace (prefixWord ++ tailWord_1094254) baseStart_1094254 baseEnd_1094254 := by
    simpa [prefixWord, tailWord_1094254, baseEnd_1094254] using wordTrace_append hprefix tailTrace_1094254
  have hstable : (prefixWord ++ tailWord_1094254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094254).length < 2 ^ (prefixWord ++ tailWord_1094254).sum := by decide
  have hdescent : baseEnd_1094254 < baseStart_1094254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094265 : List Nat := [1, 2, 1, 3, 3, 4, 1, 6]
def baseStart_1094265 : Nat := 118140960795 + 1094265 * 2 ^ 59
def prefixEnd_1094265 : Nat := 4983230072969 + 3 ^ 40 * 1094265 * 2
def baseEnd_1094265 : Nat := 83242060502557987682233

theorem tailTrace_1094265 : CollatzResearch.WordTrace tailWord_1094265 prefixEnd_1094265 83242060502557987682233 := by
  unfold tailWord_1094265
  simp only [CollatzResearch.WordTrace]
  refine ⟨39911123380672265428388249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26607415587114843618925499 39911123380672265428388249)
  ·
    refine ⟨29933342535504199071291187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39911123380672265428388249 29933342535504199071291187)
    ·
      refine ⟨44900013803256298606936781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29933342535504199071291187 44900013803256298606936781)
      ·
        refine ⟨16837505176221111977601293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44900013803256298606936781 16837505176221111977601293)
        ·
          refine ⟨6314064441082916991600485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16837505176221111977601293 6314064441082916991600485)
          ·
            refine ⟨1183887082703046935925091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6314064441082916991600485 1183887082703046935925091)
            ·
              refine ⟨1775830624054570403887637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183887082703046935925091 1775830624054570403887637)
              ·
                refine ⟨83242060502557987682233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1775830624054570403887637 83242060502557987682233)
                ·
                  rfl

theorem cell21_1094265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_1094265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094265 prefixEnd_1094265 := by exact prefixLift 1094265
  have htrace : WordTrace (prefixWord ++ tailWord_1094265) baseStart_1094265 baseEnd_1094265 := by
    simpa [prefixWord, tailWord_1094265, baseEnd_1094265] using wordTrace_append hprefix tailTrace_1094265
  have hstable : (prefixWord ++ tailWord_1094265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094265).length < 2 ^ (prefixWord ++ tailWord_1094265).sum := by decide
  have hdescent : baseEnd_1094265 < baseStart_1094265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094279 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_1094279 : Nat := 118140960795 + 1094279 * 2 ^ 59
def prefixEnd_1094279 : Nat := 4983230072969 + 3 ^ 40 * 1094279 * 2
def baseEnd_1094279 : Nat := 249729376498413049813337

theorem tailTrace_1094279 : CollatzResearch.WordTrace tailWord_1094279 prefixEnd_1094279 249729376498413049813337 := by
  unfold tailWord_1094279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39911634002621545819397891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26607756001747697212931927 39911634002621545819397891)
  ·
    refine ⟨59867451003932318729096837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39911634002621545819397891 59867451003932318729096837)
    ·
      refine ⟨11225147063237309761705657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59867451003932318729096837 11225147063237309761705657)
      ·
        refine ⟨8418860297427982321279243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11225147063237309761705657 8418860297427982321279243)
        ·
          refine ⟨12628290446141973481918865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8418860297427982321279243 12628290446141973481918865)
          ·
            refine ⟨9471217834606480111439149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12628290446141973481918865 9471217834606480111439149)
            ·
              refine ⟨3551706687977430041789681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9471217834606480111439149 3551706687977430041789681)
              ·
                refine ⟨2663780015983072531342261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551706687977430041789681 2663780015983072531342261)
                ·
                  refine ⟨249729376498413049813337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663780015983072531342261 249729376498413049813337)
                  ·
                    rfl

theorem cell21_1094279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_1094279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094279 prefixEnd_1094279 := by exact prefixLift 1094279
  have htrace : WordTrace (prefixWord ++ tailWord_1094279) baseStart_1094279 baseEnd_1094279 := by
    simpa [prefixWord, tailWord_1094279, baseEnd_1094279] using wordTrace_append hprefix tailTrace_1094279
  have hstable : (prefixWord ++ tailWord_1094279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094279).length < 2 ^ (prefixWord ++ tailWord_1094279).sum := by decide
  have hdescent : baseEnd_1094279 < baseStart_1094279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094282 : List Nat := [3, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1094282 : Nat := 118140960795 + 1094282 * 2 ^ 59
def prefixEnd_1094282 : Nat := 4983230072969 + 3 ^ 40 * 1094282 * 2
def baseEnd_1094282 : Nat := 83243353713095237087777

theorem tailTrace_1094282 : CollatzResearch.WordTrace tailWord_1094282 prefixEnd_1094282 83243353713095237087777 := by
  unfold tailWord_1094282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9977935855402669332939275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26607828947740451554504733 9977935855402669332939275)
  ·
    refine ⟨14966903783104003999408913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9977935855402669332939275 14966903783104003999408913)
    ·
      refine ⟨11225177837328002999556685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14966903783104003999408913 11225177837328002999556685)
      ·
        refine ⟨4209441688998001124833757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11225177837328002999556685 4209441688998001124833757)
        ·
          refine ⟨1578540633374250421812659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4209441688998001124833757 1578540633374250421812659)
          ·
            refine ⟨2367810950061375632718989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578540633374250421812659 2367810950061375632718989)
            ·
              refine ⟨887929106273015862269621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2367810950061375632718989 887929106273015862269621)
              ·
                refine ⟨83243353713095237087777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887929106273015862269621 83243353713095237087777)
                ·
                  rfl

theorem cell21_1094282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1094282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094282 prefixEnd_1094282 := by exact prefixLift 1094282
  have htrace : WordTrace (prefixWord ++ tailWord_1094282) baseStart_1094282 baseEnd_1094282 := by
    simpa [prefixWord, tailWord_1094282, baseEnd_1094282] using wordTrace_append hprefix tailTrace_1094282
  have hstable : (prefixWord ++ tailWord_1094282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094282).length < 2 ^ (prefixWord ++ tailWord_1094282).sum := by decide
  have hdescent : baseEnd_1094282 < baseStart_1094282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094372 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1094372 : Nat := 118140960795 + 1094372 * 2 ^ 59
def prefixEnd_1094372 : Nat := 4983230072969 + 3 ^ 40 * 1094372 * 2
def baseEnd_1094372 : Nat := 249750600365465554763147

theorem tailTrace_1094372 : CollatzResearch.WordTrace tailWord_1094372 prefixEnd_1094372 249750600365465554763147 := by
  unfold tailWord_1094372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957512995642311351266685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26610017327523081801688913 19957512995642311351266685)
  ·
    refine ⟨7484067373365866756725007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19957512995642311351266685 7484067373365866756725007)
    ·
      refine ⟨11226101060048800135087511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484067373365866756725007 11226101060048800135087511)
      ·
        refine ⟨16839151590073200202631267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11226101060048800135087511 16839151590073200202631267)
        ·
          refine ⟨25258727385109800303946901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16839151590073200202631267 25258727385109800303946901)
          ·
            refine ⟨1184002846177021889247511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25258727385109800303946901 1184002846177021889247511)
            ·
              refine ⟨1776004269265532833871267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184002846177021889247511 1776004269265532833871267)
              ·
                refine ⟨2664006403898299250806901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776004269265532833871267 2664006403898299250806901)
                ·
                  refine ⟨249750600365465554763147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664006403898299250806901 249750600365465554763147)
                  ·
                    rfl

theorem cell21_1094372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1094372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094372 prefixEnd_1094372 := by exact prefixLift 1094372
  have htrace : WordTrace (prefixWord ++ tailWord_1094372) baseStart_1094372 baseEnd_1094372 := by
    simpa [prefixWord, tailWord_1094372, baseEnd_1094372] using wordTrace_append hprefix tailTrace_1094372
  have hstable : (prefixWord ++ tailWord_1094372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094372).length < 2 ^ (prefixWord ++ tailWord_1094372).sum := by decide
  have hdescent : baseEnd_1094372 < baseStart_1094372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094423 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 3]
def baseStart_1094423 : Nat := 118140960795 + 1094423 * 2 ^ 59
def prefixEnd_1094423 : Nat := 4983230072969 + 3 ^ 40 * 1094423 * 2
def baseEnd_1094423 : Nat := 249762239260300799413043

theorem tailTrace_1094423 : CollatzResearch.WordTrace tailWord_1094423 prefixEnd_1094423 249762239260300799413043 := by
  unfold tailWord_1094423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39916886114099858412639923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26611257409399905608426615 39916886114099858412639923)
  ·
    refine ⟨59875329171149787618959885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39916886114099858412639923 59875329171149787618959885)
    ·
      refine ⟨22453248439181170357109957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59875329171149787618959885 22453248439181170357109957)
      ·
        refine ⟨4209984082346469441958117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22453248439181170357109957 4209984082346469441958117)
        ·
          refine ⟨789372015439963020367147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4209984082346469441958117 789372015439963020367147)
          ·
            refine ⟨1184058023159944530550721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789372015439963020367147 1184058023159944530550721)
            ·
              refine ⟨888043517369958397913041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184058023159944530550721 888043517369958397913041)
              ·
                refine ⟨666032638027468798434781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888043517369958397913041 666032638027468798434781)
                ·
                  refine ⟨249762239260300799413043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666032638027468798434781 249762239260300799413043)
                  ·
                    rfl

theorem cell21_1094423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].length) (baseStart_1094423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094423 prefixEnd_1094423 := by exact prefixLift 1094423
  have htrace : WordTrace (prefixWord ++ tailWord_1094423) baseStart_1094423 baseEnd_1094423 := by
    simpa [prefixWord, tailWord_1094423, baseEnd_1094423] using wordTrace_append hprefix tailTrace_1094423
  have hstable : (prefixWord ++ tailWord_1094423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094423).length < 2 ^ (prefixWord ++ tailWord_1094423).sum := by decide
  have hdescent : baseEnd_1094423 < baseStart_1094423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094476 : List Nat := [2, 2, 1, 3, 3, 2, 8]
def baseStart_1094476 : Nat := 118140960795 + 1094476 * 2 ^ 59
def prefixEnd_1094476 : Nat := 4983230072969 + 3 ^ 40 * 1094476 * 2
def baseEnd_1094476 : Nat := 27752703842487165003289

theorem tailTrace_1094476 : CollatzResearch.WordTrace tailWord_1094476 prefixEnd_1094476 27752703842487165003289 := by
  unfold tailWord_1094476
  simp only [CollatzResearch.WordTrace]
  refine ⟨19959409591453924232159641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26612546121938565642879521 19959409591453924232159641)
  ·
    refine ⟨14969557193590443174119731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19959409591453924232159641 14969557193590443174119731)
    ·
      refine ⟨22454335790385664761179597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14969557193590443174119731 22454335790385664761179597)
      ·
        refine ⟨8420375921394624285442349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22454335790385664761179597 8420375921394624285442349)
        ·
          refine ⟨3157640970522984107040881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8420375921394624285442349 3157640970522984107040881)
          ·
            refine ⟨2368230727892238080280661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157640970522984107040881 2368230727892238080280661)
            ·
              refine ⟨27752703842487165003289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2368230727892238080280661 27752703842487165003289)
              ·
                rfl

theorem cell21_1094476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 8].length) (baseStart_1094476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094476 prefixEnd_1094476 := by exact prefixLift 1094476
  have htrace : WordTrace (prefixWord ++ tailWord_1094476) baseStart_1094476 baseEnd_1094476 := by
    simpa [prefixWord, tailWord_1094476, baseEnd_1094476] using wordTrace_append hprefix tailTrace_1094476
  have hstable : (prefixWord ++ tailWord_1094476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094476).length < 2 ^ (prefixWord ++ tailWord_1094476).sum := by decide
  have hdescent : baseEnd_1094476 < baseStart_1094476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094521 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_1094521 : Nat := 118140960795 + 1094521 * 2 ^ 59
def prefixEnd_1094521 : Nat := 4983230072969 + 3 ^ 40 * 1094521 * 2
def baseEnd_1094521 : Nat := 249784604195474406779509

theorem tailTrace_1094521 : CollatzResearch.WordTrace tailWord_1094521 prefixEnd_1094521 249784604195474406779509 := by
  unfold tailWord_1094521
  simp only [CollatzResearch.WordTrace]
  refine ⟨39920460467744821149707417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26613640311829880766471611 39920460467744821149707417)
  ·
    refine ⟨29940345350808615862280563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39920460467744821149707417 29940345350808615862280563)
    ·
      refine ⟨44910518026212923793420845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29940345350808615862280563 44910518026212923793420845)
      ·
        refine ⟨16841444259829846422532817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44910518026212923793420845 16841444259829846422532817)
        ·
          refine ⟨12631083194872384816899613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16841444259829846422532817 12631083194872384816899613)
          ·
            refine ⟨4736656198077144306337355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12631083194872384816899613 4736656198077144306337355)
            ·
              refine ⟨7104984297115716459506033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736656198077144306337355 7104984297115716459506033)
              ·
                refine ⟨5328738222836787344629525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104984297115716459506033 5328738222836787344629525)
                ·
                  refine ⟨249784604195474406779509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5328738222836787344629525 249784604195474406779509)
                  ·
                    rfl

theorem cell21_1094521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_1094521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094521 prefixEnd_1094521 := by exact prefixLift 1094521
  have htrace : WordTrace (prefixWord ++ tailWord_1094521) baseStart_1094521 baseEnd_1094521 := by
    simpa [prefixWord, tailWord_1094521, baseEnd_1094521] using wordTrace_append hprefix tailTrace_1094521
  have hstable : (prefixWord ++ tailWord_1094521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094521).length < 2 ^ (prefixWord ++ tailWord_1094521).sum := by decide
  have hdescent : baseEnd_1094521 < baseStart_1094521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094538 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1094538 : Nat := 118140960795 + 1094538 * 2 ^ 59
def prefixEnd_1094538 : Nat := 4983230072969 + 3 ^ 40 * 1094538 * 2
def baseEnd_1094538 : Nat := 249788483827086154996141

theorem tailTrace_1094538 : CollatzResearch.WordTrace tailWord_1094538 prefixEnd_1094538 249788483827086154996141 := by
  unfold tailWord_1094538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980270127170808263269067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26614053672455488702050845 9980270127170808263269067)
  ·
    refine ⟨14970405190756212394903601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980270127170808263269067 14970405190756212394903601)
    ·
      refine ⟨11227803893067159296177701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14970405190756212394903601 11227803893067159296177701)
      ·
        refine ⟨2105213229950092368033319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11227803893067159296177701 2105213229950092368033319)
        ·
          refine ⟨3157819844925138552049979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105213229950092368033319 3157819844925138552049979)
          ·
            refine ⟨4736729767387707828074969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157819844925138552049979 4736729767387707828074969)
            ·
              refine ⟨3552547325540780871056227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736729767387707828074969 3552547325540780871056227)
              ·
                refine ⟨5328820988311171306584341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552547325540780871056227 5328820988311171306584341)
                ·
                  refine ⟨249788483827086154996141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5328820988311171306584341 249788483827086154996141)
                  ·
                    rfl

theorem cell21_1094538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1094538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094538 prefixEnd_1094538 := by exact prefixLift 1094538
  have htrace : WordTrace (prefixWord ++ tailWord_1094538) baseStart_1094538 baseEnd_1094538 := by
    simpa [prefixWord, tailWord_1094538, baseEnd_1094538] using wordTrace_append hprefix tailTrace_1094538
  have hstable : (prefixWord ++ tailWord_1094538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094538).length < 2 ^ (prefixWord ++ tailWord_1094538).sum := by decide
  have hdescent : baseEnd_1094538 < baseStart_1094538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094673 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1094673 : Nat := 118140960795 + 1094673 * 2 ^ 59
def prefixEnd_1094673 : Nat := 4983230072969 + 3 ^ 40 * 1094673 * 2
def baseEnd_1094673 : Nat := 249819292666355920245865

theorem tailTrace_1094673 : CollatzResearch.WordTrace tailWord_1094673 prefixEnd_1094673 249819292666355920245865 := by
  unfold tailWord_1094673
  simp only [CollatzResearch.WordTrace]
  refine ⟨39926004363194151109240673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26617336242129434072827115 39926004363194151109240673)
  ·
    refine ⟨29944503272395613331930505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39926004363194151109240673 29944503272395613331930505)
    ·
      refine ⟨22458377454296709998947879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29944503272395613331930505 22458377454296709998947879)
      ·
        refine ⟨33687566181445064998421819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22458377454296709998947879 33687566181445064998421819)
        ·
          refine ⟨50531349272167597497632729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33687566181445064998421819 50531349272167597497632729)
          ·
            refine ⟨37898511954125698123224547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50531349272167597497632729 37898511954125698123224547)
            ·
              refine ⟨56847767931188547184836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37898511954125698123224547 56847767931188547184836821)
              ·
                refine ⟨1332369560887231574644613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56847767931188547184836821 1332369560887231574644613)
                ·
                  refine ⟨249819292666355920245865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332369560887231574644613 249819292666355920245865)
                  ·
                    rfl

theorem cell21_1094673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1094673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094673 prefixEnd_1094673 := by exact prefixLift 1094673
  have htrace : WordTrace (prefixWord ++ tailWord_1094673) baseStart_1094673 baseEnd_1094673 := by
    simpa [prefixWord, tailWord_1094673, baseEnd_1094673] using wordTrace_append hprefix tailTrace_1094673
  have hstable : (prefixWord ++ tailWord_1094673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094673).length < 2 ^ (prefixWord ++ tailWord_1094673).sum := by decide
  have hdescent : baseEnd_1094673 < baseStart_1094673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094710 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1094710 : Nat := 118140960795 + 1094710 * 2 ^ 59
def prefixEnd_1094710 : Nat := 4983230072969 + 3 ^ 40 * 1094710 * 2
def baseEnd_1094710 : Nat := 249827736570452078129123

theorem tailTrace_1094710 : CollatzResearch.WordTrace tailWord_1094710 prefixEnd_1094710 249827736570452078129123 := by
  unfold tailWord_1094710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495459616503756651771099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26618235909373404285558389 2495459616503756651771099)
  ·
    refine ⟨3743189424755634977656649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495459616503756651771099 3743189424755634977656649)
    ·
      refine ⟨2807392068566726233242487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3743189424755634977656649 2807392068566726233242487)
      ·
        refine ⟨4211088102850089349863731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807392068566726233242487 4211088102850089349863731)
        ·
          refine ⟨6316632154275134024795597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211088102850089349863731 6316632154275134024795597)
          ·
            refine ⟨2368737057853175259298349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6316632154275134024795597 2368737057853175259298349)
            ·
              refine ⟨888276396694940722236881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368737057853175259298349 888276396694940722236881)
              ·
                refine ⟨666207297521205541677661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888276396694940722236881 666207297521205541677661)
                ·
                  refine ⟨249827736570452078129123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666207297521205541677661 249827736570452078129123)
                  ·
                    rfl

theorem cell21_1094710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1094710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094710 prefixEnd_1094710 := by exact prefixLift 1094710
  have htrace : WordTrace (prefixWord ++ tailWord_1094710) baseStart_1094710 baseEnd_1094710 := by
    simpa [prefixWord, tailWord_1094710, baseEnd_1094710] using wordTrace_append hprefix tailTrace_1094710
  have hstable : (prefixWord ++ tailWord_1094710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094710).length < 2 ^ (prefixWord ++ tailWord_1094710).sum := by decide
  have hdescent : baseEnd_1094710 < baseStart_1094710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094721 : List Nat := [1, 2, 5, 1, 3, 1, 2, 6]
def baseStart_1094721 : Nat := 118140960795 + 1094721 * 2 ^ 59
def prefixEnd_1094721 : Nat := 4983230072969 + 3 ^ 40 * 1094721 * 2
def baseEnd_1094721 : Nat := 83276748973439501148589

theorem tailTrace_1094721 : CollatzResearch.WordTrace tailWord_1094721 prefixEnd_1094721 83276748973439501148589 := by
  unfold tailWord_1094721
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927755067020255306988017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26618503378013503537992011 39927755067020255306988017)
  ·
    refine ⟨29945816300265191480241013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39927755067020255306988017 29945816300265191480241013)
    ·
      refine ⟨2807420278149861701272595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29945816300265191480241013 2807420278149861701272595)
      ·
        refine ⟨4211130417224792551908893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807420278149861701272595 4211130417224792551908893)
        ·
          refine ⟨1579173906459297206965835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4211130417224792551908893 1579173906459297206965835)
          ·
            refine ⟨2368760859688945810448753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579173906459297206965835 2368760859688945810448753)
            ·
              refine ⟨1776570644766709357836565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368760859688945810448753 1776570644766709357836565)
              ·
                refine ⟨83276748973439501148589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1776570644766709357836565 83276748973439501148589)
                ·
                  rfl

theorem cell21_1094721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_1094721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094721 prefixEnd_1094721 := by exact prefixLift 1094721
  have htrace : WordTrace (prefixWord ++ tailWord_1094721) baseStart_1094721 baseEnd_1094721 := by
    simpa [prefixWord, tailWord_1094721, baseEnd_1094721] using wordTrace_append hprefix tailTrace_1094721
  have hstable : (prefixWord ++ tailWord_1094721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094721).length < 2 ^ (prefixWord ++ tailWord_1094721).sum := by decide
  have hdescent : baseEnd_1094721 < baseStart_1094721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094766 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1094766 : Nat := 118140960795 + 1094766 * 2 ^ 59
def prefixEnd_1094766 : Nat := 4983230072969 + 3 ^ 40 * 1094766 * 2
def baseEnd_1094766 : Nat := 249840516533408425195675

theorem tailTrace_1094766 : CollatzResearch.WordTrace tailWord_1094766 prefixEnd_1094766 249840516533408425195675 := by
  unfold tailWord_1094766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991174543982153499047019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26619597567904818661584101 4991174543982153499047019)
  ·
    refine ⟨7486761815973230248570529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4991174543982153499047019 7486761815973230248570529)
    ·
      refine ⟨5615071361979922686427897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7486761815973230248570529 5615071361979922686427897)
      ·
        refine ⟨4211303521484942014820923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615071361979922686427897 4211303521484942014820923)
        ·
          refine ⟨6316955282227413022231385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211303521484942014820923 6316955282227413022231385)
          ·
            refine ⟨4737716461670559766673539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6316955282227413022231385 4737716461670559766673539)
            ·
              refine ⟨7106574692505839650010309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737716461670559766673539 7106574692505839650010309)
              ·
                refine ⟨1332482754844844934376933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7106574692505839650010309 1332482754844844934376933)
                ·
                  refine ⟨249840516533408425195675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332482754844844934376933 249840516533408425195675)
                  ·
                    rfl

theorem cell21_1094766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1094766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094766 prefixEnd_1094766 := by exact prefixLift 1094766
  have htrace : WordTrace (prefixWord ++ tailWord_1094766) baseStart_1094766 baseEnd_1094766 := by
    simpa [prefixWord, tailWord_1094766, baseEnd_1094766] using wordTrace_append hprefix tailTrace_1094766
  have hstable : (prefixWord ++ tailWord_1094766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094766).length < 2 ^ (prefixWord ++ tailWord_1094766).sum := by decide
  have hdescent : baseEnd_1094766 < baseStart_1094766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094839 : List Nat := [1, 1, 3, 1, 4, 1, 2, 8]
def baseStart_1094839 : Nat := 118140960795 + 1094839 * 2 ^ 59
def prefixEnd_1094839 : Nat := 4983230072969 + 3 ^ 40 * 1094839 * 2
def baseEnd_1094839 : Nat := 83285725375992173492953

theorem tailTrace_1094839 : CollatzResearch.WordTrace tailWord_1094839 prefixEnd_1094839 83285725375992173492953 := by
  unfold tailWord_1094839
  simp only [CollatzResearch.WordTrace]
  refine ⟨39932058880592761459783571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26621372587061840973189047 39932058880592761459783571)
  ·
    refine ⟨59898088320889142189675357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39932058880592761459783571 59898088320889142189675357)
    ·
      refine ⟨22461783120333428321128259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59898088320889142189675357 22461783120333428321128259)
      ·
        refine ⟨33692674680500142481692389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22461783120333428321128259 33692674680500142481692389)
        ·
          refine ⟨6317376502593776715317323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33692674680500142481692389 6317376502593776715317323)
          ·
            refine ⟨9476064753890665072975985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6317376502593776715317323 9476064753890665072975985)
            ·
              refine ⟨7107048565417998804731989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9476064753890665072975985 7107048565417998804731989)
              ·
                refine ⟨83285725375992173492953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7107048565417998804731989 83285725375992173492953)
                ·
                  rfl

theorem cell21_1094839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_1094839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094839 prefixEnd_1094839 := by exact prefixLift 1094839
  have htrace : WordTrace (prefixWord ++ tailWord_1094839) baseStart_1094839 baseEnd_1094839 := by
    simpa [prefixWord, tailWord_1094839, baseEnd_1094839] using wordTrace_append hprefix tailTrace_1094839
  have hstable : (prefixWord ++ tailWord_1094839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094839).length < 2 ^ (prefixWord ++ tailWord_1094839).sum := by decide
  have hdescent : baseEnd_1094839 < baseStart_1094839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094856 : List Nat := [2, 1, 3, 1, 2, 1, 6, 5]
def baseStart_1094856 : Nat := 118140960795 + 1094856 * 2 ^ 59
def prefixEnd_1094856 : Nat := 4983230072969 + 3 ^ 40 * 1094856 * 2
def baseEnd_1094856 : Nat := 83287018586529422898497

theorem tailTrace_1094856 : CollatzResearch.WordTrace tailWord_1094856 prefixEnd_1094856 83287018586529422898497 := by
  unfold tailWord_1094856
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966339460765586681576211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26621785947687448908768281 19966339460765586681576211)
  ·
    refine ⟨29949509191148380022364317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19966339460765586681576211 29949509191148380022364317)
    ·
      refine ⟨11231065946680642508386619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29949509191148380022364317 11231065946680642508386619)
      ·
        refine ⟨16846598920020963762579929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11231065946680642508386619 16846598920020963762579929)
        ·
          refine ⟨12634949190015722821934947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16846598920020963762579929 12634949190015722821934947)
          ·
            refine ⟨18952423785023584232902421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12634949190015722821934947 18952423785023584232902421)
            ·
              refine ⟨888394864922980510917301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18952423785023584232902421 888394864922980510917301)
              ·
                refine ⟨83287018586529422898497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888394864922980510917301 83287018586529422898497)
                ·
                  rfl

theorem cell21_1094856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_1094856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094856 prefixEnd_1094856 := by exact prefixLift 1094856
  have htrace : WordTrace (prefixWord ++ tailWord_1094856) baseStart_1094856 baseEnd_1094856 := by
    simpa [prefixWord, tailWord_1094856, baseEnd_1094856] using wordTrace_append hprefix tailTrace_1094856
  have hstable : (prefixWord ++ tailWord_1094856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094856).length < 2 ^ (prefixWord ++ tailWord_1094856).sum := by decide
  have hdescent : baseEnd_1094856 < baseStart_1094856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094862 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_1094862 : Nat := 118140960795 + 1094862 * 2 ^ 59
def prefixEnd_1094862 : Nat := 4983230072969 + 3 ^ 40 * 1094862 * 2
def baseEnd_1094862 : Nat := 249862425041333591595479

theorem tailTrace_1094862 : CollatzResearch.WordTrace tailWord_1094862 prefixEnd_1094862 249862425041333591595479 := by
  unfold tailWord_1094862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991612219938679548483855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26621931839672957591913893 4991612219938679548483855)
  ·
    refine ⟨7487418329908019322725783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4991612219938679548483855 7487418329908019322725783)
    ·
      refine ⟨11231127494862028984088675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487418329908019322725783 11231127494862028984088675)
      ·
        refine ⟨16846691242293043476133013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11231127494862028984088675 16846691242293043476133013)
        ·
          refine ⟨789688651982486412943735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16846691242293043476133013 789688651982486412943735)
          ·
            refine ⟨1184532977973729619415603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789688651982486412943735 1184532977973729619415603)
            ·
              refine ⟨1776799466960594429123405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184532977973729619415603 1776799466960594429123405)
              ·
                refine ⟨666299800110222910921277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1776799466960594429123405 666299800110222910921277)
                ·
                  refine ⟨249862425041333591595479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666299800110222910921277 249862425041333591595479)
                  ·
                    rfl

theorem cell21_1094862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_1094862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094862 prefixEnd_1094862 := by exact prefixLift 1094862
  have htrace : WordTrace (prefixWord ++ tailWord_1094862) baseStart_1094862 baseEnd_1094862 := by
    simpa [prefixWord, tailWord_1094862, baseEnd_1094862] using wordTrace_append hprefix tailTrace_1094862
  have hstable : (prefixWord ++ tailWord_1094862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094862).length < 2 ^ (prefixWord ++ tailWord_1094862).sum := by decide
  have hdescent : baseEnd_1094862 < baseStart_1094862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094915 : List Nat := [1, 1, 1, 3, 2, 4, 2, 7]
def baseStart_1094915 : Nat := 118140960795 + 1094915 * 2 ^ 59
def prefixEnd_1094915 : Nat := 4983230072969 + 3 ^ 40 * 1094915 * 2
def baseEnd_1094915 : Nat := 83291506787805759070679

theorem tailTrace_1094915 : CollatzResearch.WordTrace tailWord_1094915 prefixEnd_1094915 83291506787805759070679 := by
  unfold tailWord_1094915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39934830828317426439550199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26623220552211617626366799 39934830828317426439550199)
  ·
    refine ⟨59902246242476139659325299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39934830828317426439550199 59902246242476139659325299)
    ·
      refine ⟨89853369363714209488987949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59902246242476139659325299 89853369363714209488987949)
      ·
        refine ⟨33695013511392828558370481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89853369363714209488987949 33695013511392828558370481)
        ·
          refine ⟨25271260133544621418777861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33695013511392828558370481 25271260133544621418777861)
          ·
            refine ⟨4738361275039616516020849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25271260133544621418777861 4738361275039616516020849)
            ·
              refine ⟨3553770956279712387015637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738361275039616516020849 3553770956279712387015637)
              ·
                refine ⟨83291506787805759070679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3553770956279712387015637 83291506787805759070679)
                ·
                  rfl

theorem cell21_1094915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_1094915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1094915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1094915 prefixEnd_1094915 := by exact prefixLift 1094915
  have htrace : WordTrace (prefixWord ++ tailWord_1094915) baseStart_1094915 baseEnd_1094915 := by
    simpa [prefixWord, tailWord_1094915, baseEnd_1094915] using wordTrace_append hprefix tailTrace_1094915
  have hstable : (prefixWord ++ tailWord_1094915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094915).length < 2 ^ (prefixWord ++ tailWord_1094915).sum := by decide
  have hdescent : baseEnd_1094915 < baseStart_1094915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095036 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1095036 : Nat := 118140960795 + 1095036 * 2 ^ 59
def prefixEnd_1095036 : Nat := 4983230072969 + 3 ^ 40 * 1095036 * 2
def baseEnd_1095036 : Nat := 249902134211947955695123

theorem tailTrace_1095036 : CollatzResearch.WordTrace tailWord_1095036 prefixEnd_1095036 249902134211947955695123 := by
  unfold tailWord_1095036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969622030439532052352481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26626162707252709403136641 19969622030439532052352481)
  ·
    refine ⟨14977216522829649039264361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19969622030439532052352481 14977216522829649039264361)
    ·
      refine ⟨11232912392122236779448271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14977216522829649039264361 11232912392122236779448271)
      ·
        refine ⟨16849368588183355169172407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11232912392122236779448271 16849368588183355169172407)
        ·
          refine ⟨25274052882275032753758611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16849368588183355169172407 25274052882275032753758611)
          ·
            refine ⟨37911079323412549130637917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25274052882275032753758611 37911079323412549130637917)
            ·
              refine ⟨14216654746279705923989219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37911079323412549130637917 14216654746279705923989219)
              ·
                refine ⟨21324982119419558885983829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14216654746279705923989219 21324982119419558885983829)
                ·
                  refine ⟨249902134211947955695123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21324982119419558885983829 249902134211947955695123)
                  ·
                    rfl

theorem cell21_1095036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1095036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095036 prefixEnd_1095036 := by exact prefixLift 1095036
  have htrace : WordTrace (prefixWord ++ tailWord_1095036) baseStart_1095036 baseEnd_1095036 := by
    simpa [prefixWord, tailWord_1095036, baseEnd_1095036] using wordTrace_append hprefix tailTrace_1095036
  have hstable : (prefixWord ++ tailWord_1095036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095036).length < 2 ^ (prefixWord ++ tailWord_1095036).sum := by decide
  have hdescent : baseEnd_1095036 < baseStart_1095036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095129 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1095129 : Nat := 118140960795 + 1095129 * 2 ^ 59
def prefixEnd_1095129 : Nat := 4983230072969 + 3 ^ 40 * 1095129 * 2
def baseEnd_1095129 : Nat := 249923358079000460644933

theorem tailTrace_1095129 : CollatzResearch.WordTrace tailWord_1095129 prefixEnd_1095129 249923358079000460644933 := by
  unfold tailWord_1095129
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942636049542140987840441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26628424033028093991893627 39942636049542140987840441)
  ·
    refine ⟨29956977037156605740880331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39942636049542140987840441 29956977037156605740880331)
    ·
      refine ⟨44935465555734908611320497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29956977037156605740880331 44935465555734908611320497)
      ·
        refine ⟨33701599166801181458490373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44935465555734908611320497 33701599166801181458490373)
        ·
          refine ⟨6319049843775221523466945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33701599166801181458490373 6319049843775221523466945)
          ·
            refine ⟨4739287382831416142600209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319049843775221523466945 4739287382831416142600209)
            ·
              refine ⟨3554465537123562106950157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739287382831416142600209 3554465537123562106950157)
              ·
                refine ⟨1332924576421335790106309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3554465537123562106950157 1332924576421335790106309)
                ·
                  refine ⟨249923358079000460644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332924576421335790106309 249923358079000460644933)
                  ·
                    rfl

theorem cell21_1095129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1095129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095129 prefixEnd_1095129 := by exact prefixLift 1095129
  have htrace : WordTrace (prefixWord ++ tailWord_1095129) baseStart_1095129 baseEnd_1095129 := by
    simpa [prefixWord, tailWord_1095129, baseEnd_1095129] using wordTrace_append hprefix tailTrace_1095129
  have hstable : (prefixWord ++ tailWord_1095129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095129).length < 2 ^ (prefixWord ++ tailWord_1095129).sum := by decide
  have hdescent : baseEnd_1095129 < baseStart_1095129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095149 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1095149 : Nat := 118140960795 + 1095149 * 2 ^ 59
def prefixEnd_1095149 : Nat := 4983230072969 + 3 ^ 40 * 1095149 * 2
def baseEnd_1095149 : Nat := 249927922351484870311559

theorem tailTrace_1095149 : CollatzResearch.WordTrace tailWord_1095149 prefixEnd_1095149 249927922351484870311559 := by
  unfold tailWord_1095149
  simp only [CollatzResearch.WordTrace]
  refine ⟨39943365509469684403568501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26628910339646456269045667 39943365509469684403568501)
  ·
    refine ⟨3744690516512782912834547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39943365509469684403568501 3744690516512782912834547)
    ·
      refine ⟨5617035774769174369251821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744690516512782912834547 5617035774769174369251821)
      ·
        refine ⟨2106388415538440388469433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5617035774769174369251821 2106388415538440388469433)
        ·
          refine ⟨1579791311653830291352075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2106388415538440388469433 1579791311653830291352075)
          ·
            refine ⟨2369686967480745437028113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579791311653830291352075 2369686967480745437028113)
            ·
              refine ⟨1777265225610559077771085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369686967480745437028113 1777265225610559077771085)
              ·
                refine ⟨666474459603959654164157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777265225610559077771085 666474459603959654164157)
                ·
                  refine ⟨249927922351484870311559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666474459603959654164157 249927922351484870311559)
                  ·
                    rfl

theorem cell21_1095149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1095149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095149 prefixEnd_1095149 := by exact prefixLift 1095149
  have htrace : WordTrace (prefixWord ++ tailWord_1095149) baseStart_1095149 baseEnd_1095149 := by
    simpa [prefixWord, tailWord_1095149, baseEnd_1095149] using wordTrace_append hprefix tailTrace_1095149
  have hstable : (prefixWord ++ tailWord_1095149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095149).length < 2 ^ (prefixWord ++ tailWord_1095149).sum := by decide
  have hdescent : baseEnd_1095149 < baseStart_1095149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095219 : List Nat := [1, 1, 1, 2, 4, 5, 7]
def baseStart_1095219 : Nat := 118140960795 + 1095219 * 2 ^ 59
def prefixEnd_1095219 : Nat := 4983230072969 + 3 ^ 40 * 1095219 * 2
def baseEnd_1095219 : Nat := 27771544145020033793861

theorem tailTrace_1095219 : CollatzResearch.WordTrace tailWord_1095219 prefixEnd_1095219 27771544145020033793861 := by
  unfold tailWord_1095219
  simp only [CollatzResearch.WordTrace]
  refine ⟨39945918619216086358616711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26630612412810724239077807 39945918619216086358616711)
  ·
    refine ⟨59918877928824129537925067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39945918619216086358616711 59918877928824129537925067)
    ·
      refine ⟨89878316893236194306887601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59918877928824129537925067 89878316893236194306887601)
      ·
        refine ⟨67408737669927145730165701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89878316893236194306887601 67408737669927145730165701)
        ·
          refine ⟨12639138313111339824406069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67408737669927145730165701 12639138313111339824406069)
          ·
            refine ⟨1184919216854188108538069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12639138313111339824406069 1184919216854188108538069)
            ·
              refine ⟨27771544145020033793861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1184919216854188108538069 27771544145020033793861)
              ·
                rfl

theorem cell21_1095219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 7].length) (baseStart_1095219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095219 prefixEnd_1095219 := by exact prefixLift 1095219
  have htrace : WordTrace (prefixWord ++ tailWord_1095219) baseStart_1095219 baseEnd_1095219 := by
    simpa [prefixWord, tailWord_1095219, baseEnd_1095219] using wordTrace_append hprefix tailTrace_1095219
  have hstable : (prefixWord ++ tailWord_1095219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095219).length < 2 ^ (prefixWord ++ tailWord_1095219).sum := by decide
  have hdescent : baseEnd_1095219 < baseStart_1095219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095239 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 4]
def baseStart_1095239 : Nat := 118140960795 + 1095239 * 2 ^ 59
def prefixEnd_1095239 : Nat := 4983230072969 + 3 ^ 40 * 1095239 * 2
def baseEnd_1095239 : Nat := 249948461577664713811375

theorem tailTrace_1095239 : CollatzResearch.WordTrace tailWord_1095239 prefixEnd_1095239 249948461577664713811375 := by
  unfold tailWord_1095239
  simp only [CollatzResearch.WordTrace]
  refine ⟨39946648079143629774344771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26631098719429086516229847 39946648079143629774344771)
  ·
    refine ⟨59919972118715444661517157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39946648079143629774344771 59919972118715444661517157)
    ·
      refine ⟨11234994772259145874034467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59919972118715444661517157 11234994772259145874034467)
      ·
        refine ⟨16852492158388718811051701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11234994772259145874034467 16852492158388718811051701)
        ·
          refine ⟨1579921139848942388536097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16852492158388718811051701 1579921139848942388536097)
          ·
            refine ⟨1184940854886706791402073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579921139848942388536097 1184940854886706791402073)
            ·
              refine ⟨888705641165030093551555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184940854886706791402073 888705641165030093551555)
              ·
                refine ⟨1333058461747545140327333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888705641165030093551555 1333058461747545140327333)
                ·
                  refine ⟨249948461577664713811375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333058461747545140327333 249948461577664713811375)
                  ·
                    rfl

theorem cell21_1095239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_1095239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095239 prefixEnd_1095239 := by exact prefixLift 1095239
  have htrace : WordTrace (prefixWord ++ tailWord_1095239) baseStart_1095239 baseEnd_1095239 := by
    simpa [prefixWord, tailWord_1095239, baseEnd_1095239] using wordTrace_append hprefix tailTrace_1095239
  have hstable : (prefixWord ++ tailWord_1095239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095239).length < 2 ^ (prefixWord ++ tailWord_1095239).sum := by decide
  have hdescent : baseEnd_1095239 < baseStart_1095239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095402 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1095402 : Nat := 118140960795 + 1095402 * 2 ^ 59
def prefixEnd_1095402 : Nat := 4983230072969 + 3 ^ 40 * 1095402 * 2
def baseEnd_1095402 : Nat := 249985660398412652594375

theorem tailTrace_1095402 : CollatzResearch.WordTrace tailWord_1095402 prefixEnd_1095402 249985660398412652594375 := by
  unfold tailWord_1095402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9988148294388277153132115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26635062118368739075018973 9988148294388277153132115)
  ·
    refine ⟨14982222441582415729698173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9988148294388277153132115 14982222441582415729698173)
    ·
      refine ⟨5618333415593405898636815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14982222441582415729698173 5618333415593405898636815)
      ·
        refine ⟨8427500123390108847955223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618333415593405898636815 8427500123390108847955223)
        ·
          refine ⟨12641250185085163271932835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427500123390108847955223 12641250185085163271932835)
          ·
            refine ⟨18961875277627744907899253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12641250185085163271932835 18961875277627744907899253)
            ·
              refine ⟨1777675807277601085115555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18961875277627744907899253 1777675807277601085115555)
              ·
                refine ⟨2666513710916401627673333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777675807277601085115555 2666513710916401627673333)
                ·
                  refine ⟨249985660398412652594375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2666513710916401627673333 249985660398412652594375)
                  ·
                    rfl

theorem cell21_1095402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1095402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095402 prefixEnd_1095402 := by exact prefixLift 1095402
  have htrace : WordTrace (prefixWord ++ tailWord_1095402) baseStart_1095402 baseEnd_1095402 := by
    simpa [prefixWord, tailWord_1095402, baseEnd_1095402] using wordTrace_append hprefix tailTrace_1095402
  have hstable : (prefixWord ++ tailWord_1095402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095402).length < 2 ^ (prefixWord ++ tailWord_1095402).sum := by decide
  have hdescent : baseEnd_1095402 < baseStart_1095402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095464 : List Nat := [2, 1, 5, 1, 1, 4, 1, 6]
def baseStart_1095464 : Nat := 118140960795 + 1095464 * 2 ^ 59
def prefixEnd_1095464 : Nat := 4983230072969 + 3 ^ 40 * 1095464 * 2
def baseEnd_1095464 : Nat := 83333269881038107520305

theorem tailTrace_1095464 : CollatzResearch.WordTrace tailWord_1095464 prefixEnd_1095464 83333269881038107520305 := by
  unfold tailWord_1095464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19977427251664246600642723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26636569668885662134190297 19977427251664246600642723)
  ·
    refine ⟨29966140877496369900964085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19977427251664246600642723 29966140877496369900964085)
    ·
      refine ⟨2809325707265284678215383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29966140877496369900964085 2809325707265284678215383)
      ·
        refine ⟨4213988560897927017323075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809325707265284678215383 4213988560897927017323075)
        ·
          refine ⟨6320982841346890525984613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4213988560897927017323075 6320982841346890525984613)
          ·
            refine ⟨1185184282752541973622115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6320982841346890525984613 1185184282752541973622115)
            ·
              refine ⟨1777776424128812960433173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185184282752541973622115 1777776424128812960433173)
              ·
                refine ⟨83333269881038107520305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1777776424128812960433173 83333269881038107520305)
                ·
                  rfl

theorem cell21_1095464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_1095464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095464 prefixEnd_1095464 := by exact prefixLift 1095464
  have htrace : WordTrace (prefixWord ++ tailWord_1095464) baseStart_1095464 baseEnd_1095464 := by
    simpa [prefixWord, tailWord_1095464, baseEnd_1095464] using wordTrace_append hprefix tailTrace_1095464
  have hstable : (prefixWord ++ tailWord_1095464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095464).length < 2 ^ (prefixWord ++ tailWord_1095464).sum := by decide
  have hdescent : baseEnd_1095464 < baseStart_1095464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095481 : List Nat := [1, 2, 1, 7, 1, 1, 3, 5]
def baseStart_1095481 : Nat := 118140960795 + 1095481 * 2 ^ 59
def prefixEnd_1095481 : Nat := 4983230072969 + 3 ^ 40 * 1095481 * 2
def baseEnd_1095481 : Nat := 83334563091575356925849

theorem tailTrace_1095481 : CollatzResearch.WordTrace tailWord_1095481 prefixEnd_1095481 83334563091575356925849 := by
  unfold tailWord_1095481
  simp only [CollatzResearch.WordTrace]
  refine ⟨39955474544266905104654297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26636983029511270069769531 39955474544266905104654297)
  ·
    refine ⟨29966605908200178828490723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39955474544266905104654297 29966605908200178828490723)
    ·
      refine ⟨44949908862300268242736085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29966605908200178828490723 44949908862300268242736085)
      ·
        refine ⟨1053513488960162536939127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 44949908862300268242736085 1053513488960162536939127)
        ·
          refine ⟨1580270233440243805408691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053513488960162536939127 1580270233440243805408691)
          ·
            refine ⟨2370405350160365708113037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580270233440243805408691 2370405350160365708113037)
            ·
              refine ⟨888902006310137140542389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2370405350160365708113037 888902006310137140542389)
              ·
                refine ⟨83334563091575356925849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888902006310137140542389 83334563091575356925849)
                ·
                  rfl

theorem cell21_1095481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].length) (baseStart_1095481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095481 prefixEnd_1095481 := by exact prefixLift 1095481
  have htrace : WordTrace (prefixWord ++ tailWord_1095481) baseStart_1095481 baseEnd_1095481 := by
    simpa [prefixWord, tailWord_1095481, baseEnd_1095481] using wordTrace_append hprefix tailTrace_1095481
  have hstable : (prefixWord ++ tailWord_1095481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095481).length < 2 ^ (prefixWord ++ tailWord_1095481).sum := by decide
  have hdescent : baseEnd_1095481 < baseStart_1095481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095509 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_1095509 : Nat := 118140960795 + 1095509 * 2 ^ 59
def prefixEnd_1095509 : Nat := 4983230072969 + 3 ^ 40 * 1095509 * 2
def baseEnd_1095509 : Nat := 250010079256204244310823

theorem tailTrace_1095509 : CollatzResearch.WordTrace tailWord_1095509 prefixEnd_1095509 250010079256204244310823 := by
  unfold tailWord_1095509
  simp only [CollatzResearch.WordTrace]
  refine ⟨39956495788165465886673581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26637663858776977257782387 39956495788165465886673581)
  ·
    refine ⟨14983685920562049707502593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39956495788165465886673581 14983685920562049707502593)
    ·
      refine ⟨11237764440421537280626945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14983685920562049707502593 11237764440421537280626945)
      ·
        refine ⟨8428323330316152960470209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11237764440421537280626945 8428323330316152960470209)
        ·
          refine ⟨6321242497737114720352657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8428323330316152960470209 6321242497737114720352657)
          ·
            refine ⟨4740931873302836040264493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6321242497737114720352657 4740931873302836040264493)
            ·
              refine ⟨1777849452488563515099185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4740931873302836040264493 1777849452488563515099185)
              ·
                refine ⟨1333387089366422636324389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777849452488563515099185 1333387089366422636324389)
                ·
                  refine ⟨250010079256204244310823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333387089366422636324389 250010079256204244310823)
                  ·
                    rfl

theorem cell21_1095509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_1095509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095509 prefixEnd_1095509 := by exact prefixLift 1095509
  have htrace : WordTrace (prefixWord ++ tailWord_1095509) baseStart_1095509 baseEnd_1095509 := by
    simpa [prefixWord, tailWord_1095509, baseEnd_1095509] using wordTrace_append hprefix tailTrace_1095509
  have hstable : (prefixWord ++ tailWord_1095509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095509).length < 2 ^ (prefixWord ++ tailWord_1095509).sum := by decide
  have hdescent : baseEnd_1095509 < baseStart_1095509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095537 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1095537 : Nat := 118140960795 + 1095537 * 2 ^ 59
def prefixEnd_1095537 : Nat := 4983230072969 + 3 ^ 40 * 1095537 * 2
def baseEnd_1095537 : Nat := 250016469237682417844099

theorem tailTrace_1095537 : CollatzResearch.WordTrace tailWord_1095537 prefixEnd_1095537 250016469237682417844099 := by
  unfold tailWord_1095537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39957517032064026668692865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26638344688042684445795243 39957517032064026668692865)
  ·
    refine ⟨29968137774048020001519649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39957517032064026668692865 29968137774048020001519649)
    ·
      refine ⟨22476103330536015001139737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29968137774048020001519649 22476103330536015001139737)
      ·
        refine ⟨16857077497902011250854803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22476103330536015001139737 16857077497902011250854803)
        ·
          refine ⟨25285616246853016876282205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16857077497902011250854803 25285616246853016876282205)
          ·
            refine ⟨9482106092569881328605827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25285616246853016876282205 9482106092569881328605827)
            ·
              refine ⟨14223159138854821992908741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482106092569881328605827 14223159138854821992908741)
              ·
                refine ⟨2666842338535279123670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14223159138854821992908741 2666842338535279123670389)
                ·
                  refine ⟨250016469237682417844099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2666842338535279123670389 250016469237682417844099)
                  ·
                    rfl

theorem cell21_1095537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1095537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095537 prefixEnd_1095537 := by exact prefixLift 1095537
  have htrace : WordTrace (prefixWord ++ tailWord_1095537) baseStart_1095537 baseEnd_1095537 := by
    simpa [prefixWord, tailWord_1095537, baseEnd_1095537] using wordTrace_append hprefix tailTrace_1095537
  have hstable : (prefixWord ++ tailWord_1095537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095537).length < 2 ^ (prefixWord ++ tailWord_1095537).sum := by decide
  have hdescent : baseEnd_1095537 < baseStart_1095537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095574 : List Nat := [5, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1095574 : Nat := 118140960795 + 1095574 * 2 ^ 59
def prefixEnd_1095574 : Nat := 4983230072969 + 3 ^ 40 * 1095574 * 2
def baseEnd_1095574 : Nat := 83341637713926191909119

theorem tailTrace_1095574 : CollatzResearch.WordTrace tailWord_1095574 prefixEnd_1095574 83341637713926191909119 := by
  unfold tailWord_1095574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497429158308123874236861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26639244355286654658526517 2497429158308123874236861)
  ·
    refine ⟨936535934365546452838823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2497429158308123874236861 936535934365546452838823)
    ·
      refine ⟨1404803901548319679258235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936535934365546452838823 1404803901548319679258235)
      ·
        refine ⟨2107205852322479518887353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404803901548319679258235 2107205852322479518887353)
        ·
          refine ⟨1580404389241859639165515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107205852322479518887353 1580404389241859639165515)
          ·
            refine ⟨2370606583862789458748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580404389241859639165515 2370606583862789458748273)
            ·
              refine ⟨1777954937897092094061205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370606583862789458748273 1777954937897092094061205)
              ·
                refine ⟨83341637713926191909119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1777954937897092094061205 83341637713926191909119)
                ·
                  rfl

theorem cell21_1095574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1095574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095574 prefixEnd_1095574 := by exact prefixLift 1095574
  have htrace : WordTrace (prefixWord ++ tailWord_1095574) baseStart_1095574 baseEnd_1095574 := by
    simpa [prefixWord, tailWord_1095574, baseEnd_1095574] using wordTrace_append hprefix tailTrace_1095574
  have hstable : (prefixWord ++ tailWord_1095574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095574).length < 2 ^ (prefixWord ++ tailWord_1095574).sum := by decide
  have hdescent : baseEnd_1095574 < baseStart_1095574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095678 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1095678 : Nat := 118140960795 + 1095678 * 2 ^ 59
def prefixEnd_1095678 : Nat := 4983230072969 + 3 ^ 40 * 1095678 * 2
def baseEnd_1095678 : Nat := 250048647358697505993811

theorem tailTrace_1095678 : CollatzResearch.WordTrace tailWord_1095678 prefixEnd_1095678 250048647358697505993811 := by
  unfold tailWord_1095678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995332465569150968696961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26641773149702138499717125 4995332465569150968696961)
  ·
    refine ⟨3746499349176863226522721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4995332465569150968696961 3746499349176863226522721)
    ·
      refine ⟨2809874511882647419892041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3746499349176863226522721 2809874511882647419892041)
      ·
        refine ⟨2107405883911985564919031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2809874511882647419892041 2107405883911985564919031)
        ·
          refine ⟨3161108825867978347378547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107405883911985564919031 3161108825867978347378547)
          ·
            refine ⟨4741663238801967521067821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161108825867978347378547 4741663238801967521067821)
            ·
              refine ⟨1778123714550737820400433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4741663238801967521067821 1778123714550737820400433)
              ·
                refine ⟨1333592785913053365300325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778123714550737820400433 1333592785913053365300325)
                ·
                  refine ⟨250048647358697505993811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333592785913053365300325 250048647358697505993811)
                  ·
                    rfl

theorem cell21_1095678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1095678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095678 prefixEnd_1095678 := by exact prefixLift 1095678
  have htrace : WordTrace (prefixWord ++ tailWord_1095678) baseStart_1095678 baseEnd_1095678 := by
    simpa [prefixWord, tailWord_1095678, baseEnd_1095678] using wordTrace_append hprefix tailTrace_1095678
  have hstable : (prefixWord ++ tailWord_1095678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095678).length < 2 ^ (prefixWord ++ tailWord_1095678).sum := by decide
  have hdescent : baseEnd_1095678 < baseStart_1095678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095779 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_1095779 : Nat := 118140960795 + 1095779 * 2 ^ 59
def prefixEnd_1095779 : Nat := 4983230072969 + 3 ^ 40 * 1095779 * 2
def baseEnd_1095779 : Nat := 250071696934743774810271

theorem tailTrace_1095779 : CollatzResearch.WordTrace tailWord_1095779 prefixEnd_1095779 250071696934743774810271 := by
  unfold tailWord_1095779
  simp only [CollatzResearch.WordTrace]
  refine ⟨39966343497187301999002391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26644228998124867999334927 39966343497187301999002391)
  ·
    refine ⟨59949515245780952998503587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39966343497187301999002391 59949515245780952998503587)
    ·
      refine ⟨89924272868671429497755381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59949515245780952998503587 89924272868671429497755381)
      ·
        refine ⟨8430400581437946515414567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89924272868671429497755381 8430400581437946515414567)
        ·
          refine ⟨12645600872156919773121851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430400581437946515414567 12645600872156919773121851)
          ·
            refine ⟨18968401308235379659682777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12645600872156919773121851 18968401308235379659682777)
            ·
              refine ⟨14226300981176534744762083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18968401308235379659682777 14226300981176534744762083)
              ·
                refine ⟨21339451471764802117143125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14226300981176534744762083 21339451471764802117143125)
                ·
                  refine ⟨250071696934743774810271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21339451471764802117143125 250071696934743774810271)
                  ·
                    rfl

theorem cell21_1095779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_1095779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095779 prefixEnd_1095779 := by exact prefixLift 1095779
  have htrace : WordTrace (prefixWord ++ tailWord_1095779) baseStart_1095779 baseEnd_1095779 := by
    simpa [prefixWord, tailWord_1095779, baseEnd_1095779] using wordTrace_append hprefix tailTrace_1095779
  have hstable : (prefixWord ++ tailWord_1095779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095779).length < 2 ^ (prefixWord ++ tailWord_1095779).sum := by decide
  have hdescent : baseEnd_1095779 < baseStart_1095779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095799 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 3]
def baseStart_1095799 : Nat := 118140960795 + 1095799 * 2 ^ 59
def prefixEnd_1095799 : Nat := 4983230072969 + 3 ^ 40 * 1095799 * 2
def baseEnd_1095799 : Nat := 250076261207228184476897

theorem tailTrace_1095799 : CollatzResearch.WordTrace tailWord_1095799 prefixEnd_1095799 250076261207228184476897 := by
  unfold tailWord_1095799
  simp only [CollatzResearch.WordTrace]
  refine ⟨39967072957114845414730451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26644715304743230276486967 39967072957114845414730451)
  ·
    refine ⟨59950609435672268122095677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39967072957114845414730451 59950609435672268122095677)
    ·
      refine ⟨22481478538377100545785879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59950609435672268122095677 22481478538377100545785879)
      ·
        refine ⟨33722217807565650818678819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481478538377100545785879 33722217807565650818678819)
        ·
          refine ⟨50583326711348476228018229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33722217807565650818678819 50583326711348476228018229)
          ·
            refine ⟨4742186879188919646376709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50583326711348476228018229 4742186879188919646376709)
            ·
              refine ⟨889160039847922433695633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4742186879188919646376709 889160039847922433695633)
              ·
                refine ⟨666870029885941825271725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889160039847922433695633 666870029885941825271725)
                ·
                  refine ⟨250076261207228184476897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666870029885941825271725 250076261207228184476897)
                  ·
                    rfl

theorem cell21_1095799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].length) (baseStart_1095799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095799 prefixEnd_1095799 := by exact prefixLift 1095799
  have htrace : WordTrace (prefixWord ++ tailWord_1095799) baseStart_1095799 baseEnd_1095799 := by
    simpa [prefixWord, tailWord_1095799, baseEnd_1095799] using wordTrace_append hprefix tailTrace_1095799
  have hstable : (prefixWord ++ tailWord_1095799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095799).length < 2 ^ (prefixWord ++ tailWord_1095799).sum := by decide
  have hdescent : baseEnd_1095799 < baseStart_1095799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095847 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 4]
def baseStart_1095847 : Nat := 118140960795 + 1095847 * 2 ^ 59
def prefixEnd_1095847 : Nat := 4983230072969 + 3 ^ 40 * 1095847 * 2
def baseEnd_1095847 : Nat := 250087215461190767676799

theorem tailTrace_1095847 : CollatzResearch.WordTrace tailWord_1095847 prefixEnd_1095847 250087215461190767676799 := by
  unfold tailWord_1095847
  simp only [CollatzResearch.WordTrace]
  refine ⟨39968823660940949612477795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26645882440627299741651863 39968823660940949612477795)
  ·
    refine ⟨59953235491411424418716693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39968823660940949612477795 59953235491411424418716693)
    ·
      refine ⟨2810307913659910519627345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59953235491411424418716693 2810307913659910519627345)
      ·
        refine ⟨2107730935244932889720509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810307913659910519627345 2107730935244932889720509)
        ·
          refine ⟨790399100716849833645191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2107730935244932889720509 790399100716849833645191)
          ·
            refine ⟨1185598651075274750467787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790399100716849833645191 1185598651075274750467787)
            ·
              refine ⟨1778397976612912125701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185598651075274750467787 1778397976612912125701681)
              ·
                refine ⟨1333798482459684094276261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778397976612912125701681 1333798482459684094276261)
                ·
                  refine ⟨250087215461190767676799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333798482459684094276261 250087215461190767676799)
                  ·
                    rfl

theorem cell21_1095847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].length) (baseStart_1095847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095847 prefixEnd_1095847 := by exact prefixLift 1095847
  have htrace : WordTrace (prefixWord ++ tailWord_1095847) baseStart_1095847 baseEnd_1095847 := by
    simpa [prefixWord, tailWord_1095847, baseEnd_1095847] using wordTrace_append hprefix tailTrace_1095847
  have hstable : (prefixWord ++ tailWord_1095847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095847).length < 2 ^ (prefixWord ++ tailWord_1095847).sum := by decide
  have hdescent : baseEnd_1095847 < baseStart_1095847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095858 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1095858 : Nat := 118140960795 + 1095858 * 2 ^ 59
def prefixEnd_1095858 : Nat := 4983230072969 + 3 ^ 40 * 1095858 * 2
def baseEnd_1095858 : Nat := 250089725811057192993443

theorem tailTrace_1095858 : CollatzResearch.WordTrace tailWord_1095858 prefixEnd_1095858 250089725811057192993443 := by
  unfold tailWord_1095858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992306215975274622782057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26646149909267398994085485 9992306215975274622782057)
  ·
    refine ⟨7494229661981455967086543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9992306215975274622782057 7494229661981455967086543)
    ·
      refine ⟨11241344492972183950629815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7494229661981455967086543 11241344492972183950629815)
      ·
        refine ⟨16862016739458275925944723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241344492972183950629815 16862016739458275925944723)
        ·
          refine ⟨25293025109187413888917085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862016739458275925944723 25293025109187413888917085)
          ·
            refine ⟨9484884415945280208343907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25293025109187413888917085 9484884415945280208343907)
            ·
              refine ⟨14227326623917920312515861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484884415945280208343907 14227326623917920312515861)
              ·
                refine ⟨666905935496152514649181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14227326623917920312515861 666905935496152514649181)
                ·
                  refine ⟨250089725811057192993443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666905935496152514649181 250089725811057192993443)
                  ·
                    rfl

theorem cell21_1095858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1095858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095858 prefixEnd_1095858 := by exact prefixLift 1095858
  have htrace : WordTrace (prefixWord ++ tailWord_1095858) baseStart_1095858 baseEnd_1095858 := by
    simpa [prefixWord, tailWord_1095858, baseEnd_1095858] using wordTrace_append hprefix tailTrace_1095858
  have hstable : (prefixWord ++ tailWord_1095858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095858).length < 2 ^ (prefixWord ++ tailWord_1095858).sum := by decide
  have hdescent : baseEnd_1095858 < baseStart_1095858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095962 : List Nat := [3, 1, 1, 3, 4, 9]
def baseStart_1095962 : Nat := 118140960795 + 1095962 * 2 ^ 59
def prefixEnd_1095962 : Nat := 4983230072969 + 3 ^ 40 * 1095962 * 2
def baseEnd_1095962 : Nat := 9263461482517634194811

theorem tailTrace_1095962 : CollatzResearch.WordTrace tailWord_1095962 prefixEnd_1095962 9263461482517634194811 := by
  unfold tailWord_1095962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993254513881081063228535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26648678703682882835276093 9993254513881081063228535)
  ·
    refine ⟨14989881770821621594842803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9993254513881081063228535 14989881770821621594842803)
    ·
      refine ⟨22484822656232432392264205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14989881770821621594842803 22484822656232432392264205)
      ·
        refine ⟨8431808496087162147099077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22484822656232432392264205 8431808496087162147099077)
        ·
          refine ⟨1580964093016342902581077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8431808496087162147099077 1580964093016342902581077)
          ·
            refine ⟨9263461482517634194811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1580964093016342902581077 9263461482517634194811)
            ·
              rfl

theorem cell21_1095962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 9].length) (baseStart_1095962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095962 prefixEnd_1095962 := by exact prefixLift 1095962
  have htrace : WordTrace (prefixWord ++ tailWord_1095962) baseStart_1095962 baseEnd_1095962 := by
    simpa [prefixWord, tailWord_1095962, baseEnd_1095962] using wordTrace_append hprefix tailTrace_1095962
  have hstable : (prefixWord ++ tailWord_1095962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095962).length < 2 ^ (prefixWord ++ tailWord_1095962).sum := by decide
  have hdescent : baseEnd_1095962 < baseStart_1095962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095968 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_1095968 : Nat := 118140960795 + 1095968 * 2 ^ 59
def prefixEnd_1095968 : Nat := 4983230072969 + 3 ^ 40 * 1095968 * 2
def baseEnd_1095968 : Nat := 250114829309721446159885

theorem tailTrace_1095968 : CollatzResearch.WordTrace tailWord_1095968 prefixEnd_1095968 250114829309721446159885 := by
  unfold tailWord_1095968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19986618446751293638816279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26648824595668391518421705 19986618446751293638816279)
  ·
    refine ⟨29979927670126940458224419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19986618446751293638816279 29979927670126940458224419)
    ·
      refine ⟨44969891505190410687336629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29979927670126940458224419 44969891505190410687336629)
      ·
        refine ⟨4215927328611601001937809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44969891505190410687336629 4215927328611601001937809)
        ·
          refine ⟨3161945496458700751453357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4215927328611601001937809 3161945496458700751453357)
          ·
            refine ⟨1185729561172012781795009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3161945496458700751453357 1185729561172012781795009)
            ·
              refine ⟨889297170879009586346257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185729561172012781795009 889297170879009586346257)
              ·
                refine ⟨666972878159257189759693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889297170879009586346257 666972878159257189759693)
                ·
                  refine ⟨250114829309721446159885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666972878159257189759693 250114829309721446159885)
                  ·
                    rfl

theorem cell21_1095968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_1095968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095968 prefixEnd_1095968 := by exact prefixLift 1095968
  have htrace : WordTrace (prefixWord ++ tailWord_1095968) baseStart_1095968 baseEnd_1095968 := by
    simpa [prefixWord, tailWord_1095968, baseEnd_1095968] using wordTrace_append hprefix tailTrace_1095968
  have hstable : (prefixWord ++ tailWord_1095968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095968).length < 2 ^ (prefixWord ++ tailWord_1095968).sum := by decide
  have hdescent : baseEnd_1095968 < baseStart_1095968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095993 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1095993 : Nat := 118140960795 + 1095993 * 2 ^ 59
def prefixEnd_1095993 : Nat := 4983230072969 + 3 ^ 40 * 1095993 * 2
def baseEnd_1095993 : Nat := 250120534650326958243167

theorem tailTrace_1095993 : CollatzResearch.WordTrace tailWord_1095993 prefixEnd_1095993 250120534650326958243167 := by
  unfold tailWord_1095993
  simp only [CollatzResearch.WordTrace]
  refine ⟨39974148718412016547292633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26649432478941344364861755 39974148718412016547292633)
  ·
    refine ⟨29980611538809012410469475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39974148718412016547292633 29980611538809012410469475)
    ·
      refine ⟨44970917308213518615704213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29980611538809012410469475 44970917308213518615704213)
      ·
        refine ⟨2108011748822508685111135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44970917308213518615704213 2108011748822508685111135)
        ·
          refine ⟨3162017623233763027666703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108011748822508685111135 3162017623233763027666703)
          ·
            refine ⟨4743026434850644541500055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162017623233763027666703 4743026434850644541500055)
            ·
              refine ⟨7114539652275966812250083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743026434850644541500055 7114539652275966812250083)
              ·
                refine ⟨10671809478413950218375125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114539652275966812250083 10671809478413950218375125)
                ·
                  refine ⟨250120534650326958243167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10671809478413950218375125 250120534650326958243167)
                  ·
                    rfl

theorem cell21_1095993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1095993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1095993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1095993 prefixEnd_1095993 := by exact prefixLift 1095993
  have htrace : WordTrace (prefixWord ++ tailWord_1095993) baseStart_1095993 baseEnd_1095993 := by
    simpa [prefixWord, tailWord_1095993, baseEnd_1095993] using wordTrace_append hprefix tailTrace_1095993
  have hstable : (prefixWord ++ tailWord_1095993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095993).length < 2 ^ (prefixWord ++ tailWord_1095993).sum := by decide
  have hdescent : baseEnd_1095993 < baseStart_1095993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096007 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_1096007 : Nat := 118140960795 + 1096007 * 2 ^ 59
def prefixEnd_1096007 : Nat := 4983230072969 + 3 ^ 40 * 1096007 * 2
def baseEnd_1096007 : Nat := 250123729641066045009805

theorem tailTrace_1096007 : CollatzResearch.WordTrace tailWord_1096007 prefixEnd_1096007 250123729641066045009805 := by
  unfold tailWord_1096007
  simp only [CollatzResearch.WordTrace]
  refine ⟨39974659340361296938302275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26649772893574197958868183 39974659340361296938302275)
  ·
    refine ⟨59961989010541945407453413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39974659340361296938302275 59961989010541945407453413)
    ·
      refine ⟨11242872939476614763897515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59961989010541945407453413 11242872939476614763897515)
      ·
        refine ⟨16864309409214922145846273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11242872939476614763897515 16864309409214922145846273)
        ·
          refine ⟨12648232056911191609384705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16864309409214922145846273 12648232056911191609384705)
          ·
            refine ⟨9486174042683393707038529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12648232056911191609384705 9486174042683393707038529)
            ·
              refine ⟨7114630532012545280278897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9486174042683393707038529 7114630532012545280278897)
              ·
                refine ⟨5335972899009408960209173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7114630532012545280278897 5335972899009408960209173)
                ·
                  refine ⟨250123729641066045009805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5335972899009408960209173 250123729641066045009805)
                  ·
                    rfl

theorem cell21_1096007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_1096007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096007 prefixEnd_1096007 := by exact prefixLift 1096007
  have htrace : WordTrace (prefixWord ++ tailWord_1096007) baseStart_1096007 baseEnd_1096007 := by
    simpa [prefixWord, tailWord_1096007, baseEnd_1096007] using wordTrace_append hprefix tailTrace_1096007
  have hstable : (prefixWord ++ tailWord_1096007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096007).length < 2 ^ (prefixWord ++ tailWord_1096007).sum := by decide
  have hdescent : baseEnd_1096007 < baseStart_1096007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096193 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_1096193 : Nat := 118140960795 + 1096193 * 2 ^ 59
def prefixEnd_1096193 : Nat := 4983230072969 + 3 ^ 40 * 1096193 * 2
def baseEnd_1096193 : Nat := 250166177375171054909425

theorem tailTrace_1096193 : CollatzResearch.WordTrace tailWord_1096193 prefixEnd_1096193 250166177375171054909425 := by
  unfold tailWord_1096193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39981443317687450704573233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26654295545124967136382155 39981443317687450704573233)
  ·
    refine ⟨29986082488265588028429925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39981443317687450704573233 29986082488265588028429925)
    ·
      refine ⟨5622390466549797755330611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29986082488265588028429925 5622390466549797755330611)
      ·
        refine ⟨8433585699824696632995917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5622390466549797755330611 8433585699824696632995917)
        ·
          refine ⟨3162594637434261237373469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8433585699824696632995917 3162594637434261237373469)
          ·
            refine ⟨1185972989037847964015051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3162594637434261237373469 1185972989037847964015051)
            ·
              refine ⟨1778959483556771946022577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185972989037847964015051 1778959483556771946022577)
              ·
                refine ⟨1334219612667578959516933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778959483556771946022577 1334219612667578959516933)
                ·
                  refine ⟨250166177375171054909425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334219612667578959516933 250166177375171054909425)
                  ·
                    rfl

theorem cell21_1096193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_1096193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096193 prefixEnd_1096193 := by exact prefixLift 1096193
  have htrace : WordTrace (prefixWord ++ tailWord_1096193) baseStart_1096193 baseEnd_1096193 := by
    simpa [prefixWord, tailWord_1096193, baseEnd_1096193] using wordTrace_append hprefix tailTrace_1096193
  have hstable : (prefixWord ++ tailWord_1096193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096193).length < 2 ^ (prefixWord ++ tailWord_1096193).sum := by decide
  have hdescent : baseEnd_1096193 < baseStart_1096193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096221 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1096221 : Nat := 118140960795 + 1096221 * 2 ^ 59
def prefixEnd_1096221 : Nat := 4983230072969 + 3 ^ 40 * 1096221 * 2
def baseEnd_1096221 : Nat := 250172567356649228442701

theorem tailTrace_1096221 : CollatzResearch.WordTrace tailWord_1096221 prefixEnd_1096221 250172567356649228442701 := by
  unfold tailWord_1096221
  simp only [CollatzResearch.WordTrace]
  refine ⟨39982464561586011486592517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26654976374390674324395011 39982464561586011486592517)
  ·
    refine ⟨7496712105297377153736097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39982464561586011486592517 7496712105297377153736097)
    ·
      refine ⟨5622534078973032865302073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7496712105297377153736097 5622534078973032865302073)
      ·
        refine ⟨4216900559229774648976555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5622534078973032865302073 4216900559229774648976555)
        ·
          refine ⟨6325350838844661973464833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216900559229774648976555 6325350838844661973464833)
          ·
            refine ⟨4744013129133496480098625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6325350838844661973464833 4744013129133496480098625)
            ·
              refine ⟨3558009846850122360073969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4744013129133496480098625 3558009846850122360073969)
              ·
                refine ⟨2668507385137591770055477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558009846850122360073969 2668507385137591770055477)
                ·
                  refine ⟨250172567356649228442701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2668507385137591770055477 250172567356649228442701)
                  ·
                    rfl

theorem cell21_1096221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1096221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096221 prefixEnd_1096221 := by exact prefixLift 1096221
  have htrace : WordTrace (prefixWord ++ tailWord_1096221) baseStart_1096221 baseEnd_1096221 := by
    simpa [prefixWord, tailWord_1096221, baseEnd_1096221] using wordTrace_append hprefix tailTrace_1096221
  have hstable : (prefixWord ++ tailWord_1096221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096221).length < 2 ^ (prefixWord ++ tailWord_1096221).sum := by decide
  have hdescent : baseEnd_1096221 < baseStart_1096221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096224 : List Nat := [2, 1, 1, 6, 2, 2, 2, 5]
def baseStart_1096224 : Nat := 118140960795 + 1096224 * 2 ^ 59
def prefixEnd_1096224 : Nat := 4983230072969 + 3 ^ 40 * 1096224 * 2
def baseEnd_1096224 : Nat := 83391083999173963297565

theorem tailTrace_1096224 : CollatzResearch.WordTrace tailWord_1096224 prefixEnd_1096224 83391083999173963297565 := by
  unfold tailWord_1096224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991286990287571499475863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26655049320383428665967817 19991286990287571499475863)
  ·
    refine ⟨29986930485431357249213795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19991286990287571499475863 29986930485431357249213795)
    ·
      refine ⟨44980395728147035873820693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29986930485431357249213795 44980395728147035873820693)
      ·
        refine ⟨2108456049756892306585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44980395728147035873820693 2108456049756892306585345)
        ·
          refine ⟨1581342037317669229939009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2108456049756892306585345 1581342037317669229939009)
          ·
            refine ⟨1186006527988251922454257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581342037317669229939009 1186006527988251922454257)
            ·
              refine ⟨889504895991188941840693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186006527988251922454257 889504895991188941840693)
              ·
                refine ⟨83391083999173963297565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 889504895991188941840693 83391083999173963297565)
                ·
                  rfl

theorem cell21_1096224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_1096224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096224 prefixEnd_1096224 := by exact prefixLift 1096224
  have htrace : WordTrace (prefixWord ++ tailWord_1096224) baseStart_1096224 baseEnd_1096224 := by
    simpa [prefixWord, tailWord_1096224, baseEnd_1096224] using wordTrace_append hprefix tailTrace_1096224
  have hstable : (prefixWord ++ tailWord_1096224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096224).length < 2 ^ (prefixWord ++ tailWord_1096224).sum := by decide
  have hdescent : baseEnd_1096224 < baseStart_1096224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096266 : List Nat := [3, 1, 2, 1, 1, 5, 2, 6]
def baseStart_1096266 : Nat := 118140960795 + 1096266 * 2 ^ 59
def prefixEnd_1096266 : Nat := 4983230072969 + 3 ^ 40 * 1096266 * 2
def baseEnd_1096266 : Nat := 83394278989913050064203

theorem tailTrace_1096266 : CollatzResearch.WordTrace tailWord_1096266 prefixEnd_1096266 83394278989913050064203 := by
  unfold tailWord_1096266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996026461605746042995163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26656070564281989447987101 9996026461605746042995163)
  ·
    refine ⟨14994039692408619064492745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9996026461605746042995163 14994039692408619064492745)
    ·
      refine ⟨11245529769306464298369559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14994039692408619064492745 11245529769306464298369559)
      ·
        refine ⟨16868294653959696447554339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245529769306464298369559 16868294653959696447554339)
        ·
          refine ⟨25302441980939544671331509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868294653959696447554339 25302441980939544671331509)
          ·
            refine ⟨2372103935713082312937329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25302441980939544671331509 2372103935713082312937329)
            ·
              refine ⟨1779077951784811734702997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372103935713082312937329 1779077951784811734702997)
              ·
                refine ⟨83394278989913050064203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1779077951784811734702997 83394278989913050064203)
                ·
                  rfl

theorem cell21_1096266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_1096266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096266 prefixEnd_1096266 := by exact prefixLift 1096266
  have htrace : WordTrace (prefixWord ++ tailWord_1096266) baseStart_1096266 baseEnd_1096266 := by
    simpa [prefixWord, tailWord_1096266, baseEnd_1096266] using wordTrace_append hprefix tailTrace_1096266
  have hstable : (prefixWord ++ tailWord_1096266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096266).length < 2 ^ (prefixWord ++ tailWord_1096266).sum := by decide
  have hdescent : baseEnd_1096266 < baseStart_1096266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096269 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1096269 : Nat := 118140960795 + 1096269 * 2 ^ 59
def prefixEnd_1096269 : Nat := 4983230072969 + 3 ^ 40 * 1096269 * 2
def baseEnd_1096269 : Nat := 250183521610611811642603

theorem tailTrace_1096269 : CollatzResearch.WordTrace tailWord_1096269 prefixEnd_1096269 250183521610611811642603 := by
  unfold tailWord_1096269
  simp only [CollatzResearch.WordTrace]
  refine ⟨39984215265412115684339861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26656143510274743789559907 39984215265412115684339861)
  ·
    refine ⟨1874260090566192922703431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39984215265412115684339861 1874260090566192922703431)
    ·
      refine ⟨2811390135849289384055147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874260090566192922703431 2811390135849289384055147)
      ·
        refine ⟨4217085203773934076082721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811390135849289384055147 4217085203773934076082721)
        ·
          refine ⟨3162813902830450557062041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4217085203773934076082721 3162813902830450557062041)
          ·
            refine ⟨2372110427122837917796531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3162813902830450557062041 2372110427122837917796531)
            ·
              refine ⟨3558165640684256876694797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372110427122837917796531 3558165640684256876694797)
              ·
                refine ⟨1334312115256596328760549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3558165640684256876694797 1334312115256596328760549)
                ·
                  refine ⟨250183521610611811642603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334312115256596328760549 250183521610611811642603)
                  ·
                    rfl

theorem cell21_1096269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1096269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096269 prefixEnd_1096269 := by exact prefixLift 1096269
  have htrace : WordTrace (prefixWord ++ tailWord_1096269) baseStart_1096269 baseEnd_1096269 := by
    simpa [prefixWord, tailWord_1096269, baseEnd_1096269] using wordTrace_append hprefix tailTrace_1096269
  have hstable : (prefixWord ++ tailWord_1096269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096269).length < 2 ^ (prefixWord ++ tailWord_1096269).sum := by decide
  have hdescent : baseEnd_1096269 < baseStart_1096269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096280 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1096280 : Nat := 118140960795 + 1096280 * 2 ^ 59
def prefixEnd_1096280 : Nat := 4983230072969 + 3 ^ 40 * 1096280 * 2
def baseEnd_1096280 : Nat := 250186031960478236959247

theorem tailTrace_1096280 : CollatzResearch.WordTrace tailWord_1096280 prefixEnd_1096280 250186031960478236959247 := by
  unfold tailWord_1096280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992308234186132281495147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26656410978914843041993529 19992308234186132281495147)
  ·
    refine ⟨29988462351279198422242721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19992308234186132281495147 29988462351279198422242721)
    ·
      refine ⟨22491346763459398816682041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29988462351279198422242721 22491346763459398816682041)
      ·
        refine ⟨16868510072594549112511531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22491346763459398816682041 16868510072594549112511531)
        ·
          refine ⟨25302765108891823668767297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868510072594549112511531 25302765108891823668767297)
          ·
            refine ⟨18977073831668867751575473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25302765108891823668767297 18977073831668867751575473)
            ·
              refine ⟨14232805373751650813681605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18977073831668867751575473 14232805373751650813681605)
              ·
                refine ⟨2668651007578434527565301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14232805373751650813681605 2668651007578434527565301)
                ·
                  refine ⟨250186031960478236959247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2668651007578434527565301 250186031960478236959247)
                  ·
                    rfl

theorem cell21_1096280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1096280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096280 prefixEnd_1096280 := by exact prefixLift 1096280
  have htrace : WordTrace (prefixWord ++ tailWord_1096280) baseStart_1096280 baseEnd_1096280 := by
    simpa [prefixWord, tailWord_1096280, baseEnd_1096280] using wordTrace_append hprefix tailTrace_1096280
  have hstable : (prefixWord ++ tailWord_1096280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096280).length < 2 ^ (prefixWord ++ tailWord_1096280).sum := by decide
  have hdescent : baseEnd_1096280 < baseStart_1096280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096297 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 3]
def baseStart_1096297 : Nat := 118140960795 + 1096297 * 2 ^ 59
def prefixEnd_1096297 : Nat := 4983230072969 + 3 ^ 40 * 1096297 * 2
def baseEnd_1096297 : Nat := 250189911592089985175879

theorem tailTrace_1096297 : CollatzResearch.WordTrace tailWord_1096297 prefixEnd_1096297 250189911592089985175879 := by
  unfold tailWord_1096297
  simp only [CollatzResearch.WordTrace]
  refine ⟨39985236509310676466359145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26656824339540450977572763 39985236509310676466359145)
  ·
    refine ⟨29988927381983007349769359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39985236509310676466359145 29988927381983007349769359)
    ·
      refine ⟨44983391072974511024654039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29988927381983007349769359 44983391072974511024654039)
      ·
        refine ⟨67475086609461766536981059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44983391072974511024654039 67475086609461766536981059)
        ·
          refine ⟨101212629914192649805471589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67475086609461766536981059 101212629914192649805471589)
          ·
            refine ⟨18977368108911121838525923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101212629914192649805471589 18977368108911121838525923)
            ·
              refine ⟨28466052163366682757788885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18977368108911121838525923 28466052163366682757788885)
              ·
                refine ⟨667173097578906627135677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28466052163366682757788885 667173097578906627135677)
                ·
                  refine ⟨250189911592089985175879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667173097578906627135677 250189911592089985175879)
                  ·
                    rfl

theorem cell21_1096297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_1096297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096297 prefixEnd_1096297 := by exact prefixLift 1096297
  have htrace : WordTrace (prefixWord ++ tailWord_1096297) baseStart_1096297 baseEnd_1096297 := by
    simpa [prefixWord, tailWord_1096297, baseEnd_1096297] using wordTrace_append hprefix tailTrace_1096297
  have hstable : (prefixWord ++ tailWord_1096297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096297).length < 2 ^ (prefixWord ++ tailWord_1096297).sum := by decide
  have hdescent : baseEnd_1096297 < baseStart_1096297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096311 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_1096311 : Nat := 118140960795 + 1096311 * 2 ^ 59
def prefixEnd_1096311 : Nat := 4983230072969 + 3 ^ 40 * 1096311 * 2
def baseEnd_1096311 : Nat := 250193106582829071942517

theorem tailTrace_1096311 : CollatzResearch.WordTrace tailWord_1096311 prefixEnd_1096311 250193106582829071942517 := by
  unfold tailWord_1096311
  simp only [CollatzResearch.WordTrace]
  refine ⟨39985747131259956857368787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26657164754173304571579191 39985747131259956857368787)
  ·
    refine ⟨59978620696889935286053181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39985747131259956857368787 59978620696889935286053181)
    ·
      refine ⟨22491982761333725732269943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59978620696889935286053181 22491982761333725732269943)
      ·
        refine ⟨33737974142000588598404915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22491982761333725732269943 33737974142000588598404915)
        ·
          refine ⟨50606961213000882897607373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33737974142000588598404915 50606961213000882897607373)
          ·
            refine ⟨18977610454875331086602765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50606961213000882897607373 18977610454875331086602765)
            ·
              refine ⟨7116603920578249157476037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18977610454875331086602765 7116603920578249157476037)
              ·
                refine ⟨1334363235108421717026757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7116603920578249157476037 1334363235108421717026757)
                ·
                  refine ⟨250193106582829071942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334363235108421717026757 250193106582829071942517)
                  ·
                    rfl

theorem cell21_1096311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_1096311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096311 prefixEnd_1096311 := by exact prefixLift 1096311
  have htrace : WordTrace (prefixWord ++ tailWord_1096311) baseStart_1096311 baseEnd_1096311 := by
    simpa [prefixWord, tailWord_1096311, baseEnd_1096311] using wordTrace_append hprefix tailTrace_1096311
  have hstable : (prefixWord ++ tailWord_1096311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096311).length < 2 ^ (prefixWord ++ tailWord_1096311).sum := by decide
  have hdescent : baseEnd_1096311 < baseStart_1096311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096356 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1096356 : Nat := 118140960795 + 1096356 * 2 ^ 59
def prefixEnd_1096356 : Nat := 4983230072969 + 3 ^ 40 * 1096356 * 2
def baseEnd_1096356 : Nat := 250203376195918993692425

theorem tailTrace_1096356 : CollatzResearch.WordTrace tailWord_1096356 prefixEnd_1096356 250203376195918993692425 := by
  unfold tailWord_1096356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19993694208048464771378461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26658258944064619695171281 19993694208048464771378461)
  ·
    refine ⟨7497635328018174289266923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19993694208048464771378461 7497635328018174289266923)
    ·
      refine ⟨11246452992027261433900385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7497635328018174289266923 11246452992027261433900385)
      ·
        refine ⟨8434839744020446075425289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11246452992027261433900385 8434839744020446075425289)
        ·
          refine ⟨6326129808015334556568967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8434839744020446075425289 6326129808015334556568967)
          ·
            refine ⟨9489194712023001834853451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326129808015334556568967 9489194712023001834853451)
            ·
              refine ⟨14233792068034502752280177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9489194712023001834853451 14233792068034502752280177)
              ·
                refine ⟨10675344051025877064210133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14233792068034502752280177 10675344051025877064210133)
                ·
                  refine ⟨250203376195918993692425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10675344051025877064210133 250203376195918993692425)
                  ·
                    rfl

theorem cell21_1096356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1096356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096356 prefixEnd_1096356 := by exact prefixLift 1096356
  have htrace : WordTrace (prefixWord ++ tailWord_1096356) baseStart_1096356 baseEnd_1096356 := by
    simpa [prefixWord, tailWord_1096356, baseEnd_1096356] using wordTrace_append hprefix tailTrace_1096356
  have hstable : (prefixWord ++ tailWord_1096356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096356).length < 2 ^ (prefixWord ++ tailWord_1096356).sum := by decide
  have hdescent : baseEnd_1096356 < baseStart_1096356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096359 : List Nat := [1, 1, 6, 3, 1, 1, 8]
def baseStart_1096359 : Nat := 118140960795 + 1096359 * 2 ^ 59
def prefixEnd_1096359 : Nat := 4983230072969 + 3 ^ 40 * 1096359 * 2
def baseEnd_1096359 : Nat := 27800451204087961682491

theorem tailTrace_1096359 : CollatzResearch.WordTrace tailWord_1096359 prefixEnd_1096359 27800451204087961682491 := by
  unfold tailWord_1096359
  simp only [CollatzResearch.WordTrace]
  refine ⟨39987497835086061055116131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26658331890057374036744087 39987497835086061055116131)
  ·
    refine ⟨59981246752629091582674197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39987497835086061055116131 59981246752629091582674197)
    ·
      refine ⟨2811620941529488667937853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59981246752629091582674197 2811620941529488667937853)
      ·
        refine ⟨1054357853073558250476695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2811620941529488667937853 1054357853073558250476695)
        ·
          refine ⟨1581536779610337375715043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054357853073558250476695 1581536779610337375715043)
          ·
            refine ⟨2372305169415506063572565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581536779610337375715043 2372305169415506063572565)
            ·
              refine ⟨27800451204087961682491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2372305169415506063572565 27800451204087961682491)
              ·
                rfl

theorem cell21_1096359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 8].length) (baseStart_1096359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096359 prefixEnd_1096359 := by exact prefixLift 1096359
  have htrace : WordTrace (prefixWord ++ tailWord_1096359) baseStart_1096359 baseEnd_1096359 := by
    simpa [prefixWord, tailWord_1096359, baseEnd_1096359] using wordTrace_append hprefix tailTrace_1096359
  have hstable : (prefixWord ++ tailWord_1096359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096359).length < 2 ^ (prefixWord ++ tailWord_1096359).sum := by decide
  have hdescent : baseEnd_1096359 < baseStart_1096359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096373 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_1096373 : Nat := 118140960795 + 1096373 * 2 ^ 59
def prefixEnd_1096373 : Nat := 4983230072969 + 3 ^ 40 * 1096373 * 2
def baseEnd_1096373 : Nat := 250207255827530741909057

theorem tailTrace_1096373 : CollatzResearch.WordTrace tailWord_1096373 prefixEnd_1096373 250207255827530741909057 := by
  unfold tailWord_1096373
  simp only [CollatzResearch.WordTrace]
  refine ⟨39988008457035341446125773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26658672304690227630750515 39988008457035341446125773)
  ·
    refine ⟨14995503171388253042297165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39988008457035341446125773 14995503171388253042297165)
    ·
      refine ⟨5623313689270594890861437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14995503171388253042297165 5623313689270594890861437)
      ·
        refine ⟨2108742633476473084073039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5623313689270594890861437 2108742633476473084073039)
        ·
          refine ⟨3163113950214709626109559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108742633476473084073039 3163113950214709626109559)
          ·
            refine ⟨4744670925322064439164339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163113950214709626109559 4744670925322064439164339)
            ·
              refine ⟨7117006387983096658746509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4744670925322064439164339 7117006387983096658746509)
              ·
                refine ⟨2668877395493661247029941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7117006387983096658746509 2668877395493661247029941)
                ·
                  refine ⟨250207255827530741909057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2668877395493661247029941 250207255827530741909057)
                  ·
                    rfl

theorem cell21_1096373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_1096373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096373 prefixEnd_1096373 := by exact prefixLift 1096373
  have htrace : WordTrace (prefixWord ++ tailWord_1096373) baseStart_1096373 baseEnd_1096373 := by
    simpa [prefixWord, tailWord_1096373, baseEnd_1096373] using wordTrace_append hprefix tailTrace_1096373
  have hstable : (prefixWord ++ tailWord_1096373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096373).length < 2 ^ (prefixWord ++ tailWord_1096373).sum := by decide
  have hdescent : baseEnd_1096373 < baseStart_1096373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096401 : List Nat := [1, 2, 2, 1, 2, 3, 3, 7]
def baseStart_1096401 : Nat := 118140960795 + 1096401 * 2 ^ 59
def prefixEnd_1096401 : Nat := 4983230072969 + 3 ^ 40 * 1096401 * 2
def baseEnd_1096401 : Nat := 83404548603002971814111

theorem tailTrace_1096401 : CollatzResearch.WordTrace tailWord_1096401 prefixEnd_1096401 83404548603002971814111 := by
  unfold tailWord_1096401
  simp only [CollatzResearch.WordTrace]
  refine ⟨39989029700933902228145057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26659353133955934818763371 39989029700933902228145057)
  ·
    refine ⟨29991772275700426671108793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39989029700933902228145057 29991772275700426671108793)
    ·
      refine ⟨22493829206775320003331595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29991772275700426671108793 22493829206775320003331595)
      ·
        refine ⟨33740743810162980004997393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22493829206775320003331595 33740743810162980004997393)
        ·
          refine ⟨25305557857622235003748045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33740743810162980004997393 25305557857622235003748045)
          ·
            refine ⟨9489584196608338126405517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25305557857622235003748045 9489584196608338126405517)
            ·
              refine ⟨3558594073728126797402069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9489584196608338126405517 3558594073728126797402069)
              ·
                refine ⟨83404548603002971814111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3558594073728126797402069 83404548603002971814111)
                ·
                  rfl

theorem cell21_1096401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_1096401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096401 prefixEnd_1096401 := by exact prefixLift 1096401
  have htrace : WordTrace (prefixWord ++ tailWord_1096401) baseStart_1096401 baseEnd_1096401 := by
    simpa [prefixWord, tailWord_1096401, baseEnd_1096401] using wordTrace_append hprefix tailTrace_1096401
  have hstable : (prefixWord ++ tailWord_1096401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096401).length < 2 ^ (prefixWord ++ tailWord_1096401).sum := by decide
  have hdescent : baseEnd_1096401 < baseStart_1096401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096480 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_1096480 : Nat := 118140960795 + 1096480 * 2 ^ 59
def prefixEnd_1096480 : Nat := 4983230072969 + 3 ^ 40 * 1096480 * 2
def baseEnd_1096480 : Nat := 250231674685322333625505

theorem tailTrace_1096480 : CollatzResearch.WordTrace tailWord_1096480 prefixEnd_1096480 250231674685322333625505 := by
  unfold tailWord_1096480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19995955533823849360135447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26661274045098465813513929 19995955533823849360135447)
  ·
    refine ⟨29993933300735774040203171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19995955533823849360135447 29993933300735774040203171)
    ·
      refine ⟨44990899951103661060304757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29993933300735774040203171 44990899951103661060304757)
      ·
        refine ⟨4217896870415968224403571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44990899951103661060304757 4217896870415968224403571)
        ·
          refine ⟨6326845305623952336605357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217896870415968224403571 6326845305623952336605357)
          ·
            refine ⟨2372566989608982126227009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6326845305623952336605357 2372566989608982126227009)
            ·
              refine ⟨1779425242206736594670257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372566989608982126227009 1779425242206736594670257)
              ·
                refine ⟨1334568931655052446002693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779425242206736594670257 1334568931655052446002693)
                ·
                  refine ⟨250231674685322333625505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334568931655052446002693 250231674685322333625505)
                  ·
                    rfl

theorem cell21_1096480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_1096480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096480 prefixEnd_1096480 := by exact prefixLift 1096480
  have htrace : WordTrace (prefixWord ++ tailWord_1096480) baseStart_1096480 baseEnd_1096480 := by
    simpa [prefixWord, tailWord_1096480, baseEnd_1096480] using wordTrace_append hprefix tailTrace_1096480
  have hstable : (prefixWord ++ tailWord_1096480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096480).length < 2 ^ (prefixWord ++ tailWord_1096480).sum := by decide
  have hdescent : baseEnd_1096480 < baseStart_1096480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096556 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_1096556 : Nat := 118140960795 + 1096556 * 2 ^ 59
def prefixEnd_1096556 : Nat := 4983230072969 + 3 ^ 40 * 1096556 * 2
def baseEnd_1096556 : Nat := 250249018920763090358683

theorem tailTrace_1096556 : CollatzResearch.WordTrace tailWord_1096556 prefixEnd_1096556 250249018920763090358683 := by
  unfold tailWord_1096556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19997341507686181850018761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26663122010248242466691681 19997341507686181850018761)
  ·
    refine ⟨14998006130764636387514071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19997341507686181850018761 14998006130764636387514071)
    ·
      refine ⟨22497009196146954581271107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14998006130764636387514071 22497009196146954581271107)
      ·
        refine ⟨33745513794220431871906661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22497009196146954581271107 33745513794220431871906661)
        ·
          refine ⟨6327283836416330975982499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33745513794220431871906661 6327283836416330975982499)
          ·
            refine ⟨9490925754624496463973749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327283836416330975982499 9490925754624496463973749)
            ·
              refine ⟨889774289496046543497539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9490925754624496463973749 889774289496046543497539)
              ·
                refine ⟨1334661434244069815246309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889774289496046543497539 1334661434244069815246309)
                ·
                  refine ⟨250249018920763090358683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334661434244069815246309 250249018920763090358683)
                  ·
                    rfl

theorem cell21_1096556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_1096556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096556 prefixEnd_1096556 := by exact prefixLift 1096556
  have htrace : WordTrace (prefixWord ++ tailWord_1096556) baseStart_1096556 baseEnd_1096556 := by
    simpa [prefixWord, tailWord_1096556, baseEnd_1096556] using wordTrace_append hprefix tailTrace_1096556
  have hstable : (prefixWord ++ tailWord_1096556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096556).length < 2 ^ (prefixWord ++ tailWord_1096556).sum := by decide
  have hdescent : baseEnd_1096556 < baseStart_1096556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096629 : List Nat := [1, 3, 3, 2, 1, 1, 1, 9]
def baseStart_1096629 : Nat := 118140960795 + 1096629 * 2 ^ 59
def prefixEnd_1096629 : Nat := 4983230072969 + 3 ^ 40 * 1096629 * 2
def baseEnd_1096629 : Nat := 83421892838443728547289

theorem tailTrace_1096629 : CollatzResearch.WordTrace tailWord_1096629 prefixEnd_1096629 83421892838443728547289 := by
  unfold tailWord_1096629
  simp only [CollatzResearch.WordTrace]
  refine ⟨39997345544107897167444941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26664897029405264778296627 39997345544107897167444941)
  ·
    refine ⟨14999004579040461437791853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39997345544107897167444941 14999004579040461437791853)
    ·
      refine ⟨5624626717140173039171945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14999004579040461437791853 5624626717140173039171945)
      ·
        refine ⟨4218470037855129779378959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5624626717140173039171945 4218470037855129779378959)
        ·
          refine ⟨6327705056782694669068439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4218470037855129779378959 6327705056782694669068439)
          ·
            refine ⟨9491557585174042003602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327705056782694669068439 9491557585174042003602659)
            ·
              refine ⟨14237336377761063005403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9491557585174042003602659 14237336377761063005403989)
              ·
                refine ⟨83421892838443728547289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14237336377761063005403989 83421892838443728547289)
                ·
                  rfl

theorem cell21_1096629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_1096629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096629 prefixEnd_1096629 := by exact prefixLift 1096629
  have htrace : WordTrace (prefixWord ++ tailWord_1096629) baseStart_1096629 baseEnd_1096629 := by
    simpa [prefixWord, tailWord_1096629, baseEnd_1096629] using wordTrace_append hprefix tailTrace_1096629
  have hstable : (prefixWord ++ tailWord_1096629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096629).length < 2 ^ (prefixWord ++ tailWord_1096629).sum := by decide
  have hdescent : baseEnd_1096629 < baseStart_1096629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096643 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_1096643 : Nat := 118140960795 + 1096643 * 2 ^ 59
def prefixEnd_1096643 : Nat := 4983230072969 + 3 ^ 40 * 1096643 * 2
def baseEnd_1096643 : Nat := 250268873506070272408505

theorem tailTrace_1096643 : CollatzResearch.WordTrace tailWord_1096643 prefixEnd_1096643 250268873506070272408505 := by
  unfold tailWord_1096643
  simp only [CollatzResearch.WordTrace]
  refine ⟨39997856166057177558454583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26665237444038118372303055 39997856166057177558454583)
  ·
    refine ⟨59996784249085766337681875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39997856166057177558454583 59996784249085766337681875)
    ·
      refine ⟨89995176373628649506522813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59996784249085766337681875 89995176373628649506522813)
      ·
        refine ⟨33748191140110743564946055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89995176373628649506522813 33748191140110743564946055)
        ·
          refine ⟨50622286710166115347419083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33748191140110743564946055 50622286710166115347419083)
          ·
            refine ⟨75933430065249173021128625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50622286710166115347419083 75933430065249173021128625)
            ·
              refine ⟨56950072548936879765846469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75933430065249173021128625 56950072548936879765846469)
              ·
                refine ⟨10678138602925664956096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56950072548936879765846469 10678138602925664956096213)
                ·
                  refine ⟨250268873506070272408505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10678138602925664956096213 250268873506070272408505)
                  ·
                    rfl

theorem cell21_1096643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_1096643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096643 prefixEnd_1096643 := by exact prefixLift 1096643
  have htrace : WordTrace (prefixWord ++ tailWord_1096643) baseStart_1096643 baseEnd_1096643 := by
    simpa [prefixWord, tailWord_1096643, baseEnd_1096643] using wordTrace_append hprefix tailTrace_1096643
  have hstable : (prefixWord ++ tailWord_1096643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096643).length < 2 ^ (prefixWord ++ tailWord_1096643).sum := by decide
  have hdescent : baseEnd_1096643 < baseStart_1096643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096694 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1096694 : Nat := 118140960795 + 1096694 * 2 ^ 59
def prefixEnd_1096694 : Nat := 4983230072969 + 3 ^ 40 * 1096694 * 2
def baseEnd_1096694 : Nat := 250280512400905517058401

theorem tailTrace_1096694 : CollatzResearch.WordTrace tailWord_1096694 prefixEnd_1096694 250280512400905517058401 := by
  unfold tailWord_1096694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499982268054525829285071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26666477525914942179040757 2499982268054525829285071)
  ·
    refine ⟨3749973402081788743927607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2499982268054525829285071 3749973402081788743927607)
    ·
      refine ⟨5624960103122683115891411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749973402081788743927607 5624960103122683115891411)
      ·
        refine ⟨8437440154684024673837117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624960103122683115891411 8437440154684024673837117)
        ·
          refine ⟨3164040058006509252688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8437440154684024673837117 3164040058006509252688919)
          ·
            refine ⟨4746060087009763879033379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164040058006509252688919 4746060087009763879033379)
            ·
              refine ⟨7119090130514645818550069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746060087009763879033379 7119090130514645818550069)
              ·
                refine ⟨667414699735748045489069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7119090130514645818550069 667414699735748045489069)
                ·
                  refine ⟨250280512400905517058401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667414699735748045489069 250280512400905517058401)
                  ·
                    rfl

theorem cell21_1096694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1096694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096694 prefixEnd_1096694 := by exact prefixLift 1096694
  have htrace : WordTrace (prefixWord ++ tailWord_1096694) baseStart_1096694 baseEnd_1096694 := by
    simpa [prefixWord, tailWord_1096694, baseEnd_1096694] using wordTrace_append hprefix tailTrace_1096694
  have hstable : (prefixWord ++ tailWord_1096694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096694).length < 2 ^ (prefixWord ++ tailWord_1096694).sum := by decide
  have hdescent : baseEnd_1096694 < baseStart_1096694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096705 : List Nat := [1, 2, 4, 1, 2, 3, 8]
def baseStart_1096705 : Nat := 118140960795 + 1096705 * 2 ^ 59
def prefixEnd_1096705 : Nat := 4983230072969 + 3 ^ 40 * 1096705 * 2
def baseEnd_1096705 : Nat := 27809224750085771375005

theorem tailTrace_1096705 : CollatzResearch.WordTrace tailWord_1096705 prefixEnd_1096705 27809224750085771375005 := by
  unfold tailWord_1096705
  simp only [CollatzResearch.WordTrace]
  refine ⟨40000117491832562147211569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26666744994555041431474379 40000117491832562147211569)
  ·
    refine ⟨30000088118874421610408677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40000117491832562147211569 30000088118874421610408677)
    ·
      refine ⟨5625016522288954051951627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30000088118874421610408677 5625016522288954051951627)
      ·
        refine ⟨8437524783433431077927441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625016522288954051951627 8437524783433431077927441)
        ·
          refine ⟨6328143587575073308445581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437524783433431077927441 6328143587575073308445581)
          ·
            refine ⟨2373053845340652490667093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6328143587575073308445581 2373053845340652490667093)
            ·
              refine ⟨27809224750085771375005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2373053845340652490667093 27809224750085771375005)
              ·
                rfl

theorem cell21_1096705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 8].length) (baseStart_1096705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096705 prefixEnd_1096705 := by exact prefixLift 1096705
  have htrace : WordTrace (prefixWord ++ tailWord_1096705) baseStart_1096705 baseEnd_1096705 := by
    simpa [prefixWord, tailWord_1096705, baseEnd_1096705] using wordTrace_append hprefix tailTrace_1096705
  have hstable : (prefixWord ++ tailWord_1096705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096705).length < 2 ^ (prefixWord ++ tailWord_1096705).sum := by decide
  have hdescent : baseEnd_1096705 < baseStart_1096705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096821 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1096821 : Nat := 118140960795 + 1096821 * 2 ^ 59
def prefixEnd_1096821 : Nat := 4983230072969 + 3 ^ 40 * 1096821 * 2
def baseEnd_1096821 : Nat := 250309495531181518441475

theorem tailTrace_1096821 : CollatzResearch.WordTrace tailWord_1096821 prefixEnd_1096821 250309495531181518441475 := by
  unfold tailWord_1096821
  simp only [CollatzResearch.WordTrace]
  refine ⟨40004348359412313958434317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26669565572941542638956211 40004348359412313958434317)
  ·
    refine ⟨15001630634779617734412869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40004348359412313958434317 15001630634779617734412869)
    ·
      refine ⟨2812805744021178325202413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15001630634779617734412869 2812805744021178325202413)
      ·
        refine ⟨1054802154007941871950905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2812805744021178325202413 1054802154007941871950905)
        ·
          refine ⟨791101615505956403963179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054802154007941871950905 791101615505956403963179)
          ·
            refine ⟨1186652423258934605944769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791101615505956403963179 1186652423258934605944769)
            ·
              refine ⟨889989317444200954458577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186652423258934605944769 889989317444200954458577)
              ·
                refine ⟨667491988083150715843933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889989317444200954458577 667491988083150715843933)
                ·
                  refine ⟨250309495531181518441475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667491988083150715843933 250309495531181518441475)
                  ·
                    rfl

theorem cell21_1096821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1096821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096821 prefixEnd_1096821 := by exact prefixLift 1096821
  have htrace : WordTrace (prefixWord ++ tailWord_1096821) baseStart_1096821 baseEnd_1096821 := by
    simpa [prefixWord, tailWord_1096821, baseEnd_1096821] using wordTrace_append hprefix tailTrace_1096821
  have hstable : (prefixWord ++ tailWord_1096821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096821).length < 2 ^ (prefixWord ++ tailWord_1096821).sum := by decide
  have hdescent : baseEnd_1096821 < baseStart_1096821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096829 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1096829 : Nat := 118140960795 + 1096829 * 2 ^ 59
def prefixEnd_1096829 : Nat := 4983230072969 + 3 ^ 40 * 1096829 * 2
def baseEnd_1096829 : Nat := 250311321240175282308125

theorem tailTrace_1096829 : CollatzResearch.WordTrace tailWord_1096829 prefixEnd_1096829 250311321240175282308125 := by
  unfold tailWord_1096829
  simp only [CollatzResearch.WordTrace]
  refine ⟨40004640143383331324725541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26669760095588887549817027 40004640143383331324725541)
  ·
    refine ⟨7500870026884374623386039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40004640143383331324725541 7500870026884374623386039)
    ·
      refine ⟨11251305040326561935079059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7500870026884374623386039 11251305040326561935079059)
      ·
        refine ⟨16876957560489842902618589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251305040326561935079059 16876957560489842902618589)
        ·
          refine ⟨6328859085183691088481971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16876957560489842902618589 6328859085183691088481971)
          ·
            refine ⟨9493288627775536632722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328859085183691088481971 9493288627775536632722957)
            ·
              refine ⟨3559983235415826237271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9493288627775536632722957 3559983235415826237271109)
              ·
                refine ⟨667496856640467419488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3559983235415826237271109 667496856640467419488333)
                ·
                  refine ⟨250311321240175282308125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667496856640467419488333 250311321240175282308125)
                  ·
                    rfl

theorem cell21_1096829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1096829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096829 prefixEnd_1096829 := by exact prefixLift 1096829
  have htrace : WordTrace (prefixWord ++ tailWord_1096829) baseStart_1096829 baseEnd_1096829 := by
    simpa [prefixWord, tailWord_1096829, baseEnd_1096829] using wordTrace_append hprefix tailTrace_1096829
  have hstable : (prefixWord ++ tailWord_1096829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096829).length < 2 ^ (prefixWord ++ tailWord_1096829).sum := by decide
  have hdescent : baseEnd_1096829 < baseStart_1096829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096874 : List Nat := [3, 1, 5, 1, 1, 2, 8]
def baseStart_1096874 : Nat := 118140960795 + 1096874 * 2 ^ 59
def prefixEnd_1096874 : Nat := 4983230072969 + 3 ^ 40 * 1096874 * 2
def baseEnd_1096874 : Nat := 27813510094807244895337

theorem tailTrace_1096874 : CollatzResearch.WordTrace tailWord_1096874 prefixEnd_1096874 27813510094807244895337 := by
  unfold tailWord_1096874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001570357055076002528419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26670854285480202673409117 10001570357055076002528419)
  ·
    refine ⟨15002355535582614003792629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10001570357055076002528419 15002355535582614003792629)
    ·
      refine ⟨1406470831460870062855559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15002355535582614003792629 1406470831460870062855559)
      ·
        refine ⟨2109706247191305094283339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406470831460870062855559 2109706247191305094283339)
        ·
          refine ⟨3164559370786957641425009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109706247191305094283339 3164559370786957641425009)
          ·
            refine ⟨2373419528090218231068757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164559370786957641425009 2373419528090218231068757)
            ·
              refine ⟨27813510094807244895337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2373419528090218231068757 27813510094807244895337)
              ·
                rfl

theorem cell21_1096874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 8].length) (baseStart_1096874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096874 prefixEnd_1096874 := by exact prefixLift 1096874
  have htrace : WordTrace (prefixWord ++ tailWord_1096874) baseStart_1096874 baseEnd_1096874 := by
    simpa [prefixWord, tailWord_1096874, baseEnd_1096874] using wordTrace_append hprefix tailTrace_1096874
  have hstable : (prefixWord ++ tailWord_1096874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096874).length < 2 ^ (prefixWord ++ tailWord_1096874).sum := by decide
  have hdescent : baseEnd_1096874 < baseStart_1096874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096877 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1096877 : Nat := 118140960795 + 1096877 * 2 ^ 59
def prefixEnd_1096877 : Nat := 4983230072969 + 3 ^ 40 * 1096877 * 2
def baseEnd_1096877 : Nat := 250322275494137865508027

theorem tailTrace_1096877 : CollatzResearch.WordTrace tailWord_1096877 prefixEnd_1096877 250322275494137865508027 := by
  unfold tailWord_1096877
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006390847209435522472885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26670927231472957014981923 40006390847209435522472885)
  ·
    refine ⟨3750599141925884580231833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40006390847209435522472885 3750599141925884580231833)
    ·
      refine ⟨2812949356444413435173875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3750599141925884580231833 2812949356444413435173875)
      ·
        refine ⟨4219424034666620152760813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812949356444413435173875 4219424034666620152760813)
        ·
          refine ⟨1582284012999982557285305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4219424034666620152760813 1582284012999982557285305)
          ·
            refine ⟨1186713009749986917963979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582284012999982557285305 1186713009749986917963979)
            ·
              refine ⟨1780069514624980376945969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186713009749986917963979 1780069514624980376945969)
              ·
                refine ⟨1335052135968735282709477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780069514624980376945969 1335052135968735282709477)
                ·
                  refine ⟨250322275494137865508027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335052135968735282709477 250322275494137865508027)
                  ·
                    rfl

theorem cell21_1096877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1096877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096877 prefixEnd_1096877 := by exact prefixLift 1096877
  have htrace : WordTrace (prefixWord ++ tailWord_1096877) baseStart_1096877 baseEnd_1096877 := by
    simpa [prefixWord, tailWord_1096877, baseEnd_1096877] using wordTrace_append hprefix tailTrace_1096877
  have hstable : (prefixWord ++ tailWord_1096877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096877).length < 2 ^ (prefixWord ++ tailWord_1096877).sum := by decide
  have hdescent : baseEnd_1096877 < baseStart_1096877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096992 : List Nat := [2, 1, 1, 5, 12]
def baseStart_1096992 : Nat := 118140960795 + 1096992 * 2 ^ 59
def prefixEnd_1096992 : Nat := 4983230072969 + 3 ^ 40 * 1096992 * 2
def baseEnd_1096992 : Nat := 3090722469887941001125

theorem tailTrace_1096992 : CollatzResearch.WordTrace tailWord_1096992 prefixEnd_1096992 3090722469887941001125 := by
  unfold tailWord_1096992
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005292620896405081454615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26673723494528540108606153 20005292620896405081454615)
  ·
    refine ⟨30007938931344607622181923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20005292620896405081454615 30007938931344607622181923)
    ·
      refine ⟨45011908397016911433272885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30007938931344607622181923 45011908397016911433272885)
      ·
        refine ⟨4219866412220335446869333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45011908397016911433272885 4219866412220335446869333)
        ·
          refine ⟨3090722469887941001125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4219866412220335446869333 3090722469887941001125)
          ·
            rfl

theorem cell21_1096992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 12].length) (baseStart_1096992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096992 prefixEnd_1096992 := by exact prefixLift 1096992
  have htrace : WordTrace (prefixWord ++ tailWord_1096992) baseStart_1096992 baseEnd_1096992 := by
    simpa [prefixWord, tailWord_1096992, baseEnd_1096992] using wordTrace_append hprefix tailTrace_1096992
  have hstable : (prefixWord ++ tailWord_1096992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096992).length < 2 ^ (prefixWord ++ tailWord_1096992).sum := by decide
  have hdescent : baseEnd_1096992 < baseStart_1096992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096995 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_1096995 : Nat := 118140960795 + 1096995 * 2 ^ 59
def prefixEnd_1096995 : Nat := 4983230072969 + 3 ^ 40 * 1096995 * 2
def baseEnd_1096995 : Nat := 250349204701795882541119

theorem tailTrace_1096995 : CollatzResearch.WordTrace tailWord_1096995 prefixEnd_1096995 250349204701795882541119 := by
  unfold tailWord_1096995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40010694660781941675268439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26673796440521294450178959 40010694660781941675268439)
  ·
    refine ⟨60016041991172912512902659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40010694660781941675268439 60016041991172912512902659)
    ·
      refine ⟨90024062986759368769353989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60016041991172912512902659 90024062986759368769353989)
      ·
        refine ⟨16879511810017381644253873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90024062986759368769353989 16879511810017381644253873)
        ·
          refine ⟨12659633857513036233190405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16879511810017381644253873 12659633857513036233190405)
          ·
            refine ⟨2373681348283694293723201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12659633857513036233190405 2373681348283694293723201)
            ·
              refine ⟨1780261011212770720292401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373681348283694293723201 1780261011212770720292401)
              ·
                refine ⟨1335195758409578040219301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780261011212770720292401 1335195758409578040219301)
                ·
                  refine ⟨250349204701795882541119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335195758409578040219301 250349204701795882541119)
                  ·
                    rfl

theorem cell21_1096995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_1096995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1096995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1096995 prefixEnd_1096995 := by exact prefixLift 1096995
  have htrace : WordTrace (prefixWord ++ tailWord_1096995) baseStart_1096995 baseEnd_1096995 := by
    simpa [prefixWord, tailWord_1096995, baseEnd_1096995] using wordTrace_append hprefix tailTrace_1096995
  have hstable : (prefixWord ++ tailWord_1096995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096995).length < 2 ^ (prefixWord ++ tailWord_1096995).sum := by decide
  have hdescent : baseEnd_1096995 < baseStart_1096995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097009 : List Nat := [1, 2, 2, 3, 3, 1, 3, 6]
def baseStart_1097009 : Nat := 118140960795 + 1097009 * 2 ^ 59
def prefixEnd_1097009 : Nat := 4983230072969 + 3 ^ 40 * 1097009 * 2
def baseEnd_1097009 : Nat := 83450799897511656435919

theorem tailTrace_1097009 : CollatzResearch.WordTrace tailWord_1097009 prefixEnd_1097009 83450799897511656435919 := by
  unfold tailWord_1097009
  simp only [CollatzResearch.WordTrace]
  refine ⟨40011205282731222066278081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26674136855154148044185387 40011205282731222066278081)
  ·
    refine ⟨30008403962048416549708561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40011205282731222066278081 30008403962048416549708561)
    ·
      refine ⟨22506302971536312412281421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30008403962048416549708561 22506302971536312412281421)
      ·
        refine ⟨8439863614326117154605533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22506302971536312412281421 8439863614326117154605533)
        ·
          refine ⟨3164948855372293932977075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8439863614326117154605533 3164948855372293932977075)
          ·
            refine ⟨4747423283058440899465613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164948855372293932977075 4747423283058440899465613)
            ·
              refine ⟨1780283731146915337299605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4747423283058440899465613 1780283731146915337299605)
              ·
                refine ⟨83450799897511656435919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1780283731146915337299605 83450799897511656435919)
                ·
                  rfl

theorem cell21_1097009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_1097009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097009 prefixEnd_1097009 := by exact prefixLift 1097009
  have htrace : WordTrace (prefixWord ++ tailWord_1097009) baseStart_1097009 baseEnd_1097009 := by
    simpa [prefixWord, tailWord_1097009, baseEnd_1097009] using wordTrace_append hprefix tailTrace_1097009
  have hstable : (prefixWord ++ tailWord_1097009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097009).length < 2 ^ (prefixWord ++ tailWord_1097009).sum := by decide
  have hdescent : baseEnd_1097009 < baseStart_1097009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097023 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_1097023 : Nat := 118140960795 + 1097023 * 2 ^ 59
def prefixEnd_1097023 : Nat := 4983230072969 + 3 ^ 40 * 1097023 * 2
def baseEnd_1097023 : Nat := 250355594683274056074395

theorem tailTrace_1097023 : CollatzResearch.WordTrace tailWord_1097023 prefixEnd_1097023 250355594683274056074395 := by
  unfold tailWord_1097023
  simp only [CollatzResearch.WordTrace]
  refine ⟨40011715904680502457287723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26674477269787001638191815 40011715904680502457287723)
  ·
    refine ⟨60017573857020753685931585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40011715904680502457287723 60017573857020753685931585)
    ·
      refine ⟨45013180392765565264448689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60017573857020753685931585 45013180392765565264448689)
      ·
        refine ⟨33759885294574173948336517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45013180392765565264448689 33759885294574173948336517)
        ·
          refine ⟨6329978492732657615313097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33759885294574173948336517 6329978492732657615313097)
          ·
            refine ⟨4747483869549493211484823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6329978492732657615313097 4747483869549493211484823)
            ·
              refine ⟨7121225804324239817227235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747483869549493211484823 7121225804324239817227235)
              ·
                refine ⟨10681838706486359725840853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7121225804324239817227235 10681838706486359725840853)
                ·
                  refine ⟨250355594683274056074395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10681838706486359725840853 250355594683274056074395)
                  ·
                    rfl

theorem cell21_1097023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_1097023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097023 prefixEnd_1097023 := by exact prefixLift 1097023
  have htrace : WordTrace (prefixWord ++ tailWord_1097023) baseStart_1097023 baseEnd_1097023 := by
    simpa [prefixWord, tailWord_1097023, baseEnd_1097023] using wordTrace_append hprefix tailTrace_1097023
  have hstable : (prefixWord ++ tailWord_1097023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097023).length < 2 ^ (prefixWord ++ tailWord_1097023).sum := by decide
  have hdescent : baseEnd_1097023 < baseStart_1097023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097046 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1097046 : Nat := 118140960795 + 1097046 * 2 ^ 59
def prefixEnd_1097046 : Nat := 4983230072969 + 3 ^ 40 * 1097046 * 2
def baseEnd_1097046 : Nat := 250360843596631127191015

theorem tailTrace_1097046 : CollatzResearch.WordTrace tailWord_1097046 prefixEnd_1097046 250360843596631127191015 := by
  unfold tailWord_1097046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500784673974823586585937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26675036522398118256916661 2500784673974823586585937)
  ·
    refine ⟨1875588505481117689939453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2500784673974823586585937 1875588505481117689939453)
    ·
      refine ⟨703345689555419133727295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1875588505481117689939453 703345689555419133727295)
      ·
        refine ⟨1055018534333128700590943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703345689555419133727295 1055018534333128700590943)
        ·
          refine ⟨1582527801499693050886415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055018534333128700590943 1582527801499693050886415)
          ·
            refine ⟨2373791702249539576329623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582527801499693050886415 2373791702249539576329623)
            ·
              refine ⟨3560687553374309364494435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373791702249539576329623 3560687553374309364494435)
              ·
                refine ⟨5341031330061464046741653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560687553374309364494435 5341031330061464046741653)
                ·
                  refine ⟨250360843596631127191015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5341031330061464046741653 250360843596631127191015)
                  ·
                    rfl

theorem cell21_1097046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1097046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097046 prefixEnd_1097046 := by exact prefixLift 1097046
  have htrace : WordTrace (prefixWord ++ tailWord_1097046) baseStart_1097046 baseEnd_1097046 := by
    simpa [prefixWord, tailWord_1097046, baseEnd_1097046] using wordTrace_append hprefix tailTrace_1097046
  have hstable : (prefixWord ++ tailWord_1097046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097046).length < 2 ^ (prefixWord ++ tailWord_1097046).sum := by decide
  have hdescent : baseEnd_1097046 < baseStart_1097046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097071 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 4]
def baseStart_1097071 : Nat := 118140960795 + 1097071 * 2 ^ 59
def prefixEnd_1097071 : Nat := 4983230072969 + 3 ^ 40 * 1097071 * 2
def baseEnd_1097071 : Nat := 250366548937236639274297

theorem tailTrace_1097071 : CollatzResearch.WordTrace tailWord_1097071 prefixEnd_1097071 250366548937236639274297 := by
  unfold tailWord_1097071
  simp only [CollatzResearch.WordTrace]
  refine ⟨40013466608506606655035067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26675644405671071103356711 40013466608506606655035067)
  ·
    refine ⟨60020199912759909982552601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40013466608506606655035067 60020199912759909982552601)
    ·
      refine ⟨45015149934569932486914451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60020199912759909982552601 45015149934569932486914451)
      ·
        refine ⟨67522724901854898730371677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45015149934569932486914451 67522724901854898730371677)
        ·
          refine ⟨25321021838195587023889379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67522724901854898730371677 25321021838195587023889379)
          ·
            refine ⟨37981532757293380535834069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25321021838195587023889379 37981532757293380535834069)
            ·
              refine ⟨890192173999063606308611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37981532757293380535834069 890192173999063606308611)
              ·
                refine ⟨1335288260998595409462917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890192173999063606308611 1335288260998595409462917)
                ·
                  refine ⟨250366548937236639274297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335288260998595409462917 250366548937236639274297)
                  ·
                    rfl

theorem cell21_1097071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_1097071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097071 prefixEnd_1097071 := by exact prefixLift 1097071
  have htrace : WordTrace (prefixWord ++ tailWord_1097071) baseStart_1097071 baseEnd_1097071 := by
    simpa [prefixWord, tailWord_1097071, baseEnd_1097071] using wordTrace_append hprefix tailTrace_1097071
  have hstable : (prefixWord ++ tailWord_1097071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097071).length < 2 ^ (prefixWord ++ tailWord_1097071).sum := by decide
  have hdescent : baseEnd_1097071 < baseStart_1097071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097102 : List Nat := [4, 1, 1, 4, 2, 2, 7]
def baseStart_1097102 : Nat := 118140960795 + 1097102 * 2 ^ 59
def prefixEnd_1097102 : Nat := 4983230072969 + 3 ^ 40 * 1097102 * 2
def baseEnd_1097102 : Nat := 27819291506620830473063

theorem tailTrace_1097102 : CollatzResearch.WordTrace tailWord_1097102 prefixEnd_1097102 27819291506620830473063 := by
  unfold tailWord_1097102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001824658924287368676695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26676398180929532632942373 5001824658924287368676695)
  ·
    refine ⟨7502736988386431053015043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5001824658924287368676695 7502736988386431053015043)
    ·
      refine ⟨11254105482579646579522565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502736988386431053015043 11254105482579646579522565)
      ·
        refine ⟨2110144777983683733660481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11254105482579646579522565 2110144777983683733660481)
        ·
          refine ⟨1582608583487762800245361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110144777983683733660481 1582608583487762800245361)
          ·
            refine ⟨1186956437615822100184021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582608583487762800245361 1186956437615822100184021)
            ·
              refine ⟨27819291506620830473063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1186956437615822100184021 27819291506620830473063)
              ·
                rfl

theorem cell21_1097102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 7].length) (baseStart_1097102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097102 prefixEnd_1097102 := by exact prefixLift 1097102
  have htrace : WordTrace (prefixWord ++ tailWord_1097102) baseStart_1097102 baseEnd_1097102 := by
    simpa [prefixWord, tailWord_1097102, baseEnd_1097102] using wordTrace_append hprefix tailTrace_1097102
  have hstable : (prefixWord ++ tailWord_1097102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097102).length < 2 ^ (prefixWord ++ tailWord_1097102).sum := by decide
  have hdescent : baseEnd_1097102 < baseStart_1097102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097144 : List Nat := [2, 1, 2, 1, 2, 2, 4, 7]
def baseStart_1097144 : Nat := 118140960795 + 1097144 * 2 ^ 59
def prefixEnd_1097144 : Nat := 4983230072969 + 3 ^ 40 * 1097144 * 2
def baseEnd_1097144 : Nat := 83461069510601578185827

theorem tailTrace_1097144 : CollatzResearch.WordTrace tailWord_1097144 prefixEnd_1097144 83461069510601578185827 := by
  unfold tailWord_1097144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20008064568621070061221243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26677419424828093414961657 20008064568621070061221243)
  ·
    refine ⟨30012096852931605091831865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20008064568621070061221243 30012096852931605091831865)
    ·
      refine ⟨22509072639698703818873899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30012096852931605091831865 22509072639698703818873899)
      ·
        refine ⟨33763608959548055728310849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22509072639698703818873899 33763608959548055728310849)
        ·
          refine ⟨25322706719661041796233137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33763608959548055728310849 25322706719661041796233137)
          ·
            refine ⟨18992030039745781347174853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25322706719661041796233137 18992030039745781347174853)
            ·
              refine ⟨3561005632452334002595285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18992030039745781347174853 3561005632452334002595285)
              ·
                refine ⟨83461069510601578185827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3561005632452334002595285 83461069510601578185827)
                ·
                  rfl

theorem cell21_1097144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_1097144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097144 prefixEnd_1097144 := by exact prefixLift 1097144
  have htrace : WordTrace (prefixWord ++ tailWord_1097144) baseStart_1097144 baseEnd_1097144 := by
    simpa [prefixWord, tailWord_1097144, baseEnd_1097144] using wordTrace_append hprefix tailTrace_1097144
  have hstable : (prefixWord ++ tailWord_1097144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097144).length < 2 ^ (prefixWord ++ tailWord_1097144).sum := by decide
  have hdescent : baseEnd_1097144 < baseStart_1097144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097223 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_1097223 : Nat := 118140960795 + 1097223 * 2 ^ 59
def prefixEnd_1097223 : Nat := 4983230072969 + 3 ^ 40 * 1097223 * 2
def baseEnd_1097223 : Nat := 250401237408118152740653

theorem tailTrace_1097223 : CollatzResearch.WordTrace tailWord_1097223 prefixEnd_1097223 250401237408118152740653 := by
  unfold tailWord_1097223
  simp only [CollatzResearch.WordTrace]
  refine ⟨40019010503955936614568323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26679340335970624409712215 40019010503955936614568323)
  ·
    refine ⟨60028515755933904921852485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40019010503955936614568323 60028515755933904921852485)
    ·
      refine ⟨11255346704237607172847341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60028515755933904921852485 11255346704237607172847341)
      ·
        refine ⟨4220755014089102689817753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11255346704237607172847341 4220755014089102689817753)
        ·
          refine ⟨3165566260566827017363315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4220755014089102689817753 3165566260566827017363315)
          ·
            refine ⟨4748349390850240526044973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165566260566827017363315 4748349390850240526044973)
            ·
              refine ⟨1780631021568840197266865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4748349390850240526044973 1780631021568840197266865)
              ·
                refine ⟨1335473266176630147950149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780631021568840197266865 1335473266176630147950149)
                ·
                  refine ⟨250401237408118152740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335473266176630147950149 250401237408118152740653)
                  ·
                    rfl

theorem cell21_1097223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_1097223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097223 prefixEnd_1097223 := by exact prefixLift 1097223
  have htrace : WordTrace (prefixWord ++ tailWord_1097223) baseStart_1097223 baseEnd_1097223 := by
    simpa [prefixWord, tailWord_1097223, baseEnd_1097223] using wordTrace_append hprefix tailTrace_1097223
  have hstable : (prefixWord ++ tailWord_1097223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097223).length < 2 ^ (prefixWord ++ tailWord_1097223).sum := by decide
  have hdescent : baseEnd_1097223 < baseStart_1097223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097240 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_1097240 : Nat := 118140960795 + 1097240 * 2 ^ 59
def prefixEnd_1097240 : Nat := 4983230072969 + 3 ^ 40 * 1097240 * 2
def baseEnd_1097240 : Nat := 250405117039729900957285

theorem tailTrace_1097240 : CollatzResearch.WordTrace tailWord_1097240 prefixEnd_1097240 250405117039729900957285 := by
  unfold tailWord_1097240
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009815272447174258968587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26679753696596232345291449 20009815272447174258968587)
  ·
    refine ⟨30014722908670761388452881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20009815272447174258968587 30014722908670761388452881)
    ·
      refine ⟨22511042181503071041339661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30014722908670761388452881 22511042181503071041339661)
      ·
        refine ⟨8441640818063651640502373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22511042181503071041339661 8441640818063651640502373)
        ·
          refine ⟨1582807653386934682594195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8441640818063651640502373 1582807653386934682594195)
          ·
            refine ⟨2374211480080402023891293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582807653386934682594195 2374211480080402023891293)
            ·
              refine ⟨890329305030150758959235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374211480080402023891293 890329305030150758959235)
              ·
                refine ⟨1335493957545226138438853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890329305030150758959235 1335493957545226138438853)
                ·
                  refine ⟨250405117039729900957285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335493957545226138438853 250405117039729900957285)
                  ·
                    rfl

theorem cell21_1097240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_1097240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097240 prefixEnd_1097240 := by exact prefixLift 1097240
  have htrace : WordTrace (prefixWord ++ tailWord_1097240) baseStart_1097240 baseEnd_1097240 := by
    simpa [prefixWord, tailWord_1097240, baseEnd_1097240] using wordTrace_append hprefix tailTrace_1097240
  have hstable : (prefixWord ++ tailWord_1097240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097240).length < 2 ^ (prefixWord ++ tailWord_1097240).sum := by decide
  have hdescent : baseEnd_1097240 < baseStart_1097240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097246 : List Nat := [4, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1097246 : Nat := 118140960795 + 1097246 * 2 ^ 59
def prefixEnd_1097246 : Nat := 4983230072969 + 3 ^ 40 * 1097246 * 2
def baseEnd_1097246 : Nat := 83468828773825074619091

theorem tailTrace_1097246 : CollatzResearch.WordTrace tailWord_1097246 prefixEnd_1097246 83468828773825074619091 := by
  unfold tailWord_1097246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002481172859076442831949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26679899588581741028437061 5002481172859076442831949)
  ·
    refine ⟨1875930439822153666061981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5002481172859076442831949 1875930439822153666061981)
    ·
      refine ⟨703473914933307624773243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1875930439822153666061981 703473914933307624773243)
      ·
        refine ⟨1055210872399961437159865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703473914933307624773243 1055210872399961437159865)
        ·
          refine ⟨791408154299971077869899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055210872399961437159865 791408154299971077869899)
          ·
            refine ⟨1187112231449956616804849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791408154299971077869899 1187112231449956616804849)
            ·
              refine ⟨890334173587467462603637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1187112231449956616804849 890334173587467462603637)
              ·
                refine ⟨83468828773825074619091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 890334173587467462603637 83468828773825074619091)
                ·
                  rfl

theorem cell21_1097246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1097246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097246 prefixEnd_1097246 := by exact prefixLift 1097246
  have htrace : WordTrace (prefixWord ++ tailWord_1097246) baseStart_1097246 baseEnd_1097246 := by
    simpa [prefixWord, tailWord_1097246, baseEnd_1097246] using wordTrace_append hprefix tailTrace_1097246
  have hstable : (prefixWord ++ tailWord_1097246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097246).length < 2 ^ (prefixWord ++ tailWord_1097246).sum := by decide
  have hdescent : baseEnd_1097246 < baseStart_1097246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097285 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 3]
def baseStart_1097285 : Nat := 118140960795 + 1097285 * 2 ^ 59
def prefixEnd_1097285 : Nat := 4983230072969 + 3 ^ 40 * 1097285 * 2
def baseEnd_1097285 : Nat := 250415386652819822707193

theorem tailTrace_1097285 : CollatzResearch.WordTrace tailWord_1097285 prefixEnd_1097285 250415386652819822707193 := by
  unfold tailWord_1097285
  simp only [CollatzResearch.WordTrace]
  refine ⟨40021271829731321203325309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26680847886487547468883539 40021271829731321203325309)
  ·
    refine ⟨15007976936149245451246991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40021271829731321203325309 15007976936149245451246991)
    ·
      refine ⟨22511965404223868176870487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15007976936149245451246991 22511965404223868176870487)
      ·
        refine ⟨33767948106335802265305731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22511965404223868176870487 33767948106335802265305731)
        ·
          refine ⟨50651922159503703397958597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33767948106335802265305731 50651922159503703397958597)
          ·
            refine ⟨9497235404906944387117237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50651922159503703397958597 9497235404906944387117237)
            ·
              refine ⟨890365819210026036292241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9497235404906944387117237 890365819210026036292241)
              ·
                refine ⟨667774364407519527219181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890365819210026036292241 667774364407519527219181)
                ·
                  refine ⟨250415386652819822707193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667774364407519527219181 250415386652819822707193)
                  ·
                    rfl

theorem cell21_1097285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_1097285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097285 prefixEnd_1097285 := by exact prefixLift 1097285
  have htrace : WordTrace (prefixWord ++ tailWord_1097285) baseStart_1097285 baseEnd_1097285 := by
    simpa [prefixWord, tailWord_1097285, baseEnd_1097285] using wordTrace_append hprefix tailTrace_1097285
  have hstable : (prefixWord ++ tailWord_1097285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097285).length < 2 ^ (prefixWord ++ tailWord_1097285).sum := by decide
  have hdescent : baseEnd_1097285 < baseStart_1097285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097296 : List Nat := [2, 1, 1, 1, 1, 3, 6, 6]
def baseStart_1097296 : Nat := 118140960795 + 1097296 * 2 ^ 59
def prefixEnd_1097296 : Nat := 4983230072969 + 3 ^ 40 * 1097296 * 2
def baseEnd_1097296 : Nat := 83472632334228749341279

theorem tailTrace_1097296 : CollatzResearch.WordTrace tailWord_1097296 prefixEnd_1097296 83472632334228749341279 := by
  unfold tailWord_1097296
  simp only [CollatzResearch.WordTrace]
  refine ⟨20010836516345735040987871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26681115355127646721317161 20010836516345735040987871)
  ·
    refine ⟨30016254774518602561481807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20010836516345735040987871 30016254774518602561481807)
    ·
      refine ⟨45024382161777903842222711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30016254774518602561481807 45024382161777903842222711)
      ·
        refine ⟨67536573242666855763334067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45024382161777903842222711 67536573242666855763334067)
        ·
          refine ⟨101304859864000283645001101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67536573242666855763334067 101304859864000283645001101)
          ·
            refine ⟨37989322449000106366875413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101304859864000283645001101 37989322449000106366875413)
            ·
              refine ⟨1780749489796879985947285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37989322449000106366875413 1780749489796879985947285)
              ·
                refine ⟨83472632334228749341279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1780749489796879985947285 83472632334228749341279)
                ·
                  rfl

theorem cell21_1097296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_1097296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097296 prefixEnd_1097296 := by exact prefixLift 1097296
  have htrace : WordTrace (prefixWord ++ tailWord_1097296) baseStart_1097296 baseEnd_1097296 := by
    simpa [prefixWord, tailWord_1097296, baseEnd_1097296] using wordTrace_append hprefix tailTrace_1097296
  have hstable : (prefixWord ++ tailWord_1097296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097296).length < 2 ^ (prefixWord ++ tailWord_1097296).sum := by decide
  have hdescent : baseEnd_1097296 < baseStart_1097296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097344 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_1097344 : Nat := 118140960795 + 1097344 * 2 ^ 59
def prefixEnd_1097344 : Nat := 4983230072969 + 3 ^ 40 * 1097344 * 2
def baseEnd_1097344 : Nat := 250428851256648831223739

theorem tailTrace_1097344 : CollatzResearch.WordTrace tailWord_1097344 prefixEnd_1097344 250428851256648831223739 := by
  unfold tailWord_1097344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011711868258787139861543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26682282491011716186482057 20011711868258787139861543)
  ·
    refine ⟨30017567802388180709792315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20011711868258787139861543 30017567802388180709792315)
    ·
      refine ⟨45026351703582271064688473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30017567802388180709792315 45026351703582271064688473)
      ·
        refine ⟨33769763777686703298516355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45026351703582271064688473 33769763777686703298516355)
        ·
          refine ⟨50654645666530054947774533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33769763777686703298516355 50654645666530054947774533)
          ·
            refine ⟨9497746062474385302707725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50654645666530054947774533 9497746062474385302707725)
            ·
              refine ⟨3561654773427894488515397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9497746062474385302707725 3561654773427894488515397)
              ·
                refine ⟨667810270017730216596637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3561654773427894488515397 667810270017730216596637)
                ·
                  refine ⟨250428851256648831223739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667810270017730216596637 250428851256648831223739)
                  ·
                    rfl

theorem cell21_1097344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_1097344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097344 prefixEnd_1097344 := by exact prefixLift 1097344
  have htrace : WordTrace (prefixWord ++ tailWord_1097344) baseStart_1097344 baseEnd_1097344 := by
    simpa [prefixWord, tailWord_1097344, baseEnd_1097344] using wordTrace_append hprefix tailTrace_1097344
  have hstable : (prefixWord ++ tailWord_1097344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097344).length < 2 ^ (prefixWord ++ tailWord_1097344).sum := by decide
  have hdescent : baseEnd_1097344 < baseStart_1097344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097448 : List Nat := [2, 1, 4, 1, 3, 1, 9]
def baseStart_1097448 : Nat := 118140960795 + 1097448 * 2 ^ 59
def prefixEnd_1097448 : Nat := 4983230072969 + 3 ^ 40 * 1097448 * 2
def baseEnd_1097448 : Nat := 27828065052618640165577

theorem tailTrace_1097448 : CollatzResearch.WordTrace tailWord_1097448 prefixEnd_1097448 27828065052618640165577 := by
  unfold tailWord_1097448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20013608464070400020754499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26684811285427200027672665 20013608464070400020754499)
  ·
    refine ⟨30020412696105600031131749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20013608464070400020754499 30020412696105600031131749)
    ·
      refine ⟨5628827380519800005837203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30020412696105600031131749 5628827380519800005837203)
      ·
        refine ⟨8443241070779700008755805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628827380519800005837203 8443241070779700008755805)
        ·
          refine ⟨3166215401542387503283427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8443241070779700008755805 3166215401542387503283427)
          ·
            refine ⟨4749323102313581254925141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166215401542387503283427 4749323102313581254925141)
            ·
              refine ⟨27828065052618640165577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4749323102313581254925141 27828065052618640165577)
              ·
                rfl

theorem cell21_1097448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 9].length) (baseStart_1097448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097448 prefixEnd_1097448 := by exact prefixLift 1097448
  have htrace : WordTrace (prefixWord ++ tailWord_1097448) baseStart_1097448 baseEnd_1097448 := by
    simpa [prefixWord, tailWord_1097448, baseEnd_1097448] using wordTrace_append hprefix tailTrace_1097448
  have hstable : (prefixWord ++ tailWord_1097448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097448).length < 2 ^ (prefixWord ++ tailWord_1097448).sum := by decide
  have hdescent : baseEnd_1097448 < baseStart_1097448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097569 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_1097569 : Nat := 118140960795 + 1097569 * 2 ^ 59
def prefixEnd_1097569 : Nat := 4983230072969 + 3 ^ 40 * 1097569 * 2
def baseEnd_1097569 : Nat := 250480199322098439973279

theorem tailTrace_1097569 : CollatzResearch.WordTrace tailWord_1097569 prefixEnd_1097569 250480199322098439973279 := by
  unfold tailWord_1097569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40031630160702437706663761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26687753440468291804442507 40031630160702437706663761)
  ·
    refine ⟨30023722620526828279997821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40031630160702437706663761 30023722620526828279997821)
    ·
      refine ⟨11258895982697560604999183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30023722620526828279997821 11258895982697560604999183)
      ·
        refine ⟨16888343974046340907498775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258895982697560604999183 16888343974046340907498775)
        ·
          refine ⟨25332515961069511361248163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16888343974046340907498775 25332515961069511361248163)
          ·
            refine ⟨37998773941604267041872245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25332515961069511361248163 37998773941604267041872245)
            ·
              refine ⟨3562385057025400035175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37998773941604267041872245 3562385057025400035175523)
              ·
                refine ⟨5343577585538100052763285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562385057025400035175523 5343577585538100052763285)
                ·
                  refine ⟨250480199322098439973279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5343577585538100052763285 250480199322098439973279)
                  ·
                    rfl

theorem cell21_1097569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_1097569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097569 prefixEnd_1097569 := by exact prefixLift 1097569
  have htrace : WordTrace (prefixWord ++ tailWord_1097569) baseStart_1097569 baseEnd_1097569 := by
    simpa [prefixWord, tailWord_1097569, baseEnd_1097569] using wordTrace_append hprefix tailTrace_1097569
  have hstable : (prefixWord ++ tailWord_1097569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097569).length < 2 ^ (prefixWord ++ tailWord_1097569).sum := by decide
  have hdescent : baseEnd_1097569 < baseStart_1097569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097572 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1097572 : Nat := 118140960795 + 1097572 * 2 ^ 59
def prefixEnd_1097572 : Nat := 4983230072969 + 3 ^ 40 * 1097572 * 2
def baseEnd_1097572 : Nat := 250480883962971101423273

theorem tailTrace_1097572 : CollatzResearch.WordTrace tailWord_1097572 prefixEnd_1097572 250480883962971101423273 := by
  unfold tailWord_1097572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20015869789845784609511485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26687826386461046146015313 20015869789845784609511485)
  ·
    refine ⟨7505951171192169228566807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20015869789845784609511485 7505951171192169228566807)
    ·
      refine ⟨11258926756788253842850211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7505951171192169228566807 11258926756788253842850211)
      ·
        refine ⟨16888390135182380764275317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258926756788253842850211 16888390135182380764275317)
        ·
          refine ⟨1583286575173348196650811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16888390135182380764275317 1583286575173348196650811)
          ·
            refine ⟨2374929862760022294976217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583286575173348196650811 2374929862760022294976217)
            ·
              refine ⟨1781197397070016721232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374929862760022294976217 1781197397070016721232163)
              ·
                refine ⟨2671796095605025081848245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781197397070016721232163 2671796095605025081848245)
                ·
                  refine ⟨250480883962971101423273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671796095605025081848245 250480883962971101423273)
                  ·
                    rfl

theorem cell21_1097572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1097572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097572 prefixEnd_1097572 := by exact prefixLift 1097572
  have htrace : WordTrace (prefixWord ++ tailWord_1097572) baseStart_1097572 baseEnd_1097572 := by
    simpa [prefixWord, tailWord_1097572, baseEnd_1097572] using wordTrace_append hprefix tailTrace_1097572
  have hstable : (prefixWord ++ tailWord_1097572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097572).length < 2 ^ (prefixWord ++ tailWord_1097572).sum := by decide
  have hdescent : baseEnd_1097572 < baseStart_1097572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097724 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_1097724 : Nat := 118140960795 + 1097724 * 2 ^ 59
def prefixEnd_1097724 : Nat := 4983230072969 + 3 ^ 40 * 1097724 * 2
def baseEnd_1097724 : Nat := 250515572433852614889629

theorem tailTrace_1097724 : CollatzResearch.WordTrace tailWord_1097724 prefixEnd_1097724 250515572433852614889629 := by
  unfold tailWord_1097724
  simp only [CollatzResearch.WordTrace]
  refine ⟨20018641737570449589278113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26691522316760599452370817 20018641737570449589278113)
  ·
    refine ⟨15013981303177837191958585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20018641737570449589278113 15013981303177837191958585)
    ·
      refine ⟨11260485977383377893968939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15013981303177837191958585 11260485977383377893968939)
      ·
        refine ⟨16890728966075066840953409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260485977383377893968939 16890728966075066840953409)
        ·
          refine ⟨12668046724556300130715057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16890728966075066840953409 12668046724556300130715057)
          ·
            refine ⟨9501035043417225098036293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12668046724556300130715057 9501035043417225098036293)
            ·
              refine ⟨1781444070640729705881805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9501035043417225098036293 1781444070640729705881805)
              ·
                refine ⟨668041526490273639705677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1781444070640729705881805 668041526490273639705677)
                ·
                  refine ⟨250515572433852614889629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668041526490273639705677 250515572433852614889629)
                  ·
                    rfl

theorem cell21_1097724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_1097724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097724 prefixEnd_1097724 := by exact prefixLift 1097724
  have htrace : WordTrace (prefixWord ++ tailWord_1097724) baseStart_1097724 baseEnd_1097724 := by
    simpa [prefixWord, tailWord_1097724, baseEnd_1097724] using wordTrace_append hprefix tailTrace_1097724
  have hstable : (prefixWord ++ tailWord_1097724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097724).length < 2 ^ (prefixWord ++ tailWord_1097724).sum := by decide
  have hdescent : baseEnd_1097724 < baseStart_1097724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097738 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1097738 : Nat := 118140960795 + 1097738 * 2 ^ 59
def prefixEnd_1097738 : Nat := 4983230072969 + 3 ^ 40 * 1097738 * 2
def baseEnd_1097738 : Nat := 250518767424591701656267

theorem tailTrace_1097738 : CollatzResearch.WordTrace tailWord_1097738 prefixEnd_1097738 250518767424591701656267 := by
  unfold tailWord_1097738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009448524272544892391467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26691862731393453046377245 10009448524272544892391467)
  ·
    refine ⟨15014172786408817338587201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10009448524272544892391467 15014172786408817338587201)
    ·
      refine ⟨11260629589806613003940401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15014172786408817338587201 11260629589806613003940401)
      ·
        refine ⟨8445472192354959752955301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11260629589806613003940401 8445472192354959752955301)
        ·
          refine ⟨1583526036066554953679119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8445472192354959752955301 1583526036066554953679119)
          ·
            refine ⟨2375289054099832430518679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583526036066554953679119 2375289054099832430518679)
            ·
              refine ⟨3562933581149748645778019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375289054099832430518679 3562933581149748645778019)
              ·
                refine ⟨5344400371724622968667029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562933581149748645778019 5344400371724622968667029)
                ·
                  refine ⟨250518767424591701656267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5344400371724622968667029 250518767424591701656267)
                  ·
                    rfl

theorem cell21_1097738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1097738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097738 prefixEnd_1097738 := by exact prefixLift 1097738
  have htrace : WordTrace (prefixWord ++ tailWord_1097738) baseStart_1097738 baseEnd_1097738 := by
    simpa [prefixWord, tailWord_1097738, baseEnd_1097738] using wordTrace_append hprefix tailTrace_1097738
  have hstable : (prefixWord ++ tailWord_1097738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097738).length < 2 ^ (prefixWord ++ tailWord_1097738).sum := by decide
  have hdescent : baseEnd_1097738 < baseStart_1097738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097797 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1097797 : Nat := 118140960795 + 1097797 * 2 ^ 59
def prefixEnd_1097797 : Nat := 4983230072969 + 3 ^ 40 * 1097797 * 2
def baseEnd_1097797 : Nat := 250532232028420710172813

theorem tailTrace_1097797 : CollatzResearch.WordTrace tailWord_1097797 prefixEnd_1097797 250532232028420710172813 := by
  unfold tailWord_1097797
  simp only [CollatzResearch.WordTrace]
  refine ⟨40039946003876432645963645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26693297335917621763975763 40039946003876432645963645)
  ·
    refine ⟨15014979751453662242236367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40039946003876432645963645 15014979751453662242236367)
    ·
      refine ⟨22522469627180493363354551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15014979751453662242236367 22522469627180493363354551)
      ·
        refine ⟨33783704440770740045031827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22522469627180493363354551 33783704440770740045031827)
        ·
          refine ⟨50675556661156110067547741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33783704440770740045031827 50675556661156110067547741)
          ·
            refine ⟨19003333747933541275330403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50675556661156110067547741 19003333747933541275330403)
            ·
              refine ⟨28505000621900311912995605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19003333747933541275330403 28505000621900311912995605)
              ·
                refine ⟨1336171904151577120921669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28505000621900311912995605 1336171904151577120921669)
                ·
                  refine ⟨250532232028420710172813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336171904151577120921669 250532232028420710172813)
                  ·
                    rfl

theorem cell21_1097797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1097797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097797 prefixEnd_1097797 := by exact prefixLift 1097797
  have htrace : WordTrace (prefixWord ++ tailWord_1097797) baseStart_1097797 baseEnd_1097797 := by
    simpa [prefixWord, tailWord_1097797, baseEnd_1097797] using wordTrace_append hprefix tailTrace_1097797
  have hstable : (prefixWord ++ tailWord_1097797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097797).length < 2 ^ (prefixWord ++ tailWord_1097797).sum := by decide
  have hdescent : baseEnd_1097797 < baseStart_1097797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097980 : List Nat := [2, 2, 2, 1, 4, 2, 2, 6]
def baseStart_1097980 : Nat := 118140960795 + 1097980 * 2 ^ 59
def prefixEnd_1097980 : Nat := 4983230072969 + 3 ^ 40 * 1097980 * 2
def baseEnd_1097980 : Nat := 83524665040551019540813

theorem tailTrace_1097980 : CollatzResearch.WordTrace tailWord_1097980 prefixEnd_1097980 83524665040551019540813 := by
  unfold tailWord_1097980
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023310281106727449937697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26697747041475636599916929 20023310281106727449937697)
  ·
    refine ⟨15017482710830045587453273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20023310281106727449937697 15017482710830045587453273)
    ·
      refine ⟨11263112033122534190589955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15017482710830045587453273 11263112033122534190589955)
      ·
        refine ⟨16894668049683801285884933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11263112033122534190589955 16894668049683801285884933)
        ·
          refine ⟨3167750259315712741103425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16894668049683801285884933 3167750259315712741103425)
          ·
            refine ⟨2375812694486784555827569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167750259315712741103425 2375812694486784555827569)
            ·
              refine ⟨1781859520865088416870677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375812694486784555827569 1781859520865088416870677)
              ·
                refine ⟨83524665040551019540813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1781859520865088416870677 83524665040551019540813)
                ·
                  rfl

theorem cell21_1097980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_1097980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097980 prefixEnd_1097980 := by exact prefixLift 1097980
  have htrace : WordTrace (prefixWord ++ tailWord_1097980) baseStart_1097980 baseEnd_1097980 := by
    simpa [prefixWord, tailWord_1097980, baseEnd_1097980] using wordTrace_append hprefix tailTrace_1097980
  have hstable : (prefixWord ++ tailWord_1097980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097980).length < 2 ^ (prefixWord ++ tailWord_1097980).sum := by decide
  have hdescent : baseEnd_1097980 < baseStart_1097980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097994 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1097994 : Nat := 118140960795 + 1097994 * 2 ^ 59
def prefixEnd_1097994 : Nat := 4983230072969 + 3 ^ 40 * 1097994 * 2
def baseEnd_1097994 : Nat := 250577190112392145389077

theorem tailTrace_1097994 : CollatzResearch.WordTrace tailWord_1097994 prefixEnd_1097994 250577190112392145389077 := by
  unfold tailWord_1097994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011782796040683822721259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26698087456108490193923357 10011782796040683822721259)
  ·
    refine ⟨15017674194061025734081889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011782796040683822721259 15017674194061025734081889)
    ·
      refine ⟨11263255645545769300561417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15017674194061025734081889 11263255645545769300561417)
      ·
        refine ⟨8447441734159326975421063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11263255645545769300561417 8447441734159326975421063)
        ·
          refine ⟨12671162601238990463131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8447441734159326975421063 12671162601238990463131595)
          ·
            refine ⟨19006743901858485694697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12671162601238990463131595 19006743901858485694697393)
            ·
              refine ⟨14255057926393864271023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19006743901858485694697393 14255057926393864271023045)
              ·
                refine ⟨2672823361198849550816821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14255057926393864271023045 2672823361198849550816821)
                ·
                  refine ⟨250577190112392145389077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672823361198849550816821 250577190112392145389077)
                  ·
                    rfl

theorem cell21_1097994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1097994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1097994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1097994 prefixEnd_1097994 := by exact prefixLift 1097994
  have htrace : WordTrace (prefixWord ++ tailWord_1097994) baseStart_1097994 baseEnd_1097994 := by
    simpa [prefixWord, tailWord_1097994, baseEnd_1097994] using wordTrace_append hprefix tailTrace_1097994
  have hstable : (prefixWord ++ tailWord_1097994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097994).length < 2 ^ (prefixWord ++ tailWord_1097994).sum := by decide
  have hdescent : baseEnd_1097994 < baseStart_1097994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098028 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_1098028 : Nat := 118140960795 + 1098028 * 2 ^ 59
def prefixEnd_1098028 : Nat := 4983230072969 + 3 ^ 40 * 1098028 * 2
def baseEnd_1098028 : Nat := 250584949375615641822341

theorem tailTrace_1098028 : CollatzResearch.WordTrace tailWord_1098028 prefixEnd_1098028 250584949375615641822341 := by
  unfold tailWord_1098028
  simp only [CollatzResearch.WordTrace]
  refine ⟨20024185633019779548811369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26698914177359706065081825 20024185633019779548811369)
  ·
    refine ⟨15018139224764834661608527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20024185633019779548811369 15018139224764834661608527)
    ·
      refine ⟨22527208837147251992412791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15018139224764834661608527 22527208837147251992412791)
      ·
        refine ⟨33790813255720877988619187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22527208837147251992412791 33790813255720877988619187)
        ·
          refine ⟨50686219883581316982928781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33790813255720877988619187 50686219883581316982928781)
          ·
            refine ⟨19007332456342993868598293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50686219883581316982928781 19007332456342993868598293)
            ·
              refine ⟨890968708891077837590545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19007332456342993868598293 890968708891077837590545)
              ·
                refine ⟨668226531668308378192909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890968708891077837590545 668226531668308378192909)
                ·
                  refine ⟨250584949375615641822341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668226531668308378192909 250584949375615641822341)
                  ·
                    rfl

theorem cell21_1098028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_1098028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098028 prefixEnd_1098028 := by exact prefixLift 1098028
  have htrace : WordTrace (prefixWord ++ tailWord_1098028) baseStart_1098028 baseEnd_1098028 := by
    simpa [prefixWord, tailWord_1098028, baseEnd_1098028] using wordTrace_append hprefix tailTrace_1098028
  have hstable : (prefixWord ++ tailWord_1098028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098028).length < 2 ^ (prefixWord ++ tailWord_1098028).sum := by decide
  have hdescent : baseEnd_1098028 < baseStart_1098028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098076 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1098076 : Nat := 118140960795 + 1098076 * 2 ^ 59
def prefixEnd_1098076 : Nat := 4983230072969 + 3 ^ 40 * 1098076 * 2
def baseEnd_1098076 : Nat := 250595903629578225022243

theorem tailTrace_1098076 : CollatzResearch.WordTrace tailWord_1098076 prefixEnd_1098076 250595903629578225022243 := by
  unfold tailWord_1098076
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025060984932831647685041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26700081313243775530246721 20025060984932831647685041)
  ·
    refine ⟨15018795738699623735763781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20025060984932831647685041 15018795738699623735763781)
    ·
      refine ⟨2816024201006179450455709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15018795738699623735763781 2816024201006179450455709)
      ·
        refine ⟨1056009075377317293920891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2816024201006179450455709 1056009075377317293920891)
        ·
          refine ⟨1584013613065975940881337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056009075377317293920891 1584013613065975940881337)
          ·
            refine ⟨1188010209799481955661003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584013613065975940881337 1188010209799481955661003)
            ·
              refine ⟨1782015314699222933491505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188010209799481955661003 1782015314699222933491505)
              ·
                refine ⟨1336511486024417200118629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782015314699222933491505 1336511486024417200118629)
                ·
                  refine ⟨250595903629578225022243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336511486024417200118629 250595903629578225022243)
                  ·
                    rfl

theorem cell21_1098076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1098076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098076 prefixEnd_1098076 := by exact prefixLift 1098076
  have htrace : WordTrace (prefixWord ++ tailWord_1098076) baseStart_1098076 baseEnd_1098076 := by
    simpa [prefixWord, tailWord_1098076, baseEnd_1098076] using wordTrace_append hprefix tailTrace_1098076
  have hstable : (prefixWord ++ tailWord_1098076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098076).length < 2 ^ (prefixWord ++ tailWord_1098076).sum := by decide
  have hdescent : baseEnd_1098076 < baseStart_1098076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098087 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_1098087 : Nat := 118140960795 + 1098087 * 2 ^ 59
def prefixEnd_1098087 : Nat := 4983230072969 + 3 ^ 40 * 1098087 * 2
def baseEnd_1098087 : Nat := 250598413979444650338887

theorem tailTrace_1098087 : CollatzResearch.WordTrace tailWord_1098087 prefixEnd_1098087 250598413979444650338887 := by
  unfold tailWord_1098087
  simp only [CollatzResearch.WordTrace]
  refine ⟨40050523172825812174020515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26700348781883874782680343 40050523172825812174020515)
  ·
    refine ⟨60075784759238718261030773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40050523172825812174020515 60075784759238718261030773)
    ·
      refine ⟨5632104821178629836971635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60075784759238718261030773 5632104821178629836971635)
      ·
        refine ⟨8448157231767944755457453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632104821178629836971635 8448157231767944755457453)
        ·
          refine ⟨3168058961912979283296545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8448157231767944755457453 3168058961912979283296545)
          ·
            refine ⟨2376044221434734462472409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3168058961912979283296545 2376044221434734462472409)
            ·
              refine ⟨1782033166076050846854307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376044221434734462472409 1782033166076050846854307)
              ·
                refine ⟨2673049749114076270281461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782033166076050846854307 2673049749114076270281461)
                ·
                  refine ⟨250598413979444650338887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673049749114076270281461 250598413979444650338887)
                  ·
                    rfl

theorem cell21_1098087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_1098087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098087 prefixEnd_1098087 := by exact prefixLift 1098087
  have htrace : WordTrace (prefixWord ++ tailWord_1098087) baseStart_1098087 baseEnd_1098087 := by
    simpa [prefixWord, tailWord_1098087, baseEnd_1098087] using wordTrace_append hprefix tailTrace_1098087
  have hstable : (prefixWord ++ tailWord_1098087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098087).length < 2 ^ (prefixWord ++ tailWord_1098087).sum := by decide
  have hdescent : baseEnd_1098087 < baseStart_1098087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098152 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_1098152 : Nat := 118140960795 + 1098152 * 2 ^ 59
def prefixEnd_1098152 : Nat := 4983230072969 + 3 ^ 40 * 1098152 * 2
def baseEnd_1098152 : Nat := 250613247865018981755421

theorem tailTrace_1098152 : CollatzResearch.WordTrace tailWord_1098152 prefixEnd_1098152 250613247865018981755421 := by
  unfold tailWord_1098152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026446958795164137568355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26701929278393552183424473 20026446958795164137568355)
  ·
    refine ⟨30039670438192746206352533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20026446958795164137568355 30039670438192746206352533)
    ·
      refine ⟨1408109551790284978422775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30039670438192746206352533 1408109551790284978422775)
      ·
        refine ⟨2112164327685427467634163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408109551790284978422775 2112164327685427467634163)
        ·
          refine ⟨3168246491528141201451245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112164327685427467634163 3168246491528141201451245)
          ·
            refine ⟨1188092434323052950544217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3168246491528141201451245 1188092434323052950544217)
            ·
              refine ⟨891069325742289712908163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188092434323052950544217 891069325742289712908163)
              ·
                refine ⟨1336603988613434569362245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891069325742289712908163 1336603988613434569362245)
                ·
                  refine ⟨250613247865018981755421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336603988613434569362245 250613247865018981755421)
                  ·
                    rfl

theorem cell21_1098152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_1098152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098152 prefixEnd_1098152 := by exact prefixLift 1098152
  have htrace : WordTrace (prefixWord ++ tailWord_1098152) baseStart_1098152 baseEnd_1098152 := by
    simpa [prefixWord, tailWord_1098152, baseEnd_1098152] using wordTrace_append hprefix tailTrace_1098152
  have hstable : (prefixWord ++ tailWord_1098152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098152).length < 2 ^ (prefixWord ++ tailWord_1098152).sum := by decide
  have hdescent : baseEnd_1098152 < baseStart_1098152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098197 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 3]
def baseStart_1098197 : Nat := 118140960795 + 1098197 * 2 ^ 59
def prefixEnd_1098197 : Nat := 4983230072969 + 3 ^ 40 * 1098197 * 2
def baseEnd_1098197 : Nat := 250623517478108903505329

theorem tailTrace_1098197 : CollatzResearch.WordTrace tailWord_1098197 prefixEnd_1098197 250623517478108903505329 := by
  unfold tailWord_1098197
  simp only [CollatzResearch.WordTrace]
  refine ⟨40054535202427300960524845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26703023468284867307016563 40054535202427300960524845)
  ·
    refine ⟨15020450700910237860196817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40054535202427300960524845 15020450700910237860196817)
    ·
      refine ⟨11265338025682678395147613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15020450700910237860196817 11265338025682678395147613)
      ·
        refine ⟨4224501759631004398180355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11265338025682678395147613 4224501759631004398180355)
        ·
          refine ⟨6336752639446506597270533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224501759631004398180355 6336752639446506597270533)
          ·
            refine ⟨1188141119896219986988225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6336752639446506597270533 1188141119896219986988225)
            ·
              refine ⟨891105839922164990241169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188141119896219986988225 891105839922164990241169)
              ·
                refine ⟨668329379941623742680877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891105839922164990241169 668329379941623742680877)
                ·
                  refine ⟨250623517478108903505329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668329379941623742680877 250623517478108903505329)
                  ·
                    rfl

theorem cell21_1098197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_1098197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098197 prefixEnd_1098197 := by exact prefixLift 1098197
  have htrace : WordTrace (prefixWord ++ tailWord_1098197) baseStart_1098197 baseEnd_1098197 := by
    simpa [prefixWord, tailWord_1098197, baseEnd_1098197] using wordTrace_append hprefix tailTrace_1098197
  have hstable : (prefixWord ++ tailWord_1098197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098197).length < 2 ^ (prefixWord ++ tailWord_1098197).sum := by decide
  have hdescent : baseEnd_1098197 < baseStart_1098197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098222 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1098222 : Nat := 118140960795 + 1098222 * 2 ^ 59
def prefixEnd_1098222 : Nat := 4983230072969 + 3 ^ 40 * 1098222 * 2
def baseEnd_1098222 : Nat := 250629222818714415588611

theorem tailTrace_1098222 : CollatzResearch.WordTrace tailWord_1098222 prefixEnd_1098222 250629222818714415588611 := by
  unfold tailWord_1098222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006930878417091278773115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26703631351557820153456613 5006930878417091278773115)
  ·
    refine ⟨7510396317625636918159673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006930878417091278773115 7510396317625636918159673)
    ·
      refine ⟨5632797238219227688619755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7510396317625636918159673 5632797238219227688619755)
      ·
        refine ⟨8449195857328841532929633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632797238219227688619755 8449195857328841532929633)
        ·
          refine ⟨6336896892996631149697225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8449195857328841532929633 6336896892996631149697225)
          ·
            refine ⟨4752672669747473362272919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336896892996631149697225 4752672669747473362272919)
            ·
              refine ⟨7129009004621210043409379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752672669747473362272919 7129009004621210043409379)
              ·
                refine ⟨10693513506931815065114069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129009004621210043409379 10693513506931815065114069)
                ·
                  refine ⟨250629222818714415588611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10693513506931815065114069 250629222818714415588611)
                  ·
                    rfl

theorem cell21_1098222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1098222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098222 prefixEnd_1098222 := by exact prefixLift 1098222
  have htrace : WordTrace (prefixWord ++ tailWord_1098222) baseStart_1098222 baseEnd_1098222 := by
    simpa [prefixWord, tailWord_1098222, baseEnd_1098222] using wordTrace_append hprefix tailTrace_1098222
  have hstable : (prefixWord ++ tailWord_1098222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098222).length < 2 ^ (prefixWord ++ tailWord_1098222).sum := by decide
  have hdescent : baseEnd_1098222 < baseStart_1098222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098236 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1098236 : Nat := 118140960795 + 1098236 * 2 ^ 59
def prefixEnd_1098236 : Nat := 4983230072969 + 3 ^ 40 * 1098236 * 2
def baseEnd_1098236 : Nat := 250632417809453502355249

theorem tailTrace_1098236 : CollatzResearch.WordTrace tailWord_1098236 prefixEnd_1098236 250632417809453502355249 := by
  unfold tailWord_1098236
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027978824643005310597281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26703971766190673747463041 20027978824643005310597281)
  ·
    refine ⟨15020984118482253982947961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20027978824643005310597281 15020984118482253982947961)
    ·
      refine ⟨11265738088861690487210971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15020984118482253982947961 11265738088861690487210971)
      ·
        refine ⟨16898607133292535730816457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11265738088861690487210971 16898607133292535730816457)
        ·
          refine ⟨12673955349969401798112343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16898607133292535730816457 12673955349969401798112343)
          ·
            refine ⟨19010933024954102697168515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12673955349969401798112343 19010933024954102697168515)
            ·
              refine ⟨28516399537431154045752773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19010933024954102697168515 28516399537431154045752773)
              ·
                refine ⟨5346824913268341383578645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28516399537431154045752773 5346824913268341383578645)
                ·
                  refine ⟨250632417809453502355249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5346824913268341383578645 250632417809453502355249)
                  ·
                    rfl

theorem cell21_1098236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1098236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098236 prefixEnd_1098236 := by exact prefixLift 1098236
  have htrace : WordTrace (prefixWord ++ tailWord_1098236) baseStart_1098236 baseEnd_1098236 := by
    simpa [prefixWord, tailWord_1098236, baseEnd_1098236] using wordTrace_append hprefix tailTrace_1098236
  have hstable : (prefixWord ++ tailWord_1098236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098236).length < 2 ^ (prefixWord ++ tailWord_1098236).sum := by decide
  have hdescent : baseEnd_1098236 < baseStart_1098236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098239 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 3]
def baseStart_1098239 : Nat := 118140960795 + 1098239 * 2 ^ 59
def prefixEnd_1098239 : Nat := 4983230072969 + 3 ^ 40 * 1098239 * 2
def baseEnd_1098239 : Nat := 250633102450326163805243

theorem tailTrace_1098239 : CollatzResearch.WordTrace tailWord_1098239 prefixEnd_1098239 250633102450326163805243 := by
  unfold tailWord_1098239
  simp only [CollatzResearch.WordTrace]
  refine ⟨40056067068275142133553771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26704044712183428089035847 40056067068275142133553771)
  ·
    refine ⟨60084100602412713200330657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40056067068275142133553771 60084100602412713200330657)
    ·
      refine ⟨45063075451809534900247993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60084100602412713200330657 45063075451809534900247993)
      ·
        refine ⟨33797306588857151175185995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45063075451809534900247993 33797306588857151175185995)
        ·
          refine ⟨50695959883285726762778993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33797306588857151175185995 50695959883285726762778993)
          ·
            refine ⟨38021969912464295072084245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50695959883285726762778993 38021969912464295072084245)
            ·
              refine ⟨1782279839646763831503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38021969912464295072084245 1782279839646763831503949)
              ·
                refine ⟨668354939867536436813981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1782279839646763831503949 668354939867536436813981)
                ·
                  refine ⟨250633102450326163805243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668354939867536436813981 250633102450326163805243)
                  ·
                    rfl

theorem cell21_1098239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].length) (baseStart_1098239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098239 prefixEnd_1098239 := by exact prefixLift 1098239
  have htrace : WordTrace (prefixWord ++ tailWord_1098239) baseStart_1098239 baseEnd_1098239 := by
    simpa [prefixWord, tailWord_1098239, baseEnd_1098239] using wordTrace_append hprefix tailTrace_1098239
  have hstable : (prefixWord ++ tailWord_1098239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098239).length < 2 ^ (prefixWord ++ tailWord_1098239).sum := by decide
  have hdescent : baseEnd_1098239 < baseStart_1098239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098498 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1098498 : Nat := 118140960795 + 1098498 * 2 ^ 59
def prefixEnd_1098498 : Nat := 4983230072969 + 3 ^ 40 * 1098498 * 2
def baseEnd_1098498 : Nat := 250692209778999268988047

theorem tailTrace_1098498 : CollatzResearch.WordTrace tailWord_1098498 prefixEnd_1098498 250692209778999268988047 := by
  unfold tailWord_1098498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016378393584207341808037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26710342382891219578154765 10016378393584207341808037)
  ·
    refine ⟨1878070948797038876589007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10016378393584207341808037 1878070948797038876589007)
    ·
      refine ⟨2817106423195558314883511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878070948797038876589007 2817106423195558314883511)
      ·
        refine ⟨4225659634793337472325267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817106423195558314883511 4225659634793337472325267)
        ·
          refine ⟨6338489452190006208487901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225659634793337472325267 6338489452190006208487901)
          ·
            refine ⟨2376933544571252328182963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6338489452190006208487901 2376933544571252328182963)
            ·
              refine ⟨3565400316856878492274445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376933544571252328182963 3565400316856878492274445)
              ·
                refine ⟨1337025118821329434602917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565400316856878492274445 1337025118821329434602917)
                ·
                  refine ⟨250692209778999268988047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337025118821329434602917 250692209778999268988047)
                  ·
                    rfl

theorem cell21_1098498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1098498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098498 prefixEnd_1098498 := by exact prefixLift 1098498
  have htrace : WordTrace (prefixWord ++ tailWord_1098498) baseStart_1098498 baseEnd_1098498 := by
    simpa [prefixWord, tailWord_1098498, baseEnd_1098498] using wordTrace_append hprefix tailTrace_1098498
  have hstable : (prefixWord ++ tailWord_1098498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098498).length < 2 ^ (prefixWord ++ tailWord_1098498).sum := by decide
  have hdescent : baseEnd_1098498 < baseStart_1098498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098622 : List Nat := [4, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1098622 : Nat := 118140960795 + 1098622 * 2 ^ 59
def prefixEnd_1098622 : Nat := 4983230072969 + 3 ^ 40 * 1098622 * 2
def baseEnd_1098622 : Nat := 83573502756134202973709

theorem tailTrace_1098622 : CollatzResearch.WordTrace tailWord_1098622 prefixEnd_1098622 83573502756134202973709 := by
  unfold tailWord_1098622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008754528235949818093265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26713357483925065696497413 5008754528235949818093265)
  ·
    refine ⟨3756565896176962363569949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5008754528235949818093265 3756565896176962363569949)
    ·
      refine ⟨1408712211066360886338731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3756565896176962363569949 1408712211066360886338731)
      ·
        refine ⟨2113068316599541329508097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408712211066360886338731 2113068316599541329508097)
        ·
          refine ⟨1584801237449655997131073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113068316599541329508097 1584801237449655997131073)
          ·
            refine ⟨1188600928087241997848305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584801237449655997131073 1188600928087241997848305)
            ·
              refine ⟨891450696065431498386229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188600928087241997848305 891450696065431498386229)
              ·
                refine ⟨83573502756134202973709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891450696065431498386229 83573502756134202973709)
                ·
                  rfl

theorem cell21_1098622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1098622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098622 prefixEnd_1098622 := by exact prefixLift 1098622
  have htrace : WordTrace (prefixWord ++ tailWord_1098622) baseStart_1098622 baseEnd_1098622 := by
    simpa [prefixWord, tailWord_1098622, baseEnd_1098622] using wordTrace_append hprefix tailTrace_1098622
  have hstable : (prefixWord ++ tailWord_1098622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098622).length < 2 ^ (prefixWord ++ tailWord_1098622).sum := by decide
  have hdescent : baseEnd_1098622 < baseStart_1098622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098675 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_1098675 : Nat := 118140960795 + 1098675 * 2 ^ 59
def prefixEnd_1098675 : Nat := 4983230072969 + 3 ^ 40 * 1098675 * 2
def baseEnd_1098675 : Nat := 250732603590486294537685

theorem tailTrace_1098675 : CollatzResearch.WordTrace tailWord_1098675 prefixEnd_1098675 250732603590486294537685 := by
  unfold tailWord_1098675
  simp only [CollatzResearch.WordTrace]
  refine ⟨40071969294695588596425479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26714646196463725730950319 40071969294695588596425479)
  ·
    refine ⟨60107953942043382894638219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40071969294695588596425479 60107953942043382894638219)
    ·
      refine ⟨90161930913065074341957329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60107953942043382894638219 90161930913065074341957329)
      ·
        refine ⟨67621448184798805756467997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90161930913065074341957329 67621448184798805756467997)
        ·
          refine ⟨25358043069299552158675499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67621448184798805756467997 25358043069299552158675499)
          ·
            refine ⟨38037064603949328238013249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25358043069299552158675499 38037064603949328238013249)
            ·
              refine ⟨28527798452961996178509937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38037064603949328238013249 28527798452961996178509937)
              ·
                refine ⟨21395848839721497133882453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28527798452961996178509937 21395848839721497133882453)
                ·
                  refine ⟨250732603590486294537685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21395848839721497133882453 250732603590486294537685)
                  ·
                    rfl

theorem cell21_1098675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_1098675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098675 prefixEnd_1098675 := by exact prefixLift 1098675
  have htrace : WordTrace (prefixWord ++ tailWord_1098675) baseStart_1098675 baseEnd_1098675 := by
    simpa [prefixWord, tailWord_1098675, baseEnd_1098675] using wordTrace_append hprefix tailTrace_1098675
  have hstable : (prefixWord ++ tailWord_1098675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098675).length < 2 ^ (prefixWord ++ tailWord_1098675).sum := by decide
  have hdescent : baseEnd_1098675 < baseStart_1098675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098712 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_1098712 : Nat := 118140960795 + 1098712 * 2 ^ 59
def prefixEnd_1098712 : Nat := 4983230072969 + 3 ^ 40 * 1098712 * 2
def baseEnd_1098712 : Nat := 250741047494582452420943

theorem tailTrace_1098712 : CollatzResearch.WordTrace tailWord_1098712 prefixEnd_1098712 250741047494582452420943 := by
  unfold tailWord_1098712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20036659397780771957761195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26715545863707695943681593 20036659397780771957761195)
  ·
    refine ⟨30054989096671157936641793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20036659397780771957761195 30054989096671157936641793)
    ·
      refine ⟨22541241822503368452481345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30054989096671157936641793 22541241822503368452481345)
      ·
        refine ⟨16905931366877526339361009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22541241822503368452481345 16905931366877526339361009)
        ·
          refine ⟨12679448525158144754520757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16905931366877526339361009 12679448525158144754520757)
          ·
            refine ⟨1188698299233576070736321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12679448525158144754520757 1188698299233576070736321)
            ·
              refine ⟨891523724425182053052241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188698299233576070736321 891523724425182053052241)
              ·
                refine ⟨668642793318886539789181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891523724425182053052241 668642793318886539789181)
                ·
                  refine ⟨250741047494582452420943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668642793318886539789181 250741047494582452420943)
                  ·
                    rfl

theorem cell21_1098712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_1098712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098712 prefixEnd_1098712 := by exact prefixLift 1098712
  have htrace : WordTrace (prefixWord ++ tailWord_1098712) baseStart_1098712 baseEnd_1098712 := by
    simpa [prefixWord, tailWord_1098712, baseEnd_1098712] using wordTrace_append hprefix tailTrace_1098712
  have hstable : (prefixWord ++ tailWord_1098712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098712).length < 2 ^ (prefixWord ++ tailWord_1098712).sum := by decide
  have hdescent : baseEnd_1098712 < baseStart_1098712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098737 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_1098737 : Nat := 118140960795 + 1098737 * 2 ^ 59
def prefixEnd_1098737 : Nat := 4983230072969 + 3 ^ 40 * 1098737 * 2
def baseEnd_1098737 : Nat := 250746752835187964504225

theorem tailTrace_1098737 : CollatzResearch.WordTrace tailWord_1098737 prefixEnd_1098737 250746752835187964504225 := by
  unfold tailWord_1098737
  simp only [CollatzResearch.WordTrace]
  refine ⟨40074230620470973185182465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26716153746980648790121643 40074230620470973185182465)
  ·
    refine ⟨30055672965353229888886849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40074230620470973185182465 30055672965353229888886849)
    ·
      refine ⟨22541754724014922416665137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30055672965353229888886849 22541754724014922416665137)
      ·
        refine ⟨16906316043011191812498853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22541754724014922416665137 16906316043011191812498853)
        ·
          refine ⟨3169934258064598464843535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16906316043011191812498853 3169934258064598464843535)
          ·
            refine ⟨4754901387096897697265303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169934258064598464843535 4754901387096897697265303)
            ·
              refine ⟨7132352080645346545897955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754901387096897697265303 7132352080645346545897955)
              ·
                refine ⟨10698528120968019818846933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132352080645346545897955 10698528120968019818846933)
                ·
                  refine ⟨250746752835187964504225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10698528120968019818846933 250746752835187964504225)
                  ·
                    rfl

theorem cell21_1098737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_1098737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098737 prefixEnd_1098737 := by exact prefixLift 1098737
  have htrace : WordTrace (prefixWord ++ tailWord_1098737) baseStart_1098737 baseEnd_1098737 := by
    simpa [prefixWord, tailWord_1098737, baseEnd_1098737] using wordTrace_append hprefix tailTrace_1098737
  have hstable : (prefixWord ++ tailWord_1098737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098737).length < 2 ^ (prefixWord ++ tailWord_1098737).sum := by decide
  have hdescent : baseEnd_1098737 < baseStart_1098737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098906 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1098906 : Nat := 118140960795 + 1098906 * 2 ^ 59
def prefixEnd_1098906 : Nat := 4983230072969 + 3 ^ 40 * 1098906 * 2
def baseEnd_1098906 : Nat := 250785320937681226187213

theorem tailTrace_1098906 : CollatzResearch.WordTrace tailWord_1098906 prefixEnd_1098906 250785320937681226187213 := by
  unfold tailWord_1098906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020098639214678762021143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26720263037905810032056381 10020098639214678762021143)
  ·
    refine ⟨15030147958822018143031715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10020098639214678762021143 15030147958822018143031715)
    ·
      refine ⟨22545221938233027214547573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15030147958822018143031715 22545221938233027214547573)
      ·
        refine ⟨2113614556709346301363835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22545221938233027214547573 2113614556709346301363835)
        ·
          refine ⟨3170421835064019452045753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113614556709346301363835 3170421835064019452045753)
          ·
            refine ⟨2377816376298014589034315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3170421835064019452045753 2377816376298014589034315)
            ·
              refine ⟨3566724564447021883551473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377816376298014589034315 3566724564447021883551473)
              ·
                refine ⟨2675043423335266412663605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566724564447021883551473 2675043423335266412663605)
                ·
                  refine ⟨250785320937681226187213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675043423335266412663605 250785320937681226187213)
                  ·
                    rfl

theorem cell21_1098906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1098906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098906 prefixEnd_1098906 := by exact prefixLift 1098906
  have htrace : WordTrace (prefixWord ++ tailWord_1098906) baseStart_1098906 baseEnd_1098906 := by
    simpa [prefixWord, tailWord_1098906, baseEnd_1098906] using wordTrace_append hprefix tailTrace_1098906
  have hstable : (prefixWord ++ tailWord_1098906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098906).length < 2 ^ (prefixWord ++ tailWord_1098906).sum := by decide
  have hdescent : baseEnd_1098906 < baseStart_1098906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098937 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_1098937 : Nat := 118140960795 + 1098937 * 2 ^ 59
def prefixEnd_1098937 : Nat := 4983230072969 + 3 ^ 40 * 1098937 * 2
def baseEnd_1098937 : Nat := 250792395560032061170483

theorem tailTrace_1098937 : CollatzResearch.WordTrace tailWord_1098937 prefixEnd_1098937 250792395560032061170483 := by
  unfold tailWord_1098937
  simp only [CollatzResearch.WordTrace]
  refine ⟨40081525219746407342463065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26721016813164271561642043 40081525219746407342463065)
  ·
    refine ⟨30061143914809805506847299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40081525219746407342463065 30061143914809805506847299)
    ·
      refine ⟨45091715872214708260270949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30061143914809805506847299 45091715872214708260270949)
      ·
        refine ⟨8454696726040257798800803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45091715872214708260270949 8454696726040257798800803)
        ·
          refine ⟨12682045089060386698201205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8454696726040257798800803 12682045089060386698201205)
          ·
            refine ⟨1188941727099411252956363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12682045089060386698201205 1188941727099411252956363)
            ·
              refine ⟨1783412590649116879434545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188941727099411252956363 1783412590649116879434545)
              ·
                refine ⟨1337559442986837659575909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783412590649116879434545 1337559442986837659575909)
                ·
                  refine ⟨250792395560032061170483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337559442986837659575909 250792395560032061170483)
                  ·
                    rfl

theorem cell21_1098937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_1098937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098937 prefixEnd_1098937 := by exact prefixLift 1098937
  have htrace : WordTrace (prefixWord ++ tailWord_1098937) baseStart_1098937 baseEnd_1098937 := by
    simpa [prefixWord, tailWord_1098937, baseEnd_1098937] using wordTrace_append hprefix tailTrace_1098937
  have hstable : (prefixWord ++ tailWord_1098937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098937).length < 2 ^ (prefixWord ++ tailWord_1098937).sum := by decide
  have hdescent : baseEnd_1098937 < baseStart_1098937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098968 : List Nat := [2, 1, 2, 2, 5, 2, 2, 5]
def baseStart_1098968 : Nat := 118140960795 + 1098968 * 2 ^ 59
def prefixEnd_1098968 : Nat := 4983230072969 + 3 ^ 40 * 1098968 * 2
def baseEnd_1098968 : Nat := 83599823394127632051251

theorem tailTrace_1098968 : CollatzResearch.WordTrace tailWord_1098968 prefixEnd_1098968 83599823394127632051251 := by
  unfold tailWord_1098968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041327941317049818420779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26721770588422733091227705 20041327941317049818420779)
  ·
    refine ⟨30061991911975574727631169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20041327941317049818420779 30061991911975574727631169)
    ·
      refine ⟨22546493933981681045723377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30061991911975574727631169 22546493933981681045723377)
      ·
        refine ⟨16909870450486260784292533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22546493933981681045723377 16909870450486260784292533)
        ·
          refine ⟨1585300354733086948527425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16909870450486260784292533 1585300354733086948527425)
          ·
            refine ⟨1188975266049815211395569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585300354733086948527425 1188975266049815211395569)
            ·
              refine ⟨891731449537361408546677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188975266049815211395569 891731449537361408546677)
              ·
                refine ⟨83599823394127632051251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891731449537361408546677 83599823394127632051251)
                ·
                  rfl

theorem cell21_1098968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_1098968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1098968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1098968 prefixEnd_1098968 := by exact prefixLift 1098968
  have htrace : WordTrace (prefixWord ++ tailWord_1098968) baseStart_1098968 baseEnd_1098968 := by
    simpa [prefixWord, tailWord_1098968, baseEnd_1098968] using wordTrace_append hprefix tailTrace_1098968
  have hstable : (prefixWord ++ tailWord_1098968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098968).length < 2 ^ (prefixWord ++ tailWord_1098968).sum := by decide
  have hdescent : baseEnd_1098968 < baseStart_1098968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099078 : List Nat := [6, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1099078 : Nat := 118140960795 + 1099078 * 2 ^ 59
def prefixEnd_1099078 : Nat := 4983230072969 + 3 ^ 40 * 1099078 * 2
def baseEnd_1099078 : Nat := 83608191227015716440065

theorem tailTrace_1099078 : CollatzResearch.WordTrace tailWord_1099078 prefixEnd_1099078 83608191227015716440065 := by
  unfold tailWord_1099078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252708372257362138229559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26724445274823725615563925 1252708372257362138229559)
  ·
    refine ⟨1879062558386043207344339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252708372257362138229559 1879062558386043207344339)
    ·
      refine ⟨2818593837579064811016509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879062558386043207344339 2818593837579064811016509)
      ·
        refine ⟨1056972689092149304131191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2818593837579064811016509 1056972689092149304131191)
        ·
          refine ⟨1585459033638223956196787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056972689092149304131191 1585459033638223956196787)
          ·
            refine ⟨2378188550457335934295181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585459033638223956196787 2378188550457335934295181)
            ·
              refine ⟨891820706421500975360693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2378188550457335934295181 891820706421500975360693)
              ·
                refine ⟨83608191227015716440065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891820706421500975360693 83608191227015716440065)
                ·
                  rfl

theorem cell21_1099078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1099078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099078 prefixEnd_1099078 := by exact prefixLift 1099078
  have htrace : WordTrace (prefixWord ++ tailWord_1099078) baseStart_1099078 baseEnd_1099078 := by
    simpa [prefixWord, tailWord_1099078, baseEnd_1099078] using wordTrace_append hprefix tailTrace_1099078
  have hstable : (prefixWord ++ tailWord_1099078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099078).length < 2 ^ (prefixWord ++ tailWord_1099078).sum := by decide
  have hdescent : baseEnd_1099078 < baseStart_1099078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099117 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1099117 : Nat := 118140960795 + 1099117 * 2 ^ 59
def prefixEnd_1099117 : Nat := 4983230072969 + 3 ^ 40 * 1099117 * 2
def baseEnd_1099117 : Nat := 250833474012391748170115

theorem tailTrace_1099117 : CollatzResearch.WordTrace tailWord_1099117 prefixEnd_1099117 250833474012391748170115 := by
  unfold tailWord_1099117
  simp only [CollatzResearch.WordTrace]
  refine ⟨40088090359094298084015605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26725393572729532056010403 40088090359094298084015605)
  ·
    refine ⟨3758258471165090445376463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40088090359094298084015605 3758258471165090445376463)
    ·
      refine ⟨5637387706747635668064695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758258471165090445376463 5637387706747635668064695)
      ·
        refine ⟨8456081560121453502097043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5637387706747635668064695 8456081560121453502097043)
        ·
          refine ⟨12684122340182180253145565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456081560121453502097043 12684122340182180253145565)
          ·
            refine ⟨4756545877568317594929587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12684122340182180253145565 4756545877568317594929587)
            ·
              refine ⟨7134818816352476392394381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756545877568317594929587 7134818816352476392394381)
              ·
                refine ⟨2675557056132178647147893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7134818816352476392394381 2675557056132178647147893)
                ·
                  refine ⟨250833474012391748170115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675557056132178647147893 250833474012391748170115)
                  ·
                    rfl

theorem cell21_1099117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1099117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099117 prefixEnd_1099117 := by exact prefixLift 1099117
  have htrace : WordTrace (prefixWord ++ tailWord_1099117) baseStart_1099117 baseEnd_1099117 := by
    simpa [prefixWord, tailWord_1099117, baseEnd_1099117] using wordTrace_append hprefix tailTrace_1099117
  have hstable : (prefixWord ++ tailWord_1099117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099117).length < 2 ^ (prefixWord ++ tailWord_1099117).sum := by decide
  have hdescent : baseEnd_1099117 < baseStart_1099117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099137 : List Nat := [1, 2, 4, 3, 3, 1, 2, 5]
def baseStart_1099137 : Nat := 118140960795 + 1099137 * 2 ^ 59
def prefixEnd_1099137 : Nat := 4983230072969 + 3 ^ 40 * 1099137 * 2
def baseEnd_1099137 : Nat := 83612679428292052612247

theorem tailTrace_1099137 : CollatzResearch.WordTrace tailWord_1099137 prefixEnd_1099137 83612679428292052612247 := by
  unfold tailWord_1099137
  simp only [CollatzResearch.WordTrace]
  refine ⟨40088819819021841499743665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26725879879347894333162443 40088819819021841499743665)
  ·
    refine ⟨30066614864266381124807749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40088819819021841499743665 30066614864266381124807749)
    ·
      refine ⟨5637490287049946460901453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30066614864266381124807749 5637490287049946460901453)
      ·
        refine ⟨2114058857643729922838045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5637490287049946460901453 2114058857643729922838045)
        ·
          refine ⟨792772071616398721064267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2114058857643729922838045 792772071616398721064267)
          ·
            refine ⟨1189158107424598081596401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792772071616398721064267 1189158107424598081596401)
            ·
              refine ⟨891868580568448561197301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189158107424598081596401 891868580568448561197301)
              ·
                refine ⟨83612679428292052612247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891868580568448561197301 83612679428292052612247)
                ·
                  rfl

theorem cell21_1099137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].length) (baseStart_1099137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099137 prefixEnd_1099137 := by exact prefixLift 1099137
  have htrace : WordTrace (prefixWord ++ tailWord_1099137) baseStart_1099137 baseEnd_1099137 := by
    simpa [prefixWord, tailWord_1099137, baseEnd_1099137] using wordTrace_append hprefix tailTrace_1099137
  have hstable : (prefixWord ++ tailWord_1099137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099137).length < 2 ^ (prefixWord ++ tailWord_1099137).sum := by decide
  have hdescent : baseEnd_1099137 < baseStart_1099137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099283 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_1099283 : Nat := 118140960795 + 1099283 * 2 ^ 59
def prefixEnd_1099283 : Nat := 4983230072969 + 3 ^ 40 * 1099283 * 2
def baseEnd_1099283 : Nat := 250871357474012348403109

theorem tailTrace_1099283 : CollatzResearch.WordTrace tailWord_1099283 prefixEnd_1099283 250871357474012348403109 := by
  unfold tailWord_1099283
  simp only [CollatzResearch.WordTrace]
  refine ⟨40094144876492908434558503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26729429917661938956372335 40094144876492908434558503)
  ·
    refine ⟨60141217314739362651837755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40094144876492908434558503 60141217314739362651837755)
    ·
      refine ⟨90211825972109043977756633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60141217314739362651837755 90211825972109043977756633)
      ·
        refine ⟨67658869479081782983317475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90211825972109043977756633 67658869479081782983317475)
        ·
          refine ⟨101488304218622674474976213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67658869479081782983317475 101488304218622674474976213)
          ·
            refine ⟨2378632130123968933007255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101488304218622674474976213 2378632130123968933007255)
            ·
              refine ⟨3567948195185953399510883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378632130123968933007255 3567948195185953399510883)
              ·
                refine ⟨5351922292778930099266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567948195185953399510883 5351922292778930099266325)
                ·
                  refine ⟨250871357474012348403109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5351922292778930099266325 250871357474012348403109)
                  ·
                    rfl

theorem cell21_1099283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_1099283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099283 prefixEnd_1099283 := by exact prefixLift 1099283
  have htrace : WordTrace (prefixWord ++ tailWord_1099283) baseStart_1099283 baseEnd_1099283 := by
    simpa [prefixWord, tailWord_1099283, baseEnd_1099283] using wordTrace_append hprefix tailTrace_1099283
  have hstable : (prefixWord ++ tailWord_1099283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099283).length < 2 ^ (prefixWord ++ tailWord_1099283).sum := by decide
  have hdescent : baseEnd_1099283 < baseStart_1099283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099396 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1099396 : Nat := 118140960795 + 1099396 * 2 ^ 59
def prefixEnd_1099396 : Nat := 4983230072969 + 3 ^ 40 * 1099396 * 2
def baseEnd_1099396 : Nat := 250897145613549263019545

theorem tailTrace_1099396 : CollatzResearch.WordTrace tailWord_1099396 prefixEnd_1099396 250897145613549263019545 := by
  unfold tailWord_1099396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20049133162541764366711021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26732177550055685822281361 20049133162541764366711021)
  ·
    refine ⟨7518424935953161637516633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20049133162541764366711021 7518424935953161637516633)
    ·
      refine ⟨5638818701964871228137475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7518424935953161637516633 5638818701964871228137475)
      ·
        refine ⟨8458228052947306842206213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638818701964871228137475 8458228052947306842206213)
        ·
          refine ⟨1585917759927620032913665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8458228052947306842206213 1585917759927620032913665)
          ·
            refine ⟨1189438319945715024685249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585917759927620032913665 1189438319945715024685249)
            ·
              refine ⟨892078739959286268513937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189438319945715024685249 892078739959286268513937)
              ·
                refine ⟨669059054969464701385453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892078739959286268513937 669059054969464701385453)
                ·
                  refine ⟨250897145613549263019545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669059054969464701385453 250897145613549263019545)
                  ·
                    rfl

theorem cell21_1099396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1099396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099396 prefixEnd_1099396 := by exact prefixLift 1099396
  have htrace : WordTrace (prefixWord ++ tailWord_1099396) baseStart_1099396 baseEnd_1099396 := by
    simpa [prefixWord, tailWord_1099396, baseEnd_1099396] using wordTrace_append hprefix tailTrace_1099396
  have hstable : (prefixWord ++ tailWord_1099396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099396).length < 2 ^ (prefixWord ++ tailWord_1099396).sum := by decide
  have hdescent : baseEnd_1099396 < baseStart_1099396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099404 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1099404 : Nat := 118140960795 + 1099404 * 2 ^ 59
def prefixEnd_1099404 : Nat := 4983230072969 + 3 ^ 40 * 1099404 * 2
def baseEnd_1099404 : Nat := 250898971322543026886195

theorem tailTrace_1099404 : CollatzResearch.WordTrace tailWord_1099404 prefixEnd_1099404 250898971322543026886195 := by
  unfold tailWord_1099404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20049279054527273049856633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26732372072703030733142177 20049279054527273049856633)
  ·
    refine ⟨15036959290895454787392475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20049279054527273049856633 15036959290895454787392475)
    ·
      refine ⟨22555438936343182181088713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15036959290895454787392475 22555438936343182181088713)
      ·
        refine ⟨16916579202257386635816535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22555438936343182181088713 16916579202257386635816535)
        ·
          refine ⟨25374868803386079953724803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16916579202257386635816535 25374868803386079953724803)
          ·
            refine ⟨38062303205079119930587205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25374868803386079953724803 38062303205079119930587205)
            ·
              refine ⟨7136681850952334986985101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38062303205079119930587205 7136681850952334986985101)
              ·
                refine ⟨2676255694107125620119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7136681850952334986985101 2676255694107125620119413)
                ·
                  refine ⟨250898971322543026886195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2676255694107125620119413 250898971322543026886195)
                  ·
                    rfl

theorem cell21_1099404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1099404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099404 prefixEnd_1099404 := by exact prefixLift 1099404
  have htrace : WordTrace (prefixWord ++ tailWord_1099404) baseStart_1099404 baseEnd_1099404 := by
    simpa [prefixWord, tailWord_1099404, baseEnd_1099404] using wordTrace_append hprefix tailTrace_1099404
  have hstable : (prefixWord ++ tailWord_1099404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099404).length < 2 ^ (prefixWord ++ tailWord_1099404).sum := by decide
  have hdescent : baseEnd_1099404 < baseStart_1099404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099452 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1099452 : Nat := 118140960795 + 1099452 * 2 ^ 59
def prefixEnd_1099452 : Nat := 4983230072969 + 3 ^ 40 * 1099452 * 2
def baseEnd_1099452 : Nat := 250909925576505610086097

theorem tailTrace_1099452 : CollatzResearch.WordTrace tailWord_1099452 prefixEnd_1099452 250909925576505610086097 := by
  unfold tailWord_1099452
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050154406440325148730305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26733539208587100198307073 20050154406440325148730305)
  ·
    refine ⟨15037615804830243861547729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20050154406440325148730305 15037615804830243861547729)
    ·
      refine ⟨11278211853622682896160797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15037615804830243861547729 11278211853622682896160797)
      ·
        refine ⟨4229329445108506086060299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11278211853622682896160797 4229329445108506086060299)
        ·
          refine ⟨6343994167662759129090449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229329445108506086060299 6343994167662759129090449)
          ·
            refine ⟨4757995625747069346817837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343994167662759129090449 4757995625747069346817837)
            ·
              refine ⟨1784248359655151005056689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4757995625747069346817837 1784248359655151005056689)
              ·
                refine ⟨1338186269741363253792517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784248359655151005056689 1338186269741363253792517)
                ·
                  refine ⟨250909925576505610086097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338186269741363253792517 250909925576505610086097)
                  ·
                    rfl

theorem cell21_1099452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1099452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099452 prefixEnd_1099452 := by exact prefixLift 1099452
  have htrace : WordTrace (prefixWord ++ tailWord_1099452) baseStart_1099452 baseEnd_1099452 := by
    simpa [prefixWord, tailWord_1099452, baseEnd_1099452] using wordTrace_append hprefix tailTrace_1099452
  have hstable : (prefixWord ++ tailWord_1099452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099452).length < 2 ^ (prefixWord ++ tailWord_1099452).sum := by decide
  have hdescent : baseEnd_1099452 < baseStart_1099452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099480 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1099480 : Nat := 118140960795 + 1099480 * 2 ^ 59
def prefixEnd_1099480 : Nat := 4983230072969 + 3 ^ 40 * 1099480 * 2
def baseEnd_1099480 : Nat := 250916315557983783619373

theorem tailTrace_1099480 : CollatzResearch.WordTrace tailWord_1099480 prefixEnd_1099480 250916315557983783619373 := by
  unfold tailWord_1099480
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050665028389605539739947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26734220037852807386319929 20050665028389605539739947)
  ·
    refine ⟨30075997542584408309609921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20050665028389605539739947 30075997542584408309609921)
    ·
      refine ⟨22556998156938306232207441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30075997542584408309609921 22556998156938306232207441)
      ·
        refine ⟨16917748617703729674155581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22556998156938306232207441 16917748617703729674155581)
        ·
          refine ⟨6344155731638898627808343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16917748617703729674155581 6344155731638898627808343)
          ·
            refine ⟨9516233597458347941712515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6344155731638898627808343 9516233597458347941712515)
            ·
              refine ⟨14274350396187521912568773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516233597458347941712515 14274350396187521912568773)
              ·
                refine ⟨2676440699285160358606645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14274350396187521912568773 2676440699285160358606645)
                ·
                  refine ⟨250916315557983783619373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2676440699285160358606645 250916315557983783619373)
                  ·
                    rfl

theorem cell21_1099480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1099480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099480 prefixEnd_1099480 := by exact prefixLift 1099480
  have htrace : WordTrace (prefixWord ++ tailWord_1099480) baseStart_1099480 baseEnd_1099480 := by
    simpa [prefixWord, tailWord_1099480, baseEnd_1099480] using wordTrace_append hprefix tailTrace_1099480
  have hstable : (prefixWord ++ tailWord_1099480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099480).length < 2 ^ (prefixWord ++ tailWord_1099480).sum := by decide
  have hdescent : baseEnd_1099480 < baseStart_1099480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099587 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_1099587 : Nat := 118140960795 + 1099587 * 2 ^ 59
def prefixEnd_1099587 : Nat := 4983230072969 + 3 ^ 40 * 1099587 * 2
def baseEnd_1099587 : Nat := 250940734415775375335821

theorem tailTrace_1099587 : CollatzResearch.WordTrace tailWord_1099587 prefixEnd_1099587 250940734415775375335821 := by
  unfold tailWord_1099587
  simp only [CollatzResearch.WordTrace]
  refine ⟨40105232667391568353625015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26736821778261045569083343 40105232667391568353625015)
  ·
    refine ⟨60157849001087352530437523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40105232667391568353625015 60157849001087352530437523)
    ·
      refine ⟨90236773501631028795656285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60157849001087352530437523 90236773501631028795656285)
      ·
        refine ⟨33838790063111635798371107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90236773501631028795656285 33838790063111635798371107)
        ·
          refine ⟨50758185094667453697556661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33838790063111635798371107 50758185094667453697556661)
          ·
            refine ⟨4758579852625073784145937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50758185094667453697556661 4758579852625073784145937)
            ·
              refine ⟨3568934889468805338109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4758579852625073784145937 3568934889468805338109453)
              ·
                refine ⟨1338350583550802001791045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3568934889468805338109453 1338350583550802001791045)
                ·
                  refine ⟨250940734415775375335821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338350583550802001791045 250940734415775375335821)
                  ·
                    rfl

theorem cell21_1099587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_1099587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099587 prefixEnd_1099587 := by exact prefixLift 1099587
  have htrace : WordTrace (prefixWord ++ tailWord_1099587) baseStart_1099587 baseEnd_1099587 := by
    simpa [prefixWord, tailWord_1099587, baseEnd_1099587] using wordTrace_append hprefix tailTrace_1099587
  have hstable : (prefixWord ++ tailWord_1099587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099587).length < 2 ^ (prefixWord ++ tailWord_1099587).sum := by decide
  have hdescent : baseEnd_1099587 < baseStart_1099587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099590 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1099590 : Nat := 118140960795 + 1099590 * 2 ^ 59
def prefixEnd_1099590 : Nat := 4983230072969 + 3 ^ 40 * 1099590 * 2
def baseEnd_1099590 : Nat := 250941419056648036785815

theorem tailTrace_1099590 : CollatzResearch.WordTrace tailWord_1099590 prefixEnd_1099590 250941419056648036785815 := by
  unfold tailWord_1099590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253291940199396870812007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26736894724253799910656149 1253291940199396870812007)
  ·
    refine ⟨1879937910299095306218011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253291940199396870812007 1879937910299095306218011)
    ·
      refine ⟨2819906865448642959327017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879937910299095306218011 2819906865448642959327017)
      ·
        refine ⟨2114930149086482219495263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819906865448642959327017 2114930149086482219495263)
        ·
          refine ⟨3172395223629723329242895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114930149086482219495263 3172395223629723329242895)
          ·
            refine ⟨4758592835444584993864343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172395223629723329242895 4758592835444584993864343)
            ·
              refine ⟨7137889253166877490796515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758592835444584993864343 7137889253166877490796515)
              ·
                refine ⟨10706833879750316236194773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7137889253166877490796515 10706833879750316236194773)
                ·
                  refine ⟨250941419056648036785815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10706833879750316236194773 250941419056648036785815)
                  ·
                    rfl

theorem cell21_1099590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1099590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099590 prefixEnd_1099590 := by exact prefixLift 1099590
  have htrace : WordTrace (prefixWord ++ tailWord_1099590) baseStart_1099590 baseEnd_1099590 := by
    simpa [prefixWord, tailWord_1099590, baseEnd_1099590] using wordTrace_append hprefix tailTrace_1099590
  have hstable : (prefixWord ++ tailWord_1099590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099590).length < 2 ^ (prefixWord ++ tailWord_1099590).sum := by decide
  have hdescent : baseEnd_1099590 < baseStart_1099590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099618 : List Nat := [3, 3, 2, 1, 2, 2, 8]
def baseStart_1099618 : Nat := 118140960795 + 1099618 * 2 ^ 59
def prefixEnd_1099618 : Nat := 4983230072969 + 3 ^ 40 * 1099618 * 2
def baseEnd_1099618 : Nat := 27883089893125134479899

theorem tailTrace_1099618 : CollatzResearch.WordTrace tailWord_1099618 prefixEnd_1099618 27883089893125134479899 := by
  unfold tailWord_1099618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026590832569815162000877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26737575553519507098669005 10026590832569815162000877)
  ·
    refine ⟨3759971562213680685750329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10026590832569815162000877 3759971562213680685750329)
    ·
      refine ⟨2819978671660260514312747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3759971562213680685750329 2819978671660260514312747)
      ·
        refine ⟨4229968007490390771469121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819978671660260514312747 4229968007490390771469121)
        ·
          refine ⟨3172476005617793078601841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4229968007490390771469121 3172476005617793078601841)
          ·
            refine ⟨2379357004213344808951381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3172476005617793078601841 2379357004213344808951381)
            ·
              refine ⟨27883089893125134479899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2379357004213344808951381 27883089893125134479899)
              ·
                rfl

theorem cell21_1099618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 8].length) (baseStart_1099618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099618 prefixEnd_1099618 := by exact prefixLift 1099618
  have htrace : WordTrace (prefixWord ++ tailWord_1099618) baseStart_1099618 baseEnd_1099618 := by
    simpa [prefixWord, tailWord_1099618, baseEnd_1099618] using wordTrace_append hprefix tailTrace_1099618
  have hstable : (prefixWord ++ tailWord_1099618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099618).length < 2 ^ (prefixWord ++ tailWord_1099618).sum := by decide
  have hdescent : baseEnd_1099618 < baseStart_1099618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099638 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1099638 : Nat := 118140960795 + 1099638 * 2 ^ 59
def prefixEnd_1099638 : Nat := 4983230072969 + 3 ^ 40 * 1099638 * 2
def baseEnd_1099638 : Nat := 250952373310610619985717

theorem tailTrace_1099638 : CollatzResearch.WordTrace tailWord_1099638 prefixEnd_1099638 250952373310610619985717 := by
  unfold tailWord_1099638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506693299387925253983223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26738061860137869375821045 2506693299387925253983223)
  ·
    refine ⟨3760039949081887880974835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2506693299387925253983223 3760039949081887880974835)
    ·
      refine ⟨5640059923622831821462253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3760039949081887880974835 5640059923622831821462253)
      ·
        refine ⟨2115022471358561933048345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5640059923622831821462253 2115022471358561933048345)
        ·
          refine ⟨1586266853518921449786259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115022471358561933048345 1586266853518921449786259)
          ·
            refine ⟨2379400280278382174679389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586266853518921449786259 2379400280278382174679389)
            ·
              refine ⟨892275105104393315504771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2379400280278382174679389 892275105104393315504771)
              ·
                refine ⟨1338412657656589973257157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892275105104393315504771 1338412657656589973257157)
                ·
                  refine ⟨250952373310610619985717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338412657656589973257157 250952373310610619985717)
                  ·
                    rfl

theorem cell21_1099638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1099638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099638 prefixEnd_1099638 := by exact prefixLift 1099638
  have htrace : WordTrace (prefixWord ++ tailWord_1099638) baseStart_1099638 baseEnd_1099638 := by
    simpa [prefixWord, tailWord_1099638, baseEnd_1099638] using wordTrace_append hprefix tailTrace_1099638
  have hstable : (prefixWord ++ tailWord_1099638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099638).length < 2 ^ (prefixWord ++ tailWord_1099638).sum := by decide
  have hdescent : baseEnd_1099638 < baseStart_1099638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099677 : List Nat := [1, 4, 2, 1, 2, 2, 9]
def baseStart_1099677 : Nat := 118140960795 + 1099677 * 2 ^ 59
def prefixEnd_1099677 : Nat := 4983230072969 + 3 ^ 40 * 1099677 * 2
def baseEnd_1099677 : Nat := 27884585960217246537293

theorem tailTrace_1099677 : CollatzResearch.WordTrace tailWord_1099677 prefixEnd_1099677 27884585960217246537293 := by
  unfold tailWord_1099677
  simp only [CollatzResearch.WordTrace]
  refine ⟨40108515237065513724401285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26739010158043675816267523 40108515237065513724401285)
  ·
    refine ⟨7520346606949783823325241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40108515237065513724401285 7520346606949783823325241)
    ·
      refine ⟨5640259955212337867493931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7520346606949783823325241 5640259955212337867493931)
      ·
        refine ⟨8460389932818506801240897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640259955212337867493931 8460389932818506801240897)
        ·
          refine ⟨6345292449613880100930673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8460389932818506801240897 6345292449613880100930673)
          ·
            refine ⟨4758969337210410075698005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6345292449613880100930673 4758969337210410075698005)
            ·
              refine ⟨27884585960217246537293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4758969337210410075698005 27884585960217246537293)
              ·
                rfl

theorem cell21_1099677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 9].length) (baseStart_1099677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099677 prefixEnd_1099677 := by exact prefixLift 1099677
  have htrace : WordTrace (prefixWord ++ tailWord_1099677) baseStart_1099677 baseEnd_1099677 := by
    simpa [prefixWord, tailWord_1099677, baseEnd_1099677] using wordTrace_append hprefix tailTrace_1099677
  have hstable : (prefixWord ++ tailWord_1099677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099677).length < 2 ^ (prefixWord ++ tailWord_1099677).sum := by decide
  have hdescent : baseEnd_1099677 < baseStart_1099677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099697 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 4]
def baseStart_1099697 : Nat := 118140960795 + 1099697 * 2 ^ 59
def prefixEnd_1099697 : Nat := 4983230072969 + 3 ^ 40 * 1099697 * 2
def baseEnd_1099697 : Nat := 250965837914439628502263

theorem tailTrace_1099697 : CollatzResearch.WordTrace tailWord_1099697 prefixEnd_1099697 250965837914439628502263 := by
  unfold tailWord_1099697
  simp only [CollatzResearch.WordTrace]
  refine ⟨40109244696993057140129345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26739496464662038093419563 40109244696993057140129345)
  ·
    refine ⟨30081933522744792855097009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40109244696993057140129345 30081933522744792855097009)
    ·
      refine ⟨22561450142058594641322757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30081933522744792855097009 22561450142058594641322757)
      ·
        refine ⟨4230271901635986495248017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22561450142058594641322757 4230271901635986495248017)
        ·
          refine ⟨3172703926226989871436013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230271901635986495248017 3172703926226989871436013)
          ·
            refine ⟨1189763972335121201788505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3172703926226989871436013 1189763972335121201788505)
            ·
              refine ⟨892322979251340901341379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189763972335121201788505 892322979251340901341379)
              ·
                refine ⟨1338484468877011352012069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892322979251340901341379 1338484468877011352012069)
                ·
                  refine ⟨250965837914439628502263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338484468877011352012069 250965837914439628502263)
                  ·
                    rfl

theorem cell21_1099697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_1099697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099697 prefixEnd_1099697 := by exact prefixLift 1099697
  have htrace : WordTrace (prefixWord ++ tailWord_1099697) baseStart_1099697 baseEnd_1099697 := by
    simpa [prefixWord, tailWord_1099697, baseEnd_1099697] using wordTrace_append hprefix tailTrace_1099697
  have hstable : (prefixWord ++ tailWord_1099697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099697).length < 2 ^ (prefixWord ++ tailWord_1099697).sum := by decide
  have hdescent : baseEnd_1099697 < baseStart_1099697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099722 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1099722 : Nat := 118140960795 + 1099722 * 2 ^ 59
def prefixEnd_1099722 : Nat := 4983230072969 + 3 ^ 40 * 1099722 * 2
def baseEnd_1099722 : Nat := 250971543255045140585545

theorem tailTrace_1099722 : CollatzResearch.WordTrace tailWord_1099722 prefixEnd_1099722 250971543255045140585545 := by
  unfold tailWord_1099722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027539130475621602447355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26740104347934990939859613 10027539130475621602447355)
  ·
    refine ⟨15041308695713432403671033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10027539130475621602447355 15041308695713432403671033)
    ·
      refine ⟨11280981521785074302753275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15041308695713432403671033 11280981521785074302753275)
      ·
        refine ⟨16921472282677611454129913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11280981521785074302753275 16921472282677611454129913)
        ·
          refine ⟨12691104212008208590597435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16921472282677611454129913 12691104212008208590597435)
          ·
            refine ⟨19036656318012312885896153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12691104212008208590597435 19036656318012312885896153)
            ·
              refine ⟨14277492238509234664422115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19036656318012312885896153 14277492238509234664422115)
              ·
                refine ⟨21416238357763851996633173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14277492238509234664422115 21416238357763851996633173)
                ·
                  refine ⟨250971543255045140585545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21416238357763851996633173 250971543255045140585545)
                  ·
                    rfl

theorem cell21_1099722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1099722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099722 prefixEnd_1099722 := by exact prefixLift 1099722
  have htrace : WordTrace (prefixWord ++ tailWord_1099722) baseStart_1099722 baseEnd_1099722 := by
    simpa [prefixWord, tailWord_1099722, baseEnd_1099722] using wordTrace_append hprefix tailTrace_1099722
  have hstable : (prefixWord ++ tailWord_1099722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099722).length < 2 ^ (prefixWord ++ tailWord_1099722).sum := by decide
  have hdescent : baseEnd_1099722 < baseStart_1099722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099905 : List Nat := [1, 2, 4, 2, 3, 9]
def baseStart_1099905 : Nat := 118140960795 + 1099905 * 2 ^ 59
def prefixEnd_1099905 : Nat := 4983230072969 + 3 ^ 40 * 1099905 * 2
def baseEnd_1099905 : Nat := 9296789124010277371673

theorem tailTrace_1099905 : CollatzResearch.WordTrace tailWord_1099905 prefixEnd_1099905 9296789124010277371673 := by
  unfold tailWord_1099905
  simp only [CollatzResearch.WordTrace]
  refine ⟨40116831080239508663701169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26744554053493005775800779 40116831080239508663701169)
  ·
    refine ⟨30087623310179631497775877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40116831080239508663701169 30087623310179631497775877)
    ·
      refine ⟨5641429370658680905832977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30087623310179631497775877 5641429370658680905832977)
      ·
        refine ⟨4231072027994010679374733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5641429370658680905832977 4231072027994010679374733)
        ·
          refine ⟨1586652010497754004765525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4231072027994010679374733 1586652010497754004765525)
          ·
            refine ⟨9296789124010277371673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1586652010497754004765525 9296789124010277371673)
            ·
              rfl

theorem cell21_1099905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 9].length) (baseStart_1099905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099905 prefixEnd_1099905 := by exact prefixLift 1099905
  have htrace : WordTrace (prefixWord ++ tailWord_1099905) baseStart_1099905 baseEnd_1099905 := by
    simpa [prefixWord, tailWord_1099905, baseEnd_1099905] using wordTrace_append hprefix tailTrace_1099905
  have hstable : (prefixWord ++ tailWord_1099905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099905).length < 2 ^ (prefixWord ++ tailWord_1099905).sum := by decide
  have hdescent : baseEnd_1099905 < baseStart_1099905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099936 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1099936 : Nat := 118140960795 + 1099936 * 2 ^ 59
def prefixEnd_1099936 : Nat := 4983230072969 + 3 ^ 40 * 1099936 * 2
def baseEnd_1099936 : Nat := 251020380970628324018441

theorem tailTrace_1099936 : CollatzResearch.WordTrace tailWord_1099936 prefixEnd_1099936 251020380970628324018441 := by
  unfold tailWord_1099936
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058980871563600479039831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26745307828751467305386441 20058980871563600479039831)
  ·
    refine ⟨30088471307345400718559747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20058980871563600479039831 30088471307345400718559747)
    ·
      refine ⟨45132706961018101077839621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30088471307345400718559747 45132706961018101077839621)
      ·
        refine ⟨8462382555190893952094929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45132706961018101077839621 8462382555190893952094929)
        ·
          refine ⟨6346786916393170464071197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8462382555190893952094929 6346786916393170464071197)
          ·
            refine ⟨2380045093647438924026699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6346786916393170464071197 2380045093647438924026699)
            ·
              refine ⟨3570067640471158386040049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380045093647438924026699 3570067640471158386040049)
              ·
                refine ⟨2677550730353368789530037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570067640471158386040049 2677550730353368789530037)
                ·
                  refine ⟨251020380970628324018441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677550730353368789530037 251020380970628324018441)
                  ·
                    rfl

theorem cell21_1099936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1099936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099936 prefixEnd_1099936 := by exact prefixLift 1099936
  have htrace : WordTrace (prefixWord ++ tailWord_1099936) baseStart_1099936 baseEnd_1099936 := by
    simpa [prefixWord, tailWord_1099936, baseEnd_1099936] using wordTrace_append hprefix tailTrace_1099936
  have hstable : (prefixWord ++ tailWord_1099936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099936).length < 2 ^ (prefixWord ++ tailWord_1099936).sum := by decide
  have hdescent : baseEnd_1099936 < baseStart_1099936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099956 : List Nat := [2, 5, 3, 1, 1, 1, 8]
def baseStart_1099956 : Nat := 118140960795 + 1099956 * 2 ^ 59
def prefixEnd_1099956 : Nat := 4983230072969 + 3 ^ 40 * 1099956 * 2
def baseEnd_1099956 : Nat := 27891660582568081520563

theorem tailTrace_1099956 : CollatzResearch.WordTrace tailWord_1099956 prefixEnd_1099956 27891660582568081520563 := by
  unfold tailWord_1099956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20059345601527372186903861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26745794135369829582538481 20059345601527372186903861)
  ·
    refine ⟨1880563650143191142522237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20059345601527372186903861 1880563650143191142522237)
    ·
      refine ⟨705211368803696678445839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1880563650143191142522237 705211368803696678445839)
      ·
        refine ⟨1057817053205545017668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705211368803696678445839 1057817053205545017668759)
        ·
          refine ⟨1586725579808317526503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057817053205545017668759 1586725579808317526503139)
          ·
            refine ⟨2380088369712476289754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586725579808317526503139 2380088369712476289754709)
            ·
              refine ⟨27891660582568081520563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2380088369712476289754709 27891660582568081520563)
              ·
                rfl

theorem cell21_1099956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 8].length) (baseStart_1099956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099956 prefixEnd_1099956 := by exact prefixLift 1099956
  have htrace : WordTrace (prefixWord ++ tailWord_1099956) baseStart_1099956 baseEnd_1099956 := by
    simpa [prefixWord, tailWord_1099956, baseEnd_1099956] using wordTrace_append hprefix tailTrace_1099956
  have hstable : (prefixWord ++ tailWord_1099956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099956).length < 2 ^ (prefixWord ++ tailWord_1099956).sum := by decide
  have hdescent : baseEnd_1099956 < baseStart_1099956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099970 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1099970 : Nat := 118140960795 + 1099970 * 2 ^ 59
def prefixEnd_1099970 : Nat := 4983230072969 + 3 ^ 40 * 1099970 * 2
def baseEnd_1099970 : Nat := 251028140233851820451705

theorem tailTrace_1099970 : CollatzResearch.WordTrace tailWord_1099970 prefixEnd_1099970 251028140233851820451705 := by
  unfold tailWord_1099970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029800456251006191204341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26746134550002683176544909 10029800456251006191204341)
  ·
    refine ⟨940293792773531830425407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10029800456251006191204341 940293792773531830425407)
    ·
      refine ⟨1410440689160297745638111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940293792773531830425407 1410440689160297745638111)
      ·
        refine ⟨2115661033740446618457167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410440689160297745638111 2115661033740446618457167)
        ·
          refine ⟨3173491550610669927685751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115661033740446618457167 3173491550610669927685751)
          ·
            refine ⟨4760237325916004891528627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173491550610669927685751 4760237325916004891528627)
            ·
              refine ⟨7140355988874007337292941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760237325916004891528627 7140355988874007337292941)
              ·
                refine ⟨2677633495827752751484853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7140355988874007337292941 2677633495827752751484853)
                ·
                  refine ⟨251028140233851820451705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677633495827752751484853 251028140233851820451705)
                  ·
                    rfl

theorem cell21_1099970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1099970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1099970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1099970 prefixEnd_1099970 := by exact prefixLift 1099970
  have htrace : WordTrace (prefixWord ++ tailWord_1099970) baseStart_1099970 baseEnd_1099970 := by
    simpa [prefixWord, tailWord_1099970, baseEnd_1099970] using wordTrace_append hprefix tailTrace_1099970
  have hstable : (prefixWord ++ tailWord_1099970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099970).length < 2 ^ (prefixWord ++ tailWord_1099970).sum := by decide
  have hdescent : baseEnd_1099970 < baseStart_1099970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100026 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1100026 : Nat := 118140960795 + 1100026 * 2 ^ 59
def prefixEnd_1100026 : Nat := 4983230072969 + 3 ^ 40 * 1100026 * 2
def baseEnd_1100026 : Nat := 251040920196808167518257

theorem tailTrace_1100026 : CollatzResearch.WordTrace tailWord_1100026 prefixEnd_1100026 251040920196808167518257 := by
  unfold tailWord_1100026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030311078200286582213983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26747496208534097552570621 10030311078200286582213983)
  ·
    refine ⟨15045466617300429873320975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030311078200286582213983 15045466617300429873320975)
    ·
      refine ⟨22568199925950644809981463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15045466617300429873320975 22568199925950644809981463)
      ·
        refine ⟨33852299888925967214972195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22568199925950644809981463 33852299888925967214972195)
        ·
          refine ⟨50778449833388950822458293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33852299888925967214972195 50778449833388950822458293)
          ·
            refine ⟨4760479671880214139605465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50778449833388950822458293 4760479671880214139605465)
            ·
              refine ⟨3570359753910160604704099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760479671880214139605465 3570359753910160604704099)
              ·
                refine ⟨5355539630865240907056149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570359753910160604704099 5355539630865240907056149)
                ·
                  refine ⟨251040920196808167518257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5355539630865240907056149 251040920196808167518257)
                  ·
                    rfl

theorem cell21_1100026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1100026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100026 prefixEnd_1100026 := by exact prefixLift 1100026
  have htrace : WordTrace (prefixWord ++ tailWord_1100026) baseStart_1100026 baseEnd_1100026 := by
    simpa [prefixWord, tailWord_1100026, baseEnd_1100026] using wordTrace_append hprefix tailTrace_1100026
  have hstable : (prefixWord ++ tailWord_1100026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100026).length < 2 ^ (prefixWord ++ tailWord_1100026).sum := by decide
  have hdescent : baseEnd_1100026 < baseStart_1100026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100074 : List Nat := [3, 1, 4, 2, 3, 8]
def baseStart_1100074 : Nat := 118140960795 + 1100074 * 2 ^ 59
def prefixEnd_1100074 : Nat := 4983230072969 + 3 ^ 40 * 1100074 * 2
def baseEnd_1100074 : Nat := 9298217572250768545117

theorem tailTrace_1100074 : CollatzResearch.WordTrace tailWord_1100074 prefixEnd_1100074 9298217572250768545117 := by
  unfold tailWord_1100074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030748754156812631650819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26748663344418167017735517 10030748754156812631650819)
  ·
    refine ⟨15046123131235218947476229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030748754156812631650819 15046123131235218947476229)
    ·
      refine ⟨2821148087106603552651793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15046123131235218947476229 2821148087106603552651793)
      ·
        refine ⟨2115861065329952664488845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2821148087106603552651793 2115861065329952664488845)
        ·
          refine ⟨793447899498732249183317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2115861065329952664488845 793447899498732249183317)
          ·
            refine ⟨9298217572250768545117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 793447899498732249183317 9298217572250768545117)
            ·
              rfl

theorem cell21_1100074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 8].length) (baseStart_1100074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100074 prefixEnd_1100074 := by exact prefixLift 1100074
  have htrace : WordTrace (prefixWord ++ tailWord_1100074) baseStart_1100074 baseEnd_1100074 := by
    simpa [prefixWord, tailWord_1100074, baseEnd_1100074] using wordTrace_append hprefix tailTrace_1100074
  have hstable : (prefixWord ++ tailWord_1100074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100074).length < 2 ^ (prefixWord ++ tailWord_1100074).sum := by decide
  have hdescent : baseEnd_1100074 < baseStart_1100074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100077 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1100077 : Nat := 118140960795 + 1100077 * 2 ^ 59
def prefixEnd_1100077 : Nat := 4983230072969 + 3 ^ 40 * 1100077 * 2
def baseEnd_1100077 : Nat := 251052559091643412168153

theorem tailTrace_1100077 : CollatzResearch.WordTrace tailWord_1100077 prefixEnd_1100077 251052559091643412168153 := by
  unfold tailWord_1100077
  simp only [CollatzResearch.WordTrace]
  refine ⟨40123104435616382038962485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26748736290410921359308323 40123104435616382038962485)
  ·
    refine ⟨3761541040839035816152733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40123104435616382038962485 3761541040839035816152733)
    ·
      refine ⟨1410577890314638431057275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3761541040839035816152733 1410577890314638431057275)
      ·
        refine ⟨2115866835471957646585913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410577890314638431057275 2115866835471957646585913)
        ·
          refine ⟨1586900126603968234939435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115866835471957646585913 1586900126603968234939435)
          ·
            refine ⟨2380350189905952352409153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586900126603968234939435 2380350189905952352409153)
            ·
              refine ⟨1785262642429464264306865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380350189905952352409153 1785262642429464264306865)
              ·
                refine ⟨1338946981822098198230149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785262642429464264306865 1338946981822098198230149)
                ·
                  refine ⟨251052559091643412168153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338946981822098198230149 251052559091643412168153)
                  ·
                    rfl

theorem cell21_1100077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1100077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100077 prefixEnd_1100077 := by exact prefixLift 1100077
  have htrace : WordTrace (prefixWord ++ tailWord_1100077) baseStart_1100077 baseEnd_1100077 := by
    simpa [prefixWord, tailWord_1100077, baseEnd_1100077] using wordTrace_append hprefix tailTrace_1100077
  have hstable : (prefixWord ++ tailWord_1100077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100077).length < 2 ^ (prefixWord ++ tailWord_1100077).sum := by decide
  have hdescent : baseEnd_1100077 < baseStart_1100077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100136 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_1100136 : Nat := 118140960795 + 1100136 * 2 ^ 59
def prefixEnd_1100136 : Nat := 4983230072969 + 3 ^ 40 * 1100136 * 2
def baseEnd_1100136 : Nat := 251066023695472420684699

theorem tailTrace_1100136 : CollatzResearch.WordTrace tailWord_1100136 prefixEnd_1100136 251066023695472420684699 := by
  unfold tailWord_1100136
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062628171201317557680131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26750170894935090076906841 20062628171201317557680131)
  ·
    refine ⟨30093942256801976336520197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20062628171201317557680131 30093942256801976336520197)
    ·
      refine ⟨5642614173150370563097537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30093942256801976336520197 5642614173150370563097537)
      ·
        refine ⟨4231960629862777922323153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642614173150370563097537 4231960629862777922323153)
        ·
          refine ⟨3173970472397083441742365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231960629862777922323153 3173970472397083441742365)
          ·
            refine ⟨1190238927148906290653387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3173970472397083441742365 1190238927148906290653387)
            ·
              refine ⟨1785358390723359435980081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190238927148906290653387 1785358390723359435980081)
              ·
                refine ⟨1339018793042519576985061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785358390723359435980081 1339018793042519576985061)
                ·
                  refine ⟨251066023695472420684699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339018793042519576985061 251066023695472420684699)
                  ·
                    rfl

theorem cell21_1100136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_1100136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100136 prefixEnd_1100136 := by exact prefixLift 1100136
  have htrace : WordTrace (prefixWord ++ tailWord_1100136) baseStart_1100136 baseEnd_1100136 := by
    simpa [prefixWord, tailWord_1100136, baseEnd_1100136] using wordTrace_append hprefix tailTrace_1100136
  have hstable : (prefixWord ++ tailWord_1100136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100136).length < 2 ^ (prefixWord ++ tailWord_1100136).sum := by decide
  have hdescent : baseEnd_1100136 < baseStart_1100136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100192 : List Nat := [2, 1, 1, 4, 1, 3, 9]
def baseStart_1100192 : Nat := 118140960795 + 1100192 * 2 ^ 59
def prefixEnd_1100192 : Nat := 4983230072969 + 3 ^ 40 * 1100192 * 2
def baseEnd_1100192 : Nat := 27897644850936529750139

theorem tailTrace_1100192 : CollatzResearch.WordTrace tailWord_1100192 prefixEnd_1100192 27897644850936529750139 := by
  unfold tailWord_1100192
  simp only [CollatzResearch.WordTrace]
  refine ⟨20063649415099878339699415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26751532553466504452932553 20063649415099878339699415)
  ·
    refine ⟨30095474122649817509549123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20063649415099878339699415 30095474122649817509549123)
    ·
      refine ⟨45143211183974726264323685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30095474122649817509549123 45143211183974726264323685)
      ·
        refine ⟨8464352096995261174560691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45143211183974726264323685 8464352096995261174560691)
        ·
          refine ⟨12696528145492891761841037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464352096995261174560691 12696528145492891761841037)
          ·
            refine ⟨4761198054559834410690389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12696528145492891761841037 4761198054559834410690389)
            ·
              refine ⟨27897644850936529750139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4761198054559834410690389 27897644850936529750139)
              ·
                rfl

theorem cell21_1100192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 9].length) (baseStart_1100192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100192 prefixEnd_1100192 := by exact prefixLift 1100192
  have htrace : WordTrace (prefixWord ++ tailWord_1100192) baseStart_1100192 baseEnd_1100192 := by
    simpa [prefixWord, tailWord_1100192, baseEnd_1100192] using wordTrace_append hprefix tailTrace_1100192
  have hstable : (prefixWord ++ tailWord_1100192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100192).length < 2 ^ (prefixWord ++ tailWord_1100192).sum := by decide
  have hdescent : baseEnd_1100192 < baseStart_1100192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100209 : List Nat := [1, 2, 2, 4, 1, 3, 2, 6]
def baseStart_1100209 : Nat := 118140960795 + 1100209 * 2 ^ 59
def prefixEnd_1100209 : Nat := 4983230072969 + 3 ^ 40 * 1100209 * 2
def baseEnd_1100209 : Nat := 83694227763346838655961

theorem tailTrace_1100209 : CollatzResearch.WordTrace tailWord_1100209 prefixEnd_1100209 83694227763346838655961 := by
  unfold tailWord_1100209
  simp only [CollatzResearch.WordTrace]
  refine ⟨40127918871138168582767681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26751945914092112388511787 40127918871138168582767681)
  ·
    refine ⟨30095939153353626437075761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40127918871138168582767681 30095939153353626437075761)
    ·
      refine ⟨22571954365015219827806821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30095939153353626437075761 22571954365015219827806821)
      ·
        refine ⟨4232241443440353717713779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22571954365015219827806821 4232241443440353717713779)
        ·
          refine ⟨6348362165160530576570669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232241443440353717713779 6348362165160530576570669)
          ·
            refine ⟨2380635811935198966214001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6348362165160530576570669 2380635811935198966214001)
            ·
              refine ⟨1785476858951399224660501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380635811935198966214001 1785476858951399224660501)
              ·
                refine ⟨83694227763346838655961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1785476858951399224660501 83694227763346838655961)
                ·
                  rfl

theorem cell21_1100209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_1100209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100209 prefixEnd_1100209 := by exact prefixLift 1100209
  have htrace : WordTrace (prefixWord ++ tailWord_1100209) baseStart_1100209 baseEnd_1100209 := by
    simpa [prefixWord, tailWord_1100209, baseEnd_1100209] using wordTrace_append hprefix tailTrace_1100209
  have hstable : (prefixWord ++ tailWord_1100209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100209).length < 2 ^ (prefixWord ++ tailWord_1100209).sum := by decide
  have hdescent : baseEnd_1100209 < baseStart_1100209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100285 : List Nat := [1, 4, 1, 1, 1, 3, 5, 5]
def baseStart_1100285 : Nat := 118140960795 + 1100285 * 2 ^ 59
def prefixEnd_1100285 : Nat := 4983230072969 + 3 ^ 40 * 1100285 * 2
def baseEnd_1100285 : Nat := 83700009175160424233687

theorem tailTrace_1100285 : CollatzResearch.WordTrace tailWord_1100285 prefixEnd_1100285 83700009175160424233687 := by
  unfold tailWord_1100285
  simp only [CollatzResearch.WordTrace]
  refine ⟨40130690818862833562534309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26753793879241889041689539 40130690818862833562534309)
  ·
    refine ⟨7524504528536781292975183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40130690818862833562534309 7524504528536781292975183)
    ·
      refine ⟨11286756792805171939462775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7524504528536781292975183 11286756792805171939462775)
      ·
        refine ⟨16930135189207757909194163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286756792805171939462775 16930135189207757909194163)
        ·
          refine ⟨25395202783811636863791245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16930135189207757909194163 25395202783811636863791245)
          ·
            refine ⟨9523201043929363823921717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25395202783811636863791245 9523201043929363823921717)
            ·
              refine ⟨892800097868377858492661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9523201043929363823921717 892800097868377858492661)
              ·
                refine ⟨83700009175160424233687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 892800097868377858492661 83700009175160424233687)
                ·
                  rfl

theorem cell21_1100285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].length) (baseStart_1100285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100285 prefixEnd_1100285 := by exact prefixLift 1100285
  have htrace : WordTrace (prefixWord ++ tailWord_1100285) baseStart_1100285 baseEnd_1100285 := by
    simpa [prefixWord, tailWord_1100285, baseEnd_1100285] using wordTrace_append hprefix tailTrace_1100285
  have hstable : (prefixWord ++ tailWord_1100285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100285).length < 2 ^ (prefixWord ++ tailWord_1100285).sum := by decide
  have hdescent : baseEnd_1100285 < baseStart_1100285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100313 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1100313 : Nat := 118140960795 + 1100313 * 2 ^ 59
def prefixEnd_1100313 : Nat := 4983230072969 + 3 ^ 40 * 1100313 * 2
def baseEnd_1100313 : Nat := 251106417506959446234337

theorem tailTrace_1100313 : CollatzResearch.WordTrace tailWord_1100313 prefixEnd_1100313 251106417506959446234337 := by
  unfold tailWord_1100313
  simp only [CollatzResearch.WordTrace]
  refine ⟨40131712062761394344553593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26754474708507596229702395 40131712062761394344553593)
  ·
    refine ⟨30098784047071045758415195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40131712062761394344553593 30098784047071045758415195)
    ·
      refine ⟨45148176070606568637622793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30098784047071045758415195 45148176070606568637622793)
      ·
        refine ⟨33861132052954926478217095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45148176070606568637622793 33861132052954926478217095)
        ·
          refine ⟨50791698079432389717325643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33861132052954926478217095 50791698079432389717325643)
          ·
            refine ⟨76187547119148584575988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50791698079432389717325643 76187547119148584575988465)
            ·
              refine ⟨57140660339361438431991349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76187547119148584575988465 57140660339361438431991349)
              ·
                refine ⟨5356936906815134852999189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57140660339361438431991349 5356936906815134852999189)
                ·
                  refine ⟨251106417506959446234337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5356936906815134852999189 251106417506959446234337)
                  ·
                    rfl

theorem cell21_1100313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1100313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100313 prefixEnd_1100313 := by exact prefixLift 1100313
  have htrace : WordTrace (prefixWord ++ tailWord_1100313) baseStart_1100313 baseEnd_1100313 := by
    simpa [prefixWord, tailWord_1100313, baseEnd_1100313] using wordTrace_append hprefix tailTrace_1100313
  have hstable : (prefixWord ++ tailWord_1100313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100313).length < 2 ^ (prefixWord ++ tailWord_1100313).sum := by decide
  have hdescent : baseEnd_1100313 < baseStart_1100313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100316 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1100316 : Nat := 118140960795 + 1100316 * 2 ^ 59
def prefixEnd_1100316 : Nat := 4983230072969 + 3 ^ 40 * 1100316 * 2
def baseEnd_1100316 : Nat := 251107102147832107684331

theorem tailTrace_1100316 : CollatzResearch.WordTrace tailWord_1100316 prefixEnd_1100316 251107102147832107684331 := by
  unfold tailWord_1100316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20065910740875262928456401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26754547654500350571275201 20065910740875262928456401)
  ·
    refine ⟨15049433055656447196342301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20065910740875262928456401 15049433055656447196342301)
    ·
      refine ⟨5643537395871167698628363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15049433055656447196342301 5643537395871167698628363)
      ·
        refine ⟨8465306093806751547942545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643537395871167698628363 8465306093806751547942545)
        ·
          refine ⟨6348979570355063660956909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8465306093806751547942545 6348979570355063660956909)
          ·
            refine ⟨2380867338883148872858841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6348979570355063660956909 2380867338883148872858841)
            ·
              refine ⟨1785650504162361654644131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380867338883148872858841 1785650504162361654644131)
              ·
                refine ⟨2678475756243542481966197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785650504162361654644131 2678475756243542481966197)
                ·
                  refine ⟨251107102147832107684331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678475756243542481966197 251107102147832107684331)
                  ·
                    rfl

theorem cell21_1100316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1100316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100316 prefixEnd_1100316 := by exact prefixLift 1100316
  have htrace : WordTrace (prefixWord ++ tailWord_1100316) baseStart_1100316 baseEnd_1100316 := by
    simpa [prefixWord, tailWord_1100316, baseEnd_1100316] using wordTrace_append hprefix tailTrace_1100316
  have hstable : (prefixWord ++ tailWord_1100316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100316).length < 2 ^ (prefixWord ++ tailWord_1100316).sum := by decide
  have hdescent : baseEnd_1100316 < baseStart_1100316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100344 : List Nat := [2, 1, 2, 1, 4, 1, 3, 7]
def baseStart_1100344 : Nat := 118140960795 + 1100344 * 2 ^ 59
def prefixEnd_1100344 : Nat := 4983230072969 + 3 ^ 40 * 1100344 * 2
def baseEnd_1100344 : Nat := 83704497376436760405869

theorem tailTrace_1100344 : CollatzResearch.WordTrace tailWord_1100344 prefixEnd_1100344 83704497376436760405869 := by
  unfold tailWord_1100344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066421362824543319466043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26755228483766057759288057 20066421362824543319466043)
  ·
    refine ⟨30099632044236814979199065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066421362824543319466043 30099632044236814979199065)
    ·
      refine ⟨22574724033177611234399299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30099632044236814979199065 22574724033177611234399299)
      ·
        refine ⟨33862086049766416851598949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22574724033177611234399299 33862086049766416851598949)
        ·
          refine ⟨6349141134331203159674803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33862086049766416851598949 6349141134331203159674803)
          ·
            refine ⟨9523711701496804739512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349141134331203159674803 9523711701496804739512205)
            ·
              refine ⟨3571391888061301777317077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9523711701496804739512205 3571391888061301777317077)
              ·
                refine ⟨83704497376436760405869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3571391888061301777317077 83704497376436760405869)
                ·
                  rfl

theorem cell21_1100344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_1100344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100344 prefixEnd_1100344 := by exact prefixLift 1100344
  have htrace : WordTrace (prefixWord ++ tailWord_1100344) baseStart_1100344 baseEnd_1100344 := by
    simpa [prefixWord, tailWord_1100344, baseEnd_1100344] using wordTrace_append hprefix tailTrace_1100344
  have hstable : (prefixWord ++ tailWord_1100344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100344).length < 2 ^ (prefixWord ++ tailWord_1100344).sum := by decide
  have hdescent : baseEnd_1100344 < baseStart_1100344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100418 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1100418 : Nat := 118140960795 + 1100418 * 2 ^ 59
def prefixEnd_1100418 : Nat := 4983230072969 + 3 ^ 40 * 1100418 * 2
def baseEnd_1100418 : Nat := 251130379937502596984123

theorem tailTrace_1100418 : CollatzResearch.WordTrace tailWord_1100418 prefixEnd_1100418 251130379937502596984123 := by
  unfold tailWord_1100418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033885431845249319281477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26757027818253998184750605 10033885431845249319281477)
  ·
    refine ⟨1881353518470984247365277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10033885431845249319281477 1881353518470984247365277)
    ·
      refine ⟨705507569426619092761979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1881353518470984247365277 705507569426619092761979)
      ·
        refine ⟨1058261354139928639142969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705507569426619092761979 1058261354139928639142969)
        ·
          refine ⟨793696015604946479357227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058261354139928639142969 793696015604946479357227)
          ·
            refine ⟨1190544023407419719035841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793696015604946479357227 1190544023407419719035841)
            ·
              refine ⟨892908017555564789276881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190544023407419719035841 892908017555564789276881)
              ·
                refine ⟨669681013166673591957661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892908017555564789276881 669681013166673591957661)
                ·
                  refine ⟨251130379937502596984123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669681013166673591957661 251130379937502596984123)
                  ·
                    rfl

theorem cell21_1100418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1100418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100418 prefixEnd_1100418 := by exact prefixLift 1100418
  have htrace : WordTrace (prefixWord ++ tailWord_1100418) baseStart_1100418 baseEnd_1100418 := by
    simpa [prefixWord, tailWord_1100418, baseEnd_1100418] using wordTrace_append hprefix tailTrace_1100418
  have hstable : (prefixWord ++ tailWord_1100418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100418).length < 2 ^ (prefixWord ++ tailWord_1100418).sum := by decide
  have hdescent : baseEnd_1100418 < baseStart_1100418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100420 : List Nat := [2, 3, 2, 1, 3, 10]
def baseStart_1100420 : Nat := 118140960795 + 1100420 * 2 ^ 59
def prefixEnd_1100420 : Nat := 4983230072969 + 3 ^ 40 * 1100420 * 2
def baseEnd_1100420 : Nat := 9301142087583371775955

theorem tailTrace_1100420 : CollatzResearch.WordTrace tailWord_1100420 prefixEnd_1100420 9301142087583371775955 := by
  unfold tailWord_1100420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067807336686875809349357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26757076448915834412465809 20067807336686875809349357)
  ·
    refine ⟨7525427751257578428506009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20067807336686875809349357 7525427751257578428506009)
    ·
      refine ⟨5644070813443183821379507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7525427751257578428506009 5644070813443183821379507)
      ·
        refine ⟨8466106220164775732069261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644070813443183821379507 8466106220164775732069261)
        ·
          refine ⟨3174789832561790899525973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8466106220164775732069261 3174789832561790899525973)
          ·
            refine ⟨9301142087583371775955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3174789832561790899525973 9301142087583371775955)
            ·
              rfl

theorem cell21_1100420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 10].length) (baseStart_1100420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100420 prefixEnd_1100420 := by exact prefixLift 1100420
  have htrace : WordTrace (prefixWord ++ tailWord_1100420) baseStart_1100420 baseEnd_1100420 := by
    simpa [prefixWord, tailWord_1100420, baseEnd_1100420] using wordTrace_append hprefix tailTrace_1100420
  have hstable : (prefixWord ++ tailWord_1100420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100420).length < 2 ^ (prefixWord ++ tailWord_1100420).sum := by decide
  have hdescent : baseEnd_1100420 < baseStart_1100420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100513 : List Nat := [1, 2, 3, 1, 4, 1, 4, 5]
def baseStart_1100513 : Nat := 118140960795 + 1100513 * 2 ^ 59
def prefixEnd_1100513 : Nat := 4983230072969 + 3 ^ 40 * 1100513 * 2
def baseEnd_1100513 : Nat := 83717353410601180966865

theorem tailTrace_1100513 : CollatzResearch.WordTrace tailWord_1100513 prefixEnd_1100513 83717353410601180966865 := by
  unfold tailWord_1100513
  simp only [CollatzResearch.WordTrace]
  refine ⟨40139006662036828501834193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26759337774691219001222795 40139006662036828501834193)
  ·
    refine ⟨30104254996527621376375645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40139006662036828501834193 30104254996527621376375645)
    ·
      refine ⟨11289095623697858016140867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30104254996527621376375645 11289095623697858016140867)
      ·
        refine ⟨16933643435546787024211301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11289095623697858016140867 16933643435546787024211301)
        ·
          refine ⟨3175058144165022567039619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16933643435546787024211301 3175058144165022567039619)
          ·
            refine ⟨4762587216247533850559429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175058144165022567039619 4762587216247533850559429)
            ·
              refine ⟨892985103046412596979893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4762587216247533850559429 892985103046412596979893)
              ·
                refine ⟨83717353410601180966865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 892985103046412596979893 83717353410601180966865)
                ·
                  rfl

theorem cell21_1100513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].length) (baseStart_1100513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100513 prefixEnd_1100513 := by exact prefixLift 1100513
  have htrace : WordTrace (prefixWord ++ tailWord_1100513) baseStart_1100513 baseEnd_1100513 := by
    simpa [prefixWord, tailWord_1100513, baseEnd_1100513] using wordTrace_append hprefix tailTrace_1100513
  have hstable : (prefixWord ++ tailWord_1100513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100513).length < 2 ^ (prefixWord ++ tailWord_1100513).sum := by decide
  have hdescent : baseEnd_1100513 < baseStart_1100513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100541 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1100541 : Nat := 118140960795 + 1100541 * 2 ^ 59
def prefixEnd_1100541 : Nat := 4983230072969 + 3 ^ 40 * 1100541 * 2
def baseEnd_1100541 : Nat := 251158450213281716433871

theorem tailTrace_1100541 : CollatzResearch.WordTrace tailWord_1100541 prefixEnd_1100541 251158450213281716433871 := by
  unfold tailWord_1100541
  simp only [CollatzResearch.WordTrace]
  refine ⟨40140027905935389283853477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26760018603956926189235651 40140027905935389283853477)
  ·
    refine ⟨7526255232362885490722527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40140027905935389283853477 7526255232362885490722527)
    ·
      refine ⟨11289382848544328236083791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7526255232362885490722527 11289382848544328236083791)
      ·
        refine ⟨16934074272816492354125687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11289382848544328236083791 16934074272816492354125687)
        ·
          refine ⟨25401111409224738531188531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16934074272816492354125687 25401111409224738531188531)
          ·
            refine ⟨38101667113837107796782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25401111409224738531188531 38101667113837107796782797)
            ·
              refine ⟨14288125167688915423793549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38101667113837107796782797 14288125167688915423793549)
              ·
                refine ⟨5358046937883343283922581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14288125167688915423793549 5358046937883343283922581)
                ·
                  refine ⟨251158450213281716433871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5358046937883343283922581 251158450213281716433871)
                  ·
                    rfl

theorem cell21_1100541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1100541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100541 prefixEnd_1100541 := by exact prefixLift 1100541
  have htrace : WordTrace (prefixWord ++ tailWord_1100541) baseStart_1100541 baseEnd_1100541 := by
    simpa [prefixWord, tailWord_1100541, baseEnd_1100541] using wordTrace_append hprefix tailTrace_1100541
  have hstable : (prefixWord ++ tailWord_1100541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100541).length < 2 ^ (prefixWord ++ tailWord_1100541).sum := by decide
  have hdescent : baseEnd_1100541 < baseStart_1100541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100572 : List Nat := [2, 2, 3, 1, 1, 3, 2, 7]
def baseStart_1100572 : Nat := 118140960795 + 1100572 * 2 ^ 59
def prefixEnd_1100572 : Nat := 4983230072969 + 3 ^ 40 * 1100572 * 2
def baseEnd_1100572 : Nat := 83721841611877517139047

theorem tailTrace_1100572 : CollatzResearch.WordTrace tailWord_1100572 prefixEnd_1100572 83721841611877517139047 := by
  unfold tailWord_1100572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070579284411540789115985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26760772379215387718821313 20070579284411540789115985)
  ·
    refine ⟨15052934463308655591836989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20070579284411540789115985 15052934463308655591836989)
    ·
      refine ⟨5644850423740745846938871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15052934463308655591836989 5644850423740745846938871)
      ·
        refine ⟨8467275635611118770408307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644850423740745846938871 8467275635611118770408307)
        ·
          refine ⟨12700913453416678155612461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467275635611118770408307 12700913453416678155612461)
          ·
            refine ⟨4762842545031254308354673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12700913453416678155612461 4762842545031254308354673)
            ·
              refine ⟨3572131908773440731266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762842545031254308354673 3572131908773440731266005)
              ·
                refine ⟨83721841611877517139047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3572131908773440731266005 83721841611877517139047)
                ·
                  rfl

theorem cell21_1100572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_1100572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100572 prefixEnd_1100572 := by exact prefixLift 1100572
  have htrace : WordTrace (prefixWord ++ tailWord_1100572) baseStart_1100572 baseEnd_1100572 := by
    simpa [prefixWord, tailWord_1100572, baseEnd_1100572] using wordTrace_append hprefix tailTrace_1100572
  have hstable : (prefixWord ++ tailWord_1100572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100572).length < 2 ^ (prefixWord ++ tailWord_1100572).sum := by decide
  have hdescent : baseEnd_1100572 < baseStart_1100572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100589 : List Nat := [1, 5, 3, 2, 10]
def baseStart_1100589 : Nat := 118140960795 + 1100589 * 2 ^ 59
def prefixEnd_1100589 : Nat := 4983230072969 + 3 ^ 40 * 1100589 * 2
def baseEnd_1100589 : Nat := 3100856845274620983133

theorem tailTrace_1100589 : CollatzResearch.WordTrace tailWord_1100589 prefixEnd_1100589 3100856845274620983133 := by
  unfold tailWord_1100589
  simp only [CollatzResearch.WordTrace]
  refine ⟨40141778609761493481600821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26761185739840995654400547 40141778609761493481600821)
  ·
    refine ⟨3763291744665140013900077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40141778609761493481600821 3763291744665140013900077)
    ·
      refine ⟨1411234404249427505212529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3763291744665140013900077 1411234404249427505212529)
      ·
        refine ⟨1058425803187070628909397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411234404249427505212529 1058425803187070628909397)
        ·
          refine ⟨3100856845274620983133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1058425803187070628909397 3100856845274620983133)
          ·
            rfl

theorem cell21_1100589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 10].length) (baseStart_1100589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100589 prefixEnd_1100589 := by exact prefixLift 1100589
  have htrace : WordTrace (prefixWord ++ tailWord_1100589) baseStart_1100589 baseEnd_1100589 := by
    simpa [prefixWord, tailWord_1100589, baseEnd_1100589] using wordTrace_append hprefix tailTrace_1100589
  have hstable : (prefixWord ++ tailWord_1100589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100589).length < 2 ^ (prefixWord ++ tailWord_1100589).sum := by decide
  have hdescent : baseEnd_1100589 < baseStart_1100589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100606 : List Nat := [4, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1100606 : Nat := 118140960795 + 1100606 * 2 ^ 59
def prefixEnd_1100606 : Nat := 4983230072969 + 3 ^ 40 * 1100606 * 2
def baseEnd_1100606 : Nat := 83724428032952015950135

theorem tailTrace_1100606 : CollatzResearch.WordTrace tailWord_1100606 prefixEnd_1100606 83724428032952015950135 := by
  unfold tailWord_1100606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017799831337488173121209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26761599100466603589979781 5017799831337488173121209)
  ·
    refine ⟨3763349873503116129840907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5017799831337488173121209 3763349873503116129840907)
    ·
      refine ⟨5645024810254674194761361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763349873503116129840907 5645024810254674194761361)
      ·
        refine ⟨4233768607691005646071021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5645024810254674194761361 4233768607691005646071021)
        ·
          refine ⟨1587663227884127117276633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4233768607691005646071021 1587663227884127117276633)
          ·
            refine ⟨1190747420913095337957475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587663227884127117276633 1190747420913095337957475)
            ·
              refine ⟨1786121131369643006936213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190747420913095337957475 1786121131369643006936213)
              ·
                refine ⟨83724428032952015950135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786121131369643006936213 83724428032952015950135)
                ·
                  rfl

theorem cell21_1100606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1100606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100606 prefixEnd_1100606 := by exact prefixLift 1100606
  have htrace : WordTrace (prefixWord ++ tailWord_1100606) baseStart_1100606 baseEnd_1100606 := by
    simpa [prefixWord, tailWord_1100606, baseEnd_1100606] using wordTrace_append hprefix tailTrace_1100606
  have hstable : (prefixWord ++ tailWord_1100606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100606).length < 2 ^ (prefixWord ++ tailWord_1100606).sum := by decide
  have hdescent : baseEnd_1100606 < baseStart_1100606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100648 : List Nat := [2, 1, 4, 2, 1, 3, 8]
def baseStart_1100648 : Nat := 118140960795 + 1100648 * 2 ^ 59
def prefixEnd_1100648 : Nat := 4983230072969 + 3 ^ 40 * 1100648 * 2
def baseEnd_1100648 : Nat := 27909207674563700905591

theorem tailTrace_1100648 : CollatzResearch.WordTrace tailWord_1100648 prefixEnd_1100648 27909207674563700905591 := by
  unfold tailWord_1100648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20071965258273873278999299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26762620344365164371999065 20071965258273873278999299)
  ·
    refine ⟨30107947887410809918498949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20071965258273873278999299 30107947887410809918498949)
    ·
      refine ⟨5645240228889526859718553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30107947887410809918498949 5645240228889526859718553)
      ·
        refine ⟨4233930171667145144788915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5645240228889526859718553 4233930171667145144788915)
        ·
          refine ⟨6350895257500717717183373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233930171667145144788915 6350895257500717717183373)
          ·
            refine ⟨2381585721562769143943765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6350895257500717717183373 2381585721562769143943765)
            ·
              refine ⟨27909207674563700905591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2381585721562769143943765 27909207674563700905591)
              ·
                rfl

theorem cell21_1100648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 8].length) (baseStart_1100648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100648 prefixEnd_1100648 := by exact prefixLift 1100648
  have htrace : WordTrace (prefixWord ++ tailWord_1100648) baseStart_1100648 baseEnd_1100648 := by
    simpa [prefixWord, tailWord_1100648, baseEnd_1100648] using wordTrace_append hprefix tailTrace_1100648
  have hstable : (prefixWord ++ tailWord_1100648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100648).length < 2 ^ (prefixWord ++ tailWord_1100648).sum := by decide
  have hdescent : baseEnd_1100648 < baseStart_1100648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100679 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_1100679 : Nat := 118140960795 + 1100679 * 2 ^ 59
def prefixEnd_1100679 : Nat := 4983230072969 + 3 ^ 40 * 1100679 * 2
def baseEnd_1100679 : Nat := 251189943693424143133589

theorem tailTrace_1100679 : CollatzResearch.WordTrace tailWord_1100679 prefixEnd_1100679 251189943693424143133589 := by
  unfold tailWord_1100679
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145061179435438852377091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26763374119623625901584727 40145061179435438852377091)
  ·
    refine ⟨60217591769153158278565637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40145061179435438852377091 60217591769153158278565637)
    ·
      refine ⟨11290798456716217177231057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60217591769153158278565637 11290798456716217177231057)
      ·
        refine ⟨8468098842537162882923293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11290798456716217177231057 8468098842537162882923293)
        ·
          refine ⟨3175537065951436081096235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8468098842537162882923293 3175537065951436081096235)
          ·
            refine ⟨4763305598927154121644353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175537065951436081096235 4763305598927154121644353)
            ·
              refine ⟨3572479199195365591233265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4763305598927154121644353 3572479199195365591233265)
              ·
                refine ⟨2679359399396524193424949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572479199195365591233265 2679359399396524193424949)
                ·
                  refine ⟨251189943693424143133589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679359399396524193424949 251189943693424143133589)
                  ·
                    rfl

theorem cell21_1100679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_1100679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100679 prefixEnd_1100679 := by exact prefixLift 1100679
  have htrace : WordTrace (prefixWord ++ tailWord_1100679) baseStart_1100679 baseEnd_1100679 := by
    simpa [prefixWord, tailWord_1100679, baseEnd_1100679] using wordTrace_append hprefix tailTrace_1100679
  have hstable : (prefixWord ++ tailWord_1100679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100679).length < 2 ^ (prefixWord ++ tailWord_1100679).sum := by decide
  have hdescent : baseEnd_1100679 < baseStart_1100679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100682 : List Nat := [3, 1, 2, 4, 1, 3, 2, 5]
def baseStart_1100682 : Nat := 118140960795 + 1100682 * 2 ^ 59
def prefixEnd_1100682 : Nat := 4983230072969 + 3 ^ 40 * 1100682 * 2
def baseEnd_1100682 : Nat := 83730209444765601527861

theorem tailTrace_1100682 : CollatzResearch.WordTrace tailWord_1100682 prefixEnd_1100682 83730209444765601527861 := by
  unfold tailWord_1100682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036292649606142591184075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26763447065616380243157533 10036292649606142591184075)
  ·
    refine ⟨15054438974409213886776113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036292649606142591184075 15054438974409213886776113)
    ·
      refine ⟨11290829230806910415082085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15054438974409213886776113 11290829230806910415082085)
      ·
        refine ⟨2117030480776295702827891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11290829230806910415082085 2117030480776295702827891)
        ·
          refine ⟨3175545721164443554241837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117030480776295702827891 3175545721164443554241837)
          ·
            refine ⟨1190829645436666332840689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3175545721164443554241837 1190829645436666332840689)
            ·
              refine ⟨893122234077499749630517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190829645436666332840689 893122234077499749630517)
              ·
                refine ⟨83730209444765601527861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893122234077499749630517 83730209444765601527861)
                ·
                  rfl

theorem cell21_1100682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_1100682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100682 prefixEnd_1100682 := by exact prefixLift 1100682
  have htrace : WordTrace (prefixWord ++ tailWord_1100682) baseStart_1100682 baseEnd_1100682 := by
    simpa [prefixWord, tailWord_1100682, baseEnd_1100682] using wordTrace_append hprefix tailTrace_1100682
  have hstable : (prefixWord ++ tailWord_1100682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100682).length < 2 ^ (prefixWord ++ tailWord_1100682).sum := by decide
  have hdescent : baseEnd_1100682 < baseStart_1100682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100693 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_1100693 : Nat := 118140960795 + 1100693 * 2 ^ 59
def prefixEnd_1100693 : Nat := 4983230072969 + 3 ^ 40 * 1100693 * 2
def baseEnd_1100693 : Nat := 251193138684163229900227

theorem tailTrace_1100693 : CollatzResearch.WordTrace tailWord_1100693 prefixEnd_1100693 251193138684163229900227 := by
  unfold tailWord_1100693
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145571801384719243386733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26763714534256479495591155 40145571801384719243386733)
  ·
    refine ⟨15054589425519269716270025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40145571801384719243386733 15054589425519269716270025)
    ·
      refine ⟨11290942069139452287202519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15054589425519269716270025 11290942069139452287202519)
      ·
        refine ⟨16936413103709178430803779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11290942069139452287202519 16936413103709178430803779)
        ·
          refine ⟨25404619655563767646205669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16936413103709178430803779 25404619655563767646205669)
          ·
            refine ⟨4763366185418206433663563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25404619655563767646205669 4763366185418206433663563)
            ·
              refine ⟨7145049278127309650495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763366185418206433663563 7145049278127309650495345)
              ·
                refine ⟨5358786958595482237871509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145049278127309650495345 5358786958595482237871509)
                ·
                  refine ⟨251193138684163229900227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5358786958595482237871509 251193138684163229900227)
                  ·
                    rfl

theorem cell21_1100693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_1100693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100693 prefixEnd_1100693 := by exact prefixLift 1100693
  have htrace : WordTrace (prefixWord ++ tailWord_1100693) baseStart_1100693 baseEnd_1100693 := by
    simpa [prefixWord, tailWord_1100693, baseEnd_1100693] using wordTrace_append hprefix tailTrace_1100693
  have hstable : (prefixWord ++ tailWord_1100693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100693).length < 2 ^ (prefixWord ++ tailWord_1100693).sum := by decide
  have hdescent : baseEnd_1100693 < baseStart_1100693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100707 : List Nat := [1, 1, 1, 4, 1, 2, 11]
def baseStart_1100707 : Nat := 118140960795 + 1100707 * 2 ^ 59
def prefixEnd_1100707 : Nat := 4983230072969 + 3 ^ 40 * 1100707 * 2
def baseEnd_1100707 : Nat := 27910703741655812962985

theorem tailTrace_1100707 : CollatzResearch.WordTrace tailWord_1100707 prefixEnd_1100707 27910703741655812962985 := by
  unfold tailWord_1100707
  simp only [CollatzResearch.WordTrace]
  refine ⟨40146082423333999634396375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26764054948889333089597583 40146082423333999634396375)
  ·
    refine ⟨60219123635000999451594563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40146082423333999634396375 60219123635000999451594563)
    ·
      refine ⟨90328685452501499177391845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60219123635000999451594563 90328685452501499177391845)
      ·
        refine ⟨16936628522344031095760971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90328685452501499177391845 16936628522344031095760971)
        ·
          refine ⟨25404942783516046643641457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16936628522344031095760971 25404942783516046643641457)
          ·
            refine ⟨19053707087637034982731093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25404942783516046643641457 19053707087637034982731093)
            ·
              refine ⟨27910703741655812962985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19053707087637034982731093 27910703741655812962985)
              ·
                rfl

theorem cell21_1100707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_1100707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100707 prefixEnd_1100707 := by exact prefixLift 1100707
  have htrace : WordTrace (prefixWord ++ tailWord_1100707) baseStart_1100707 baseEnd_1100707 := by
    simpa [prefixWord, tailWord_1100707, baseEnd_1100707] using wordTrace_append hprefix tailTrace_1100707
  have hstable : (prefixWord ++ tailWord_1100707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100707).length < 2 ^ (prefixWord ++ tailWord_1100707).sum := by decide
  have hdescent : baseEnd_1100707 < baseStart_1100707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100789 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_1100789 : Nat := 118140960795 + 1100789 * 2 ^ 59
def prefixEnd_1100789 : Nat := 4983230072969 + 3 ^ 40 * 1100789 * 2
def baseEnd_1100789 : Nat := 251215047192088396300031

theorem tailTrace_1100789 : CollatzResearch.WordTrace tailWord_1100789 prefixEnd_1100789 251215047192088396300031 := by
  unfold tailWord_1100789
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149073209036927638881421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26766048806024618425920947 40149073209036927638881421)
  ·
    refine ⟨15055902453388847864580533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40149073209036927638881421 15055902453388847864580533)
    ·
      refine ⟨1411490855005204487304425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15055902453388847864580533 1411490855005204487304425)
      ·
        refine ⟨1058618141253903365478319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411490855005204487304425 1058618141253903365478319)
        ·
          refine ⟨1587927211880855048217479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058618141253903365478319 1587927211880855048217479)
          ·
            refine ⟨2381890817821282572326219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587927211880855048217479 2381890817821282572326219)
            ·
              refine ⟨3572836226731923858489329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381890817821282572326219 3572836226731923858489329)
              ·
                refine ⟨2679627170048942893866997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572836226731923858489329 2679627170048942893866997)
                ·
                  refine ⟨251215047192088396300031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679627170048942893866997 251215047192088396300031)
                  ·
                    rfl

theorem cell21_1100789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_1100789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100789 prefixEnd_1100789 := by exact prefixLift 1100789
  have htrace : WordTrace (prefixWord ++ tailWord_1100789) baseStart_1100789 baseEnd_1100789 := by
    simpa [prefixWord, tailWord_1100789, baseEnd_1100789] using wordTrace_append hprefix tailTrace_1100789
  have hstable : (prefixWord ++ tailWord_1100789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100789).length < 2 ^ (prefixWord ++ tailWord_1100789).sum := by decide
  have hdescent : baseEnd_1100789 < baseStart_1100789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100831 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_1100831 : Nat := 118140960795 + 1100831 * 2 ^ 59
def prefixEnd_1100831 : Nat := 4983230072969 + 3 ^ 40 * 1100831 * 2
def baseEnd_1100831 : Nat := 251224632164305656599945

theorem tailTrace_1100831 : CollatzResearch.WordTrace tailWord_1100831 prefixEnd_1100831 251224632164305656599945 := by
  unfold tailWord_1100831
  simp only [CollatzResearch.WordTrace]
  refine ⟨40150605074884768811910347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26767070049923179207940231 40150605074884768811910347)
  ·
    refine ⟨60225907612327153217865521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40150605074884768811910347 60225907612327153217865521)
    ·
      refine ⟨45169430709245364913399141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60225907612327153217865521 45169430709245364913399141)
      ·
        refine ⟨8469268257983505921262339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45169430709245364913399141 8469268257983505921262339)
        ·
          refine ⟨12703902386975258881893509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8469268257983505921262339 12703902386975258881893509)
          ·
            refine ⟨2381981697557861040355033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12703902386975258881893509 2381981697557861040355033)
            ·
              refine ⟨1786486273168395780266275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381981697557861040355033 1786486273168395780266275)
              ·
                refine ⟨2679729409752593670399413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786486273168395780266275 2679729409752593670399413)
                ·
                  refine ⟨251224632164305656599945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679729409752593670399413 251224632164305656599945)
                  ·
                    rfl

theorem cell21_1100831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_1100831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100831 prefixEnd_1100831 := by exact prefixLift 1100831
  have htrace : WordTrace (prefixWord ++ tailWord_1100831) baseStart_1100831 baseEnd_1100831 := by
    simpa [prefixWord, tailWord_1100831, baseEnd_1100831] using wordTrace_append hprefix tailTrace_1100831
  have hstable : (prefixWord ++ tailWord_1100831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100831).length < 2 ^ (prefixWord ++ tailWord_1100831).sum := by decide
  have hdescent : baseEnd_1100831 < baseStart_1100831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100862 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1100862 : Nat := 118140960795 + 1100862 * 2 ^ 59
def prefixEnd_1100862 : Nat := 4983230072969 + 3 ^ 40 * 1100862 * 2
def baseEnd_1100862 : Nat := 251231706786656491583215

theorem tailTrace_1100862 : CollatzResearch.WordTrace tailWord_1100862 prefixEnd_1100862 251231706786656491583215 := by
  unfold tailWord_1100862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018966967221557638286105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26767823825181640737525893 5018966967221557638286105)
  ·
    refine ⟨3764225225416168228714579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5018966967221557638286105 3764225225416168228714579)
    ·
      refine ⟨5646337838124252343071869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764225225416168228714579 5646337838124252343071869)
      ·
        refine ⟨2117376689296594628651951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5646337838124252343071869 2117376689296594628651951)
        ·
          refine ⟨3176065033944891942977927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117376689296594628651951 3176065033944891942977927)
          ·
            refine ⟨4764097550917337914466891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176065033944891942977927 4764097550917337914466891)
            ·
              refine ⟨7146146326376006871700337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764097550917337914466891 7146146326376006871700337)
              ·
                refine ⟨5359609744782005153775253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146146326376006871700337 5359609744782005153775253)
                ·
                  refine ⟨251231706786656491583215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5359609744782005153775253 251231706786656491583215)
                  ·
                    rfl

theorem cell21_1100862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1100862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100862 prefixEnd_1100862 := by exact prefixLift 1100862
  have htrace : WordTrace (prefixWord ++ tailWord_1100862) baseStart_1100862 baseEnd_1100862 := by
    simpa [prefixWord, tailWord_1100862, baseEnd_1100862] using wordTrace_append hprefix tailTrace_1100862
  have hstable : (prefixWord ++ tailWord_1100862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100862).length < 2 ^ (prefixWord ++ tailWord_1100862).sum := by decide
  have hdescent : baseEnd_1100862 < baseStart_1100862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100890 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1100890 : Nat := 118140960795 + 1100890 * 2 ^ 59
def prefixEnd_1100890 : Nat := 4983230072969 + 3 ^ 40 * 1100890 * 2
def baseEnd_1100890 : Nat := 251238096768134665116491

theorem tailTrace_1100890 : CollatzResearch.WordTrace tailWord_1100890 prefixEnd_1100890 251238096768134665116491 := by
  unfold tailWord_1100890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038189245417755472077031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26768504654447347925538749 10038189245417755472077031)
  ·
    refine ⟨15057283868126633208115547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10038189245417755472077031 15057283868126633208115547)
    ·
      refine ⟨22585925802189949812173321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057283868126633208115547 22585925802189949812173321)
      ·
        refine ⟨16939444351642462359129991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22585925802189949812173321 16939444351642462359129991)
        ·
          refine ⟨25409166527463693538694987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16939444351642462359129991 25409166527463693538694987)
          ·
            refine ⟨38113749791195540308042481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25409166527463693538694987 38113749791195540308042481)
            ·
              refine ⟨28585312343396655231031861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38113749791195540308042481 28585312343396655231031861)
              ·
                refine ⟨2679873032193436427909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28585312343396655231031861 2679873032193436427909237)
                ·
                  refine ⟨251238096768134665116491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679873032193436427909237 251238096768134665116491)
                  ·
                    rfl

theorem cell21_1100890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1100890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100890 prefixEnd_1100890 := by exact prefixLift 1100890
  have htrace : WordTrace (prefixWord ++ tailWord_1100890) baseStart_1100890 baseEnd_1100890 := by
    simpa [prefixWord, tailWord_1100890, baseEnd_1100890] using wordTrace_append hprefix tailTrace_1100890
  have hstable : (prefixWord ++ tailWord_1100890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100890).length < 2 ^ (prefixWord ++ tailWord_1100890).sum := by decide
  have hdescent : baseEnd_1100890 < baseStart_1100890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100938 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1100938 : Nat := 118140960795 + 1100938 * 2 ^ 59
def prefixEnd_1100938 : Nat := 4983230072969 + 3 ^ 40 * 1100938 * 2
def baseEnd_1100938 : Nat := 251249051022097248316393

theorem tailTrace_1100938 : CollatzResearch.WordTrace tailWord_1100938 prefixEnd_1100938 251249051022097248316393 := by
  unfold tailWord_1100938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038626921374281521513867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26769671790331417390703645 10038626921374281521513867)
  ·
    refine ⟨15057940382061422282270801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10038626921374281521513867 15057940382061422282270801)
    ·
      refine ⟨11293455286546066711703101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15057940382061422282270801 11293455286546066711703101)
      ·
        refine ⟨4235045732454775016888663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11293455286546066711703101 4235045732454775016888663)
        ·
          refine ⟨6352568598682162525332995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235045732454775016888663 6352568598682162525332995)
          ·
            refine ⟨9528852898023243787999493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352568598682162525332995 9528852898023243787999493)
            ·
              refine ⟨1786659918379358210249905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9528852898023243787999493 1786659918379358210249905)
              ·
                refine ⟨1339994938784518657687429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786659918379358210249905 1339994938784518657687429)
                ·
                  refine ⟨251249051022097248316393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339994938784518657687429 251249051022097248316393)
                  ·
                    rfl

theorem cell21_1100938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1100938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100938 prefixEnd_1100938 := by exact prefixLift 1100938
  have htrace : WordTrace (prefixWord ++ tailWord_1100938) baseStart_1100938 baseEnd_1100938 := by
    simpa [prefixWord, tailWord_1100938, baseEnd_1100938] using wordTrace_append hprefix tailTrace_1100938
  have hstable : (prefixWord ++ tailWord_1100938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100938).length < 2 ^ (prefixWord ++ tailWord_1100938).sum := by decide
  have hdescent : baseEnd_1100938 < baseStart_1100938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100952 : List Nat := [2, 1, 2, 4, 2, 1, 3, 6]
def baseStart_1100952 : Nat := 118140960795 + 1100952 * 2 ^ 59
def prefixEnd_1100952 : Nat := 4983230072969 + 3 ^ 40 * 1100952 * 2
def baseEnd_1100952 : Nat := 83750748670945445027677

theorem tailTrace_1100952 : CollatzResearch.WordTrace tailWord_1100952 prefixEnd_1100952 83750748670945445027677 := by
  unfold tailWord_1100952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077509153723203238532555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26770012204964270984710073 20077509153723203238532555)
  ·
    refine ⟨30116263730584804857798833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20077509153723203238532555 30116263730584804857798833)
    ·
      refine ⟨22587197797938603643349125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30116263730584804857798833 22587197797938603643349125)
      ·
        refine ⟨4235099587113488183127961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22587197797938603643349125 4235099587113488183127961)
        ·
          refine ⟨3176324690335116137345971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4235099587113488183127961 3176324690335116137345971)
          ·
            refine ⟨4764487035502674206018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176324690335116137345971 4764487035502674206018957)
            ·
              refine ⟨1786682638313502827257109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4764487035502674206018957 1786682638313502827257109)
              ·
                refine ⟨83750748670945445027677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786682638313502827257109 83750748670945445027677)
                ·
                  rfl

theorem cell21_1100952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_1100952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1100952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1100952 prefixEnd_1100952 := by exact prefixLift 1100952
  have htrace : WordTrace (prefixWord ++ tailWord_1100952) baseStart_1100952 baseEnd_1100952 := by
    simpa [prefixWord, tailWord_1100952, baseEnd_1100952] using wordTrace_append hprefix tailTrace_1100952
  have hstable : (prefixWord ++ tailWord_1100952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100952).length < 2 ^ (prefixWord ++ tailWord_1100952).sum := by decide
  have hdescent : baseEnd_1100952 < baseStart_1100952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101028 : List Nat := [2, 3, 1, 1, 1, 2, 6, 5]
def baseStart_1101028 : Nat := 118140960795 + 1101028 * 2 ^ 59
def prefixEnd_1101028 : Nat := 4983230072969 + 3 ^ 40 * 1101028 * 2
def baseEnd_1101028 : Nat := 83756530082759030605403

theorem tailTrace_1101028 : CollatzResearch.WordTrace tailWord_1101028 prefixEnd_1101028 83756530082759030605403 := by
  unfold tailWord_1101028
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078895127585535728415869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26771860170114047637887825 20078895127585535728415869)
  ·
    refine ⟨7529585672844575898155951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20078895127585535728415869 7529585672844575898155951)
    ·
      refine ⟨11294378509266863847233927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529585672844575898155951 11294378509266863847233927)
      ·
        refine ⟨16941567763900295770850891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294378509266863847233927 16941567763900295770850891)
        ·
          refine ⟨25412351645850443656276337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16941567763900295770850891 25412351645850443656276337)
          ·
            refine ⟨19059263734387832742207253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25412351645850443656276337 19059263734387832742207253)
            ·
              refine ⟨893402987549429659790965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19059263734387832742207253 893402987549429659790965)
              ·
                refine ⟨83756530082759030605403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893402987549429659790965 83756530082759030605403)
                ·
                  rfl

theorem cell21_1101028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_1101028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101028 prefixEnd_1101028 := by exact prefixLift 1101028
  have htrace : WordTrace (prefixWord ++ tailWord_1101028) baseStart_1101028 baseEnd_1101028 := by
    simpa [prefixWord, tailWord_1101028, baseEnd_1101028] using wordTrace_append hprefix tailTrace_1101028
  have hstable : (prefixWord ++ tailWord_1101028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101028).length < 2 ^ (prefixWord ++ tailWord_1101028).sum := by decide
  have hdescent : baseEnd_1101028 < baseStart_1101028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101059 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_1101059 : Nat := 118140960795 + 1101059 * 2 ^ 59
def prefixEnd_1101059 : Nat := 4983230072969 + 3 ^ 40 * 1101059 * 2
def baseEnd_1101059 : Nat := 251276664870627926799479

theorem tailTrace_1101059 : CollatzResearch.WordTrace tailWord_1101059 prefixEnd_1101059 251276664870627926799479 := by
  unfold tailWord_1101059
  simp only [CollatzResearch.WordTrace]
  refine ⟨40158920918058763751210231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26772613945372509167473487 40158920918058763751210231)
  ·
    refine ⟨60238381377088145626815347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40158920918058763751210231 60238381377088145626815347)
    ·
      refine ⟨90357572065632218440223021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60238381377088145626815347 90357572065632218440223021)
      ·
        refine ⟨33884089524612081915083633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90357572065632218440223021 33884089524612081915083633)
        ·
          refine ⟨25413067143459061436312725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33884089524612081915083633 25413067143459061436312725)
          ·
            refine ⟨1191237522349643504827159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25413067143459061436312725 1191237522349643504827159)
            ·
              refine ⟨1786856283524465257240739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191237522349643504827159 1786856283524465257240739)
              ·
                refine ⟨2680284425286697885861109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786856283524465257240739 2680284425286697885861109)
                ·
                  refine ⟨251276664870627926799479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2680284425286697885861109 251276664870627926799479)
                  ·
                    rfl

theorem cell21_1101059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_1101059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101059 prefixEnd_1101059 := by exact prefixLift 1101059
  have htrace : WordTrace (prefixWord ++ tailWord_1101059) baseStart_1101059 baseEnd_1101059 := by
    simpa [prefixWord, tailWord_1101059, baseEnd_1101059] using wordTrace_append hprefix tailTrace_1101059
  have hstable : (prefixWord ++ tailWord_1101059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101059).length < 2 ^ (prefixWord ++ tailWord_1101059).sum := by decide
  have hdescent : baseEnd_1101059 < baseStart_1101059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101073 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_1101073 : Nat := 118140960795 + 1101073 * 2 ^ 59
def prefixEnd_1101073 : Nat := 4983230072969 + 3 ^ 40 * 1101073 * 2
def baseEnd_1101073 : Nat := 251279859861367013566117

theorem tailTrace_1101073 : CollatzResearch.WordTrace tailWord_1101073 prefixEnd_1101073 251279859861367013566117 := by
  unfold tailWord_1101073
  simp only [CollatzResearch.WordTrace]
  refine ⟨40159431540008044142219873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26772954360005362761479915 40159431540008044142219873)
  ·
    refine ⟨30119573655006033106664905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40159431540008044142219873 30119573655006033106664905)
    ·
      refine ⟨22589680241254524829998679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30119573655006033106664905 22589680241254524829998679)
      ·
        refine ⟨33884520361881787244998019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22589680241254524829998679 33884520361881787244998019)
        ·
          refine ⟨50826780542822680867497029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33884520361881787244998019 50826780542822680867497029)
          ·
            refine ⟨9530021351779252662655693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50826780542822680867497029 9530021351779252662655693)
            ·
              refine ⟨3573758006917219748495885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9530021351779252662655693 3573758006917219748495885)
              ·
                refine ⟨1340159252593957405685957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3573758006917219748495885 1340159252593957405685957)
                ·
                  refine ⟨251279859861367013566117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340159252593957405685957 251279859861367013566117)
                  ·
                    rfl

theorem cell21_1101073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_1101073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101073 prefixEnd_1101073 := by exact prefixLift 1101073
  have htrace : WordTrace (prefixWord ++ tailWord_1101073) baseStart_1101073 baseEnd_1101073 := by
    simpa [prefixWord, tailWord_1101073, baseEnd_1101073] using wordTrace_append hprefix tailTrace_1101073
  have hstable : (prefixWord ++ tailWord_1101073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101073).length < 2 ^ (prefixWord ++ tailWord_1101073).sum := by decide
  have hdescent : baseEnd_1101073 < baseStart_1101073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101110 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1101110 : Nat := 118140960795 + 1101110 * 2 ^ 59
def prefixEnd_1101110 : Nat := 4983230072969 + 3 ^ 40 * 1101110 * 2
def baseEnd_1101110 : Nat := 251288303765463171449375

theorem tailTrace_1101110 : CollatzResearch.WordTrace tailWord_1101110 prefixEnd_1101110 251288303765463171449375 := by
  unfold tailWord_1101110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510048815054624966332299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26773854027249332974211189 2510048815054624966332299)
  ·
    refine ⟨3765073222581937449498449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510048815054624966332299 3765073222581937449498449)
    ·
      refine ⟨2823804916936453087123837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3765073222581937449498449 2823804916936453087123837)
      ·
        refine ⟨1058926843851169907671439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2823804916936453087123837 1058926843851169907671439)
        ·
          refine ⟨1588390265776754861507159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058926843851169907671439 1588390265776754861507159)
          ·
            refine ⟨2382585398665132292260739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588390265776754861507159 2382585398665132292260739)
            ·
              refine ⟨3573878097997698438391109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382585398665132292260739 3573878097997698438391109)
              ·
                refine ⟨670102143374568457198333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3573878097997698438391109 670102143374568457198333)
                ·
                  refine ⟨251288303765463171449375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670102143374568457198333 251288303765463171449375)
                  ·
                    rfl

theorem cell21_1101110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1101110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101110 prefixEnd_1101110 := by exact prefixLift 1101110
  have htrace : WordTrace (prefixWord ++ tailWord_1101110) baseStart_1101110 baseEnd_1101110 := by
    simpa [prefixWord, tailWord_1101110, baseEnd_1101110] using wordTrace_append hprefix tailTrace_1101110
  have hstable : (prefixWord ++ tailWord_1101110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101110).length < 2 ^ (prefixWord ++ tailWord_1101110).sum := by decide
  have hdescent : baseEnd_1101110 < baseStart_1101110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101121 : List Nat := [1, 2, 5, 2, 1, 3, 1, 6]
def baseStart_1101121 : Nat := 118140960795 + 1101121 * 2 ^ 59
def prefixEnd_1101121 : Nat := 4983230072969 + 3 ^ 40 * 1101121 * 2
def baseEnd_1101121 : Nat := 83763604705109865588673

theorem tailTrace_1101121 : CollatzResearch.WordTrace tailWord_1101121 prefixEnd_1101121 83763604705109865588673 := by
  unfold tailWord_1101121
  simp only [CollatzResearch.WordTrace]
  refine ⟨40161182243834148339967217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26774121495889432226644811 40161182243834148339967217)
  ·
    refine ⟨30120886682875611254975413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40161182243834148339967217 30120886682875611254975413)
    ·
      refine ⟨2823833126519588555153945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30120886682875611254975413 2823833126519588555153945)
      ·
        refine ⟨2117874844889691416365459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823833126519588555153945 2117874844889691416365459)
        ·
          refine ⟨3176812267334537124548189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117874844889691416365459 3176812267334537124548189)
          ·
            refine ⟨1191304600250451421705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3176812267334537124548189 1191304600250451421705571)
            ·
              refine ⟨1786956900375677132558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191304600250451421705571 1786956900375677132558357)
              ·
                refine ⟨83763604705109865588673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786956900375677132558357 83763604705109865588673)
                ·
                  rfl

theorem cell21_1101121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_1101121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101121 prefixEnd_1101121 := by exact prefixLift 1101121
  have htrace : WordTrace (prefixWord ++ tailWord_1101121) baseStart_1101121 baseEnd_1101121 := by
    simpa [prefixWord, tailWord_1101121, baseEnd_1101121] using wordTrace_append hprefix tailTrace_1101121
  have hstable : (prefixWord ++ tailWord_1101121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101121).length < 2 ^ (prefixWord ++ tailWord_1101121).sum := by decide
  have hdescent : baseEnd_1101121 < baseStart_1101121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101152 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_1101152 : Nat := 118140960795 + 1101152 * 2 ^ 59
def prefixEnd_1101152 : Nat := 4983230072969 + 3 ^ 40 * 1101152 * 2
def baseEnd_1101152 : Nat := 251297888737680431749289

theorem tailTrace_1101152 : CollatzResearch.WordTrace tailWord_1101152 prefixEnd_1101152 251297888737680431749289 := by
  unfold tailWord_1101152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081156453360920317172855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26774875271147893756230473 20081156453360920317172855)
  ·
    refine ⟨30121734680041380475759283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20081156453360920317172855 30121734680041380475759283)
    ·
      refine ⟨45182602020062070713638925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30121734680041380475759283 45182602020062070713638925)
      ·
        refine ⟨16943475757523276517614597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45182602020062070713638925 16943475757523276517614597)
        ·
          refine ⟨3176901704535614347052737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16943475757523276517614597 3176901704535614347052737)
          ·
            refine ⟨2382676278401710760289553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176901704535614347052737 2382676278401710760289553)
            ·
              refine ⟨1787007208801283070217165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382676278401710760289553 1787007208801283070217165)
              ·
                refine ⟨670127703300481151331437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787007208801283070217165 670127703300481151331437)
                ·
                  refine ⟨251297888737680431749289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670127703300481151331437 251297888737680431749289)
                  ·
                    rfl

theorem cell21_1101152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_1101152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101152 prefixEnd_1101152 := by exact prefixLift 1101152
  have htrace : WordTrace (prefixWord ++ tailWord_1101152) baseStart_1101152 baseEnd_1101152 := by
    simpa [prefixWord, tailWord_1101152, baseEnd_1101152] using wordTrace_append hprefix tailTrace_1101152
  have hstable : (prefixWord ++ tailWord_1101152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101152).length < 2 ^ (prefixWord ++ tailWord_1101152).sum := by decide
  have hdescent : baseEnd_1101152 < baseStart_1101152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101214 : List Nat := [4, 3, 1, 2, 3, 1, 7]
def baseStart_1101214 : Nat := 118140960795 + 1101214 * 2 ^ 59
def prefixEnd_1101214 : Nat := 4983230072969 + 3 ^ 40 * 1101214 * 2
def baseEnd_1101214 : Nat := 27923559775820233523981

theorem tailTrace_1101214 : CollatzResearch.WordTrace tailWord_1101214 prefixEnd_1101214 27923559775820233523981 := by
  unfold tailWord_1101214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020571779062153152887837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26776382821664816815401797 5020571779062153152887837)
  ·
    refine ⟨1882714417148307432332939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5020571779062153152887837 1882714417148307432332939)
    ·
      refine ⟨2824071625722461148499409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882714417148307432332939 2824071625722461148499409)
      ·
        refine ⟨2118053719291845861374557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824071625722461148499409 2118053719291845861374557)
        ·
          refine ⟨794270144734442198015459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118053719291845861374557 794270144734442198015459)
          ·
            refine ⟨1191405217101663297023189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794270144734442198015459 1191405217101663297023189)
            ·
              refine ⟨27923559775820233523981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1191405217101663297023189 27923559775820233523981)
              ·
                rfl

theorem cell21_1101214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 7].length) (baseStart_1101214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101214 prefixEnd_1101214 := by exact prefixLift 1101214
  have htrace : WordTrace (prefixWord ++ tailWord_1101214) baseStart_1101214 baseEnd_1101214 := by
    simpa [prefixWord, tailWord_1101214, baseEnd_1101214] using wordTrace_append hprefix tailTrace_1101214
  have hstable : (prefixWord ++ tailWord_1101214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101214).length < 2 ^ (prefixWord ++ tailWord_1101214).sum := by decide
  have hdescent : baseEnd_1101214 < baseStart_1101214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101239 : List Nat := [1, 1, 3, 1, 3, 2, 4, 6]
def baseStart_1101239 : Nat := 118140960795 + 1101239 * 2 ^ 59
def prefixEnd_1101239 : Nat := 4983230072969 + 3 ^ 40 * 1101239 * 2
def baseEnd_1101239 : Nat := 83772581107662537933037

theorem tailTrace_1101239 : CollatzResearch.WordTrace tailWord_1101239 prefixEnd_1101239 83772581107662537933037 := by
  unfold tailWord_1101239
  simp only [CollatzResearch.WordTrace]
  refine ⟨40165486057406654492762771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26776990704937769661841847 40165486057406654492762771)
  ·
    refine ⟨60248229086109981739144157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40165486057406654492762771 60248229086109981739144157)
    ·
      refine ⟨22593085907291243152179059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60248229086109981739144157 22593085907291243152179059)
      ·
        refine ⟨33889628860936864728268589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22593085907291243152179059 33889628860936864728268589)
        ·
          refine ⟨12708610822851324273100721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33889628860936864728268589 12708610822851324273100721)
          ·
            refine ⟨9531458117138493204825541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12708610822851324273100721 9531458117138493204825541)
            ·
              refine ⟨1787148396963467475904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9531458117138493204825541 1787148396963467475904789)
              ·
                refine ⟨83772581107662537933037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787148396963467475904789 83772581107662537933037)
                ·
                  rfl

theorem cell21_1101239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_1101239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101239 prefixEnd_1101239 := by exact prefixLift 1101239
  have htrace : WordTrace (prefixWord ++ tailWord_1101239) baseStart_1101239 baseEnd_1101239 := by
    simpa [prefixWord, tailWord_1101239, baseEnd_1101239] using wordTrace_append hprefix tailTrace_1101239
  have hstable : (prefixWord ++ tailWord_1101239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101239).length < 2 ^ (prefixWord ++ tailWord_1101239).sum := by decide
  have hdescent : baseEnd_1101239 < baseStart_1101239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101284 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1101284 : Nat := 118140960795 + 1101284 * 2 ^ 59
def prefixEnd_1101284 : Nat := 4983230072969 + 3 ^ 40 * 1101284 * 2
def baseEnd_1101284 : Nat := 251328012936077535549019

theorem tailTrace_1101284 : CollatzResearch.WordTrace tailWord_1101284 prefixEnd_1101284 251328012936077535549019 := by
  unfold tailWord_1101284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083563671121813589075453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26778084894829084785433937 20083563671121813589075453)
  ·
    refine ⟨7531336376670680095903295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20083563671121813589075453 7531336376670680095903295)
    ·
      refine ⟨11297004565006020143854943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7531336376670680095903295 11297004565006020143854943)
      ·
        refine ⟨16945506847509030215782415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11297004565006020143854943 16945506847509030215782415)
        ·
          refine ⟨25418260271263545323673623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16945506847509030215782415 25418260271263545323673623)
          ·
            refine ⟨38127390406895317985510435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25418260271263545323673623 38127390406895317985510435)
            ·
              refine ⟨57191085610342976978265653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38127390406895317985510435 57191085610342976978265653)
              ·
                refine ⟨5361664275969654091712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57191085610342976978265653 5361664275969654091712405)
                ·
                  refine ⟨251328012936077535549019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5361664275969654091712405 251328012936077535549019)
                  ·
                    rfl

theorem cell21_1101284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1101284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101284 prefixEnd_1101284 := by exact prefixLift 1101284
  have htrace : WordTrace (prefixWord ++ tailWord_1101284) baseStart_1101284 baseEnd_1101284 := by
    simpa [prefixWord, tailWord_1101284, baseEnd_1101284] using wordTrace_append hprefix tailTrace_1101284
  have hstable : (prefixWord ++ tailWord_1101284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101284).length < 2 ^ (prefixWord ++ tailWord_1101284).sum := by decide
  have hdescent : baseEnd_1101284 < baseStart_1101284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101329 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_1101329 : Nat := 118140960795 + 1101329 * 2 ^ 59
def prefixEnd_1101329 : Nat := 4983230072969 + 3 ^ 40 * 1101329 * 2
def baseEnd_1101329 : Nat := 251338282549167457298927

theorem tailTrace_1101329 : CollatzResearch.WordTrace tailWord_1101329 prefixEnd_1101329 251338282549167457298927 := by
  unfold tailWord_1101329
  simp only [CollatzResearch.WordTrace]
  refine ⟨40168768627080599863539041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26779179084720399909026027 40168768627080599863539041)
  ·
    refine ⟨30126576470310449897654281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40168768627080599863539041 30126576470310449897654281)
    ·
      refine ⟨22594932352732837423240711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30126576470310449897654281 22594932352732837423240711)
      ·
        refine ⟨33892398529099256134861067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594932352732837423240711 33892398529099256134861067)
        ·
          refine ⟨50838597793648884202291601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33892398529099256134861067 50838597793648884202291601)
          ·
            refine ⟨38128948345236663151718701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50838597793648884202291601 38128948345236663151718701)
            ·
              refine ⟨14298355629463748681894513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38128948345236663151718701 14298355629463748681894513)
              ·
                refine ⟨10723766722097811511420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14298355629463748681894513 10723766722097811511420885)
                ·
                  refine ⟨251338282549167457298927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10723766722097811511420885 251338282549167457298927)
                  ·
                    rfl

theorem cell21_1101329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_1101329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101329 prefixEnd_1101329 := by exact prefixLift 1101329
  have htrace : WordTrace (prefixWord ++ tailWord_1101329) baseStart_1101329 baseEnd_1101329 := by
    simpa [prefixWord, tailWord_1101329, baseEnd_1101329] using wordTrace_append hprefix tailTrace_1101329
  have hstable : (prefixWord ++ tailWord_1101329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101329).length < 2 ^ (prefixWord ++ tailWord_1101329).sum := by decide
  have hdescent : baseEnd_1101329 < baseStart_1101329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101346 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1101346 : Nat := 118140960795 + 1101346 * 2 ^ 59
def prefixEnd_1101346 : Nat := 4983230072969 + 3 ^ 40 * 1101346 * 2
def baseEnd_1101346 : Nat := 251342162180779205515559

theorem tailTrace_1101346 : CollatzResearch.WordTrace tailWord_1101346 prefixEnd_1101346 251342162180779205515559 := by
  unfold tailWord_1101346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042347167004752941726973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26779592445346007844605261 10042347167004752941726973)
  ·
    refine ⟨3765880187626782353147615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10042347167004752941726973 3765880187626782353147615)
    ·
      refine ⟨5648820281440173529721423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765880187626782353147615 5648820281440173529721423)
      ·
        refine ⟨8473230422160260294582135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648820281440173529721423 8473230422160260294582135)
        ·
          refine ⟨12709845633240390441873203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8473230422160260294582135 12709845633240390441873203)
          ·
            refine ⟨19064768449860585662809805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12709845633240390441873203 19064768449860585662809805)
            ·
              refine ⟨7149288168697719623553677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19064768449860585662809805 7149288168697719623553677)
              ·
                refine ⟨2680983063261644858832629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7149288168697719623553677 2680983063261644858832629)
                ·
                  refine ⟨251342162180779205515559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2680983063261644858832629 251342162180779205515559)
                  ·
                    rfl

theorem cell21_1101346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1101346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101346 prefixEnd_1101346 := by exact prefixLift 1101346
  have htrace : WordTrace (prefixWord ++ tailWord_1101346) baseStart_1101346 baseEnd_1101346 := by
    simpa [prefixWord, tailWord_1101346, baseEnd_1101346] using wordTrace_append hprefix tailTrace_1101346
  have hstable : (prefixWord ++ tailWord_1101346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101346).length < 2 ^ (prefixWord ++ tailWord_1101346).sum := by decide
  have hdescent : baseEnd_1101346 < baseStart_1101346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101366 : List Nat := [5, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1101366 : Nat := 118140960795 + 1101366 * 2 ^ 59
def prefixEnd_1101366 : Nat := 4983230072969 + 3 ^ 40 * 1101366 * 2
def baseEnd_1101366 : Nat := 83782242151087871727395

theorem tailTrace_1101366 : CollatzResearch.WordTrace tailWord_1101366 prefixEnd_1101366 83782242151087871727395 := by
  unfold tailWord_1101366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510632382996659698914747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26780078751964370121757301 2510632382996659698914747)
  ·
    refine ⟨3765948574494989548372121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510632382996659698914747 3765948574494989548372121)
    ·
      refine ⟨2824461430871242161279091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3765948574494989548372121 2824461430871242161279091)
      ·
        refine ⟨4236692146306863241918637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824461430871242161279091 4236692146306863241918637)
        ·
          refine ⟨1588759554865073715719489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4236692146306863241918637 1588759554865073715719489)
          ·
            refine ⟨1191569666148805286789617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1588759554865073715719489 1191569666148805286789617)
            ·
              refine ⟨893677249611603965092213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191569666148805286789617 893677249611603965092213)
              ·
                refine ⟨83782242151087871727395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893677249611603965092213 83782242151087871727395)
                ·
                  rfl

theorem cell21_1101366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1101366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101366 prefixEnd_1101366 := by exact prefixLift 1101366
  have htrace : WordTrace (prefixWord ++ tailWord_1101366) baseStart_1101366 baseEnd_1101366 := by
    simpa [prefixWord, tailWord_1101366, baseEnd_1101366] using wordTrace_append hprefix tailTrace_1101366
  have hstable : (prefixWord ++ tailWord_1101366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101366).length < 2 ^ (prefixWord ++ tailWord_1101366).sum := by decide
  have hdescent : baseEnd_1101366 < baseStart_1101366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101470 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1101470 : Nat := 118140960795 + 1101470 * 2 ^ 59
def prefixEnd_1101470 : Nat := 4983230072969 + 3 ^ 40 * 1101470 * 2
def baseEnd_1101470 : Nat := 251370460670182545448639

theorem tailTrace_1101470 : CollatzResearch.WordTrace tailWord_1101470 prefixEnd_1101470 251370460670182545448639 := by
  unfold tailWord_1101470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021738914946222618052733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26782607546379853962947909 5021738914946222618052733)
  ·
    refine ⟨1883152093104833481769775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5021738914946222618052733 1883152093104833481769775)
    ·
      refine ⟨2824728139657250222654663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883152093104833481769775 2824728139657250222654663)
      ·
        refine ⟨4237092209485875333981995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824728139657250222654663 4237092209485875333981995)
        ·
          refine ⟨6355638314228813000972993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237092209485875333981995 6355638314228813000972993)
          ·
            refine ⟨4766728735671609750729745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6355638314228813000972993 4766728735671609750729745)
            ·
              refine ⟨3575046551753707313047309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4766728735671609750729745 3575046551753707313047309)
              ·
                refine ⟨1340642456907640242392741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3575046551753707313047309 1340642456907640242392741)
                ·
                  refine ⟨251370460670182545448639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340642456907640242392741 251370460670182545448639)
                  ·
                    rfl

theorem cell21_1101470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1101470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101470 prefixEnd_1101470 := by exact prefixLift 1101470
  have htrace : WordTrace (prefixWord ++ tailWord_1101470) baseStart_1101470 baseEnd_1101470 := by
    simpa [prefixWord, tailWord_1101470, baseEnd_1101470] using wordTrace_append hprefix tailTrace_1101470
  have hstable : (prefixWord ++ tailWord_1101470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101470).length < 2 ^ (prefixWord ++ tailWord_1101470).sum := by decide
  have hdescent : baseEnd_1101470 < baseStart_1101470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101512 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_1101512 : Nat := 118140960795 + 1101512 * 2 ^ 59
def prefixEnd_1101512 : Nat := 4983230072969 + 3 ^ 40 * 1101512 * 2
def baseEnd_1101512 : Nat := 251380045642399805748553

theorem tailTrace_1101512 : CollatzResearch.WordTrace tailWord_1101512 prefixEnd_1101512 251380045642399805748553 := by
  unfold tailWord_1101512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20087721592708811058725395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26783628790278414744967193 20087721592708811058725395)
  ·
    refine ⟨30131582389063216588088093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20087721592708811058725395 30131582389063216588088093)
    ·
      refine ⟨11299343395898706220533035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30131582389063216588088093 11299343395898706220533035)
      ·
        refine ⟨16949015093848059330799553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11299343395898706220533035 16949015093848059330799553)
        ·
          refine ⟨12711761320386044498099665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16949015093848059330799553 12711761320386044498099665)
          ·
            refine ⟨9533820990289533373574749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12711761320386044498099665 9533820990289533373574749)
            ·
              refine ⟨3575182871358575015090531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9533820990289533373574749 3575182871358575015090531)
              ·
                refine ⟨5362774307037862522635797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575182871358575015090531 5362774307037862522635797)
                ·
                  refine ⟨251380045642399805748553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5362774307037862522635797 251380045642399805748553)
                  ·
                    rfl

theorem cell21_1101512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_1101512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101512 prefixEnd_1101512 := by exact prefixLift 1101512
  have htrace : WordTrace (prefixWord ++ tailWord_1101512) baseStart_1101512 baseEnd_1101512 := by
    simpa [prefixWord, tailWord_1101512, baseEnd_1101512] using wordTrace_append hprefix tailTrace_1101512
  have hstable : (prefixWord ++ tailWord_1101512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101512).length < 2 ^ (prefixWord ++ tailWord_1101512).sum := by decide
  have hdescent : baseEnd_1101512 < baseStart_1101512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101619 : List Nat := [1, 1, 1, 2, 8, 8]
def baseStart_1101619 : Nat := 118140960795 + 1101619 * 2 ^ 59
def prefixEnd_1101619 : Nat := 4983230072969 + 3 ^ 40 * 1101619 * 2
def baseEnd_1101619 : Nat := 9311276462970051757963

theorem tailTrace_1101619 : CollatzResearch.WordTrace tailWord_1101619 prefixEnd_1101619 9311276462970051757963 := by
  unfold tailWord_1101619
  simp only [CollatzResearch.WordTrace]
  refine ⟨40179345796029979391595911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26786230530686652927730607 40179345796029979391595911)
  ·
    refine ⟨60269018694044969087393867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40179345796029979391595911 60269018694044969087393867)
    ·
      refine ⟨90403528041067453631090801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60269018694044969087393867 90403528041067453631090801)
      ·
        refine ⟨67802646030800590223318101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90403528041067453631090801 67802646030800590223318101)
        ·
          refine ⟨794562258173444416679509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 67802646030800590223318101 794562258173444416679509)
          ·
            refine ⟨9311276462970051757963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 794562258173444416679509 9311276462970051757963)
            ·
              rfl

theorem cell21_1101619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 8].length) (baseStart_1101619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101619 prefixEnd_1101619 := by exact prefixLift 1101619
  have htrace : WordTrace (prefixWord ++ tailWord_1101619) baseStart_1101619 baseEnd_1101619 := by
    simpa [prefixWord, tailWord_1101619, baseEnd_1101619] using wordTrace_append hprefix tailTrace_1101619
  have hstable : (prefixWord ++ tailWord_1101619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101619).length < 2 ^ (prefixWord ++ tailWord_1101619).sum := by decide
  have hdescent : baseEnd_1101619 < baseStart_1101619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101622 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1101622 : Nat := 118140960795 + 1101622 * 2 ^ 59
def prefixEnd_1101622 : Nat := 4983230072969 + 3 ^ 40 * 1101622 * 2
def baseEnd_1101622 : Nat := 251405149141064058914995

theorem tailTrace_1101622 : CollatzResearch.WordTrace tailWord_1101622 prefixEnd_1101622 251405149141064058914995 := by
  unfold tailWord_1101622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511215950938694431497195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26786303476679407269303413 2511215950938694431497195)
  ·
    refine ⟨3766823926408041647245793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511215950938694431497195 3766823926408041647245793)
    ·
      refine ⟨2825117944806031235434345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3766823926408041647245793 2825117944806031235434345)
      ·
        refine ⟨2118838458604523426575759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825117944806031235434345 2118838458604523426575759)
        ·
          refine ⟨3178257687906785139863639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118838458604523426575759 3178257687906785139863639)
          ·
            refine ⟨4767386531860177709795459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178257687906785139863639 4767386531860177709795459)
            ·
              refine ⟨7151079797790266564693189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767386531860177709795459 7151079797790266564693189)
              ·
                refine ⟨1340827462085674980879973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7151079797790266564693189 1340827462085674980879973)
                ·
                  refine ⟨251405149141064058914995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340827462085674980879973 251405149141064058914995)
                  ·
                    rfl

theorem cell21_1101622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1101622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101622 prefixEnd_1101622 := by exact prefixLift 1101622
  have htrace : WordTrace (prefixWord ++ tailWord_1101622) baseStart_1101622 baseEnd_1101622 := by
    simpa [prefixWord, tailWord_1101622, baseEnd_1101622] using wordTrace_append hprefix tailTrace_1101622
  have hstable : (prefixWord ++ tailWord_1101622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101622).length < 2 ^ (prefixWord ++ tailWord_1101622).sum := by decide
  have hdescent : baseEnd_1101622 < baseStart_1101622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101650 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1101650 : Nat := 118140960795 + 1101650 * 2 ^ 59
def prefixEnd_1101650 : Nat := 4983230072969 + 3 ^ 40 * 1101650 * 2
def baseEnd_1101650 : Nat := 251411539122542232448271

theorem tailTrace_1101650 : CollatzResearch.WordTrace tailWord_1101650 prefixEnd_1101650 251411539122542232448271 := by
  unfold tailWord_1101650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045119114729417921493601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26786984305945114457316269 10045119114729417921493601)
  ·
    refine ⟨7533839336047063441120201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10045119114729417921493601 7533839336047063441120201)
    ·
      refine ⟨5650379502035297580840151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7533839336047063441120201 5650379502035297580840151)
      ·
        refine ⟨8475569253052946371260227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650379502035297580840151 8475569253052946371260227)
        ·
          refine ⟨12713353879579419556890341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475569253052946371260227 12713353879579419556890341)
          ·
            refine ⟨2383753852421141166916939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12713353879579419556890341 2383753852421141166916939)
            ·
              refine ⟨3575630778631711750375409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383753852421141166916939 3575630778631711750375409)
              ·
                refine ⟨2681723083973783812781557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575630778631711750375409 2681723083973783812781557)
                ·
                  refine ⟨251411539122542232448271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681723083973783812781557 251411539122542232448271)
                  ·
                    rfl

theorem cell21_1101650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1101650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101650 prefixEnd_1101650 := by exact prefixLift 1101650
  have htrace : WordTrace (prefixWord ++ tailWord_1101650) baseStart_1101650 baseEnd_1101650 := by
    simpa [prefixWord, tailWord_1101650, baseEnd_1101650] using wordTrace_append hprefix tailTrace_1101650
  have hstable : (prefixWord ++ tailWord_1101650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101650).length < 2 ^ (prefixWord ++ tailWord_1101650).sum := by decide
  have hdescent : baseEnd_1101650 < baseStart_1101650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101743 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 3]
def baseStart_1101743 : Nat := 118140960795 + 1101743 * 2 ^ 59
def prefixEnd_1101743 : Nat := 4983230072969 + 3 ^ 40 * 1101743 * 2
def baseEnd_1101743 : Nat := 251432762989594737398081

theorem tailTrace_1101743 : CollatzResearch.WordTrace tailWord_1101743 prefixEnd_1101743 251432762989594737398081 := by
  unfold tailWord_1101743
  simp only [CollatzResearch.WordTrace]
  refine ⟨40183868447580748569109883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26789245631720499046073255 40183868447580748569109883)
  ·
    refine ⟨60275802671371122853664825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40183868447580748569109883 60275802671371122853664825)
    ·
      refine ⟨45206852003528342140248619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60275802671371122853664825 45206852003528342140248619)
      ·
        refine ⟨67810278005292513210372929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45206852003528342140248619 67810278005292513210372929)
        ·
          refine ⟨50857708503969384907779697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67810278005292513210372929 50857708503969384907779697)
          ·
            refine ⟨38143281377977038680834773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50857708503969384907779697 38143281377977038680834773)
            ·
              refine ⟨893983157296336844082065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38143281377977038680834773 893983157296336844082065)
              ·
                refine ⟨670487367972252633061549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893983157296336844082065 670487367972252633061549)
                ·
                  refine ⟨251432762989594737398081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670487367972252633061549 251432762989594737398081)
                  ·
                    rfl

theorem cell21_1101743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].length) (baseStart_1101743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101743 prefixEnd_1101743 := by exact prefixLift 1101743
  have htrace : WordTrace (prefixWord ++ tailWord_1101743) baseStart_1101743 baseEnd_1101743 := by
    simpa [prefixWord, tailWord_1101743, baseEnd_1101743] using wordTrace_append hprefix tailTrace_1101743
  have hstable : (prefixWord ++ tailWord_1101743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101743).length < 2 ^ (prefixWord ++ tailWord_1101743).sum := by decide
  have hdescent : baseEnd_1101743 < baseStart_1101743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101757 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1101757 : Nat := 118140960795 + 1101757 * 2 ^ 59
def prefixEnd_1101757 : Nat := 4983230072969 + 3 ^ 40 * 1101757 * 2
def baseEnd_1101757 : Nat := 251435957980333824164719

theorem tailTrace_1101757 : CollatzResearch.WordTrace tailWord_1101757 prefixEnd_1101757 251435957980333824164719 := by
  unfold tailWord_1101757
  simp only [CollatzResearch.WordTrace]
  refine ⟨40184379069530028960119525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26789586046353352640079683 40184379069530028960119525)
  ·
    refine ⟨7534571075536880430022411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40184379069530028960119525 7534571075536880430022411)
    ·
      refine ⟨11301856613305320645033617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534571075536880430022411 11301856613305320645033617)
      ·
        refine ⟨8476392459978990483775213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11301856613305320645033617 8476392459978990483775213)
        ·
          refine ⟨3178647172492121431415705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8476392459978990483775213 3178647172492121431415705)
          ·
            refine ⟨2383985379369091073561779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178647172492121431415705 2383985379369091073561779)
            ·
              refine ⟨3575978069053636610342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383985379369091073561779 3575978069053636610342669)
              ·
                refine ⟨1340991775895113728878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3575978069053636610342669 1340991775895113728878501)
                ·
                  refine ⟨251435957980333824164719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340991775895113728878501 251435957980333824164719)
                  ·
                    rfl

theorem cell21_1101757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1101757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101757 prefixEnd_1101757 := by exact prefixLift 1101757
  have htrace : WordTrace (prefixWord ++ tailWord_1101757) baseStart_1101757 baseEnd_1101757 := by
    simpa [prefixWord, tailWord_1101757, baseEnd_1101757] using wordTrace_append hprefix tailTrace_1101757
  have hstable : (prefixWord ++ tailWord_1101757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101757).length < 2 ^ (prefixWord ++ tailWord_1101757).sum := by decide
  have hdescent : baseEnd_1101757 < baseStart_1101757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101788 : List Nat := [2, 2, 6, 1, 10]
def baseStart_1101788 : Nat := 118140960795 + 1101788 * 2 ^ 59
def prefixEnd_1101788 : Nat := 4983230072969 + 3 ^ 40 * 1101788 * 2
def baseEnd_1101788 : Nat := 3104234970403514310469

theorem tailTrace_1101788 : CollatzResearch.WordTrace tailWord_1101788 prefixEnd_1101788 3104234970403514310469 := by
  unfold tailWord_1101788
  simp only [CollatzResearch.WordTrace]
  refine ⟨20092754866208860627249009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26790339821611814169665345 20092754866208860627249009)
  ·
    refine ⟨15069566149656645470436757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20092754866208860627249009 15069566149656645470436757)
    ·
      refine ⟨706385913265155256426723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15069566149656645470436757 706385913265155256426723)
      ·
        refine ⟨1059578869897732884640085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706385913265155256426723 1059578869897732884640085)
        ·
          refine ⟨3104234970403514310469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1059578869897732884640085 3104234970403514310469)
          ·
            rfl

theorem cell21_1101788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 10].length) (baseStart_1101788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101788 prefixEnd_1101788 := by exact prefixLift 1101788
  have htrace : WordTrace (prefixWord ++ tailWord_1101788) baseStart_1101788 baseEnd_1101788 := by
    simpa [prefixWord, tailWord_1101788, baseEnd_1101788] using wordTrace_append hprefix tailTrace_1101788
  have hstable : (prefixWord ++ tailWord_1101788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101788).length < 2 ^ (prefixWord ++ tailWord_1101788).sum := by decide
  have hdescent : baseEnd_1101788 < baseStart_1101788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101794 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1101794 : Nat := 118140960795 + 1101794 * 2 ^ 59
def prefixEnd_1101794 : Nat := 4983230072969 + 3 ^ 40 * 1101794 * 2
def baseEnd_1101794 : Nat := 251444401884429982047977

theorem tailTrace_1101794 : CollatzResearch.WordTrace tailWord_1101794 prefixEnd_1101794 251444401884429982047977 := by
  unfold tailWord_1101794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046432142598996069804109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26790485713597322852810957 10046432142598996069804109)
  ·
    refine ⟨3767412053474623526176541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10046432142598996069804109 3767412053474623526176541)
    ·
      refine ⟨1412779520052983822316203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3767412053474623526176541 1412779520052983822316203)
      ·
        refine ⟨2119169280079475733474305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412779520052983822316203 2119169280079475733474305)
        ·
          refine ⟨1589376960059606800105729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119169280079475733474305 1589376960059606800105729)
          ·
            refine ⟨1192032720044705100079297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589376960059606800105729 1192032720044705100079297)
            ·
              refine ⟨894024540033528825059473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192032720044705100079297 894024540033528825059473)
              ·
                refine ⟨670518405025146618794605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894024540033528825059473 670518405025146618794605)
                ·
                  refine ⟨251444401884429982047977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670518405025146618794605 251444401884429982047977)
                  ·
                    rfl

theorem cell21_1101794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1101794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101794 prefixEnd_1101794 := by exact prefixLift 1101794
  have htrace : WordTrace (prefixWord ++ tailWord_1101794) baseStart_1101794 baseEnd_1101794 := by
    simpa [prefixWord, tailWord_1101794, baseEnd_1101794] using wordTrace_append hprefix tailTrace_1101794
  have hstable : (prefixWord ++ tailWord_1101794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101794).length < 2 ^ (prefixWord ++ tailWord_1101794).sum := by decide
  have hdescent : baseEnd_1101794 < baseStart_1101794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101805 : List Nat := [1, 5, 1, 4, 1, 2, 1, 6]
def baseStart_1101805 : Nat := 118140960795 + 1101805 * 2 ^ 59
def prefixEnd_1101805 : Nat := 4983230072969 + 3 ^ 40 * 1101805 * 2
def baseEnd_1101805 : Nat := 83815637411432135788207

theorem tailTrace_1101805 : CollatzResearch.WordTrace tailWord_1101805 prefixEnd_1101805 83815637411432135788207 := by
  unfold tailWord_1101805
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186129773356133157866869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26790753182237422105244579 40186129773356133157866869)
  ·
    refine ⟨3767449666252137483550019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40186129773356133157866869 3767449666252137483550019)
    ·
      refine ⟨5651174499378206225325029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767449666252137483550019 5651174499378206225325029)
      ·
        refine ⟨1059595218633413667248443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5651174499378206225325029 1059595218633413667248443)
        ·
          refine ⟨1589392827950120500872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059595218633413667248443 1589392827950120500872665)
          ·
            refine ⟨1192044620962590375654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589392827950120500872665 1192044620962590375654499)
            ·
              refine ⟨1788066931443885563481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192044620962590375654499 1788066931443885563481749)
              ·
                refine ⟨83815637411432135788207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1788066931443885563481749 83815637411432135788207)
                ·
                  rfl

theorem cell21_1101805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_1101805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101805 prefixEnd_1101805 := by exact prefixLift 1101805
  have htrace : WordTrace (prefixWord ++ tailWord_1101805) baseStart_1101805 baseEnd_1101805 := by
    simpa [prefixWord, tailWord_1101805, baseEnd_1101805] using wordTrace_append hprefix tailTrace_1101805
  have hstable : (prefixWord ++ tailWord_1101805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101805).length < 2 ^ (prefixWord ++ tailWord_1101805).sum := by decide
  have hdescent : baseEnd_1101805 < baseStart_1101805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101816 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_1101816 : Nat := 118140960795 + 1101816 * 2 ^ 59
def prefixEnd_1101816 : Nat := 4983230072969 + 3 ^ 40 * 1101816 * 2
def baseEnd_1101816 : Nat := 251449422584162832681265

theorem tailTrace_1101816 : CollatzResearch.WordTrace tailWord_1101816 prefixEnd_1101816 251449422584162832681265 := by
  unfold tailWord_1101816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20093265488158141018258651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26791020650877521357678201 20093265488158141018258651)
  ·
    refine ⟨30139898232237211527387977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20093265488158141018258651 30139898232237211527387977)
    ·
      refine ⟨22604923674177908645540983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30139898232237211527387977 22604923674177908645540983)
      ·
        refine ⟨33907385511266862968311475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22604923674177908645540983 33907385511266862968311475)
        ·
          refine ⟨50861078266900294452467213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33907385511266862968311475 50861078266900294452467213)
          ·
            refine ⟨19072904350087610419675205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50861078266900294452467213 19072904350087610419675205)
            ·
              refine ⟨3576169565641426953689101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19072904350087610419675205 3576169565641426953689101)
              ·
                refine ⟨1341063587115535107633413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3576169565641426953689101 1341063587115535107633413)
                ·
                  refine ⟨251449422584162832681265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341063587115535107633413 251449422584162832681265)
                  ·
                    rfl

theorem cell21_1101816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_1101816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101816 prefixEnd_1101816 := by exact prefixLift 1101816
  have htrace : WordTrace (prefixWord ++ tailWord_1101816) baseStart_1101816 baseEnd_1101816 := by
    simpa [prefixWord, tailWord_1101816, baseEnd_1101816] using wordTrace_append hprefix tailTrace_1101816
  have hstable : (prefixWord ++ tailWord_1101816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101816).length < 2 ^ (prefixWord ++ tailWord_1101816).sum := by decide
  have hdescent : baseEnd_1101816 < baseStart_1101816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101847 : List Nat := [1, 1, 3, 5, 2, 1, 8]
def baseStart_1101847 : Nat := 118140960795 + 1101847 * 2 ^ 59
def prefixEnd_1101847 : Nat := 4983230072969 + 3 ^ 40 * 1101847 * 2
def baseEnd_1101847 : Nat := 27939610800723740851615

theorem tailTrace_1101847 : CollatzResearch.WordTrace tailWord_1101847 prefixEnd_1101847 27939610800723740851615 := by
  unfold tailWord_1101847
  simp only [CollatzResearch.WordTrace]
  refine ⟨40187661639203974330895795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26791774426135982887263863 40187661639203974330895795)
  ·
    refine ⟨60281492458805961496343693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40187661639203974330895795 60281492458805961496343693)
    ·
      refine ⟨22605559672052235561128885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60281492458805961496343693 22605559672052235561128885)
      ·
        refine ⟨2119271219254897083855833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22605559672052235561128885 2119271219254897083855833)
        ·
          refine ⟨1589453414441172812891875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119271219254897083855833 1589453414441172812891875)
          ·
            refine ⟨2384180121661759219337813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589453414441172812891875 2384180121661759219337813)
            ·
              refine ⟨27939610800723740851615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2384180121661759219337813 27939610800723740851615)
              ·
                rfl

theorem cell21_1101847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_1101847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101847 prefixEnd_1101847 := by exact prefixLift 1101847
  have htrace : WordTrace (prefixWord ++ tailWord_1101847) baseStart_1101847 baseEnd_1101847 := by
    simpa [prefixWord, tailWord_1101847, baseEnd_1101847] using wordTrace_append hprefix tailTrace_1101847
  have hstable : (prefixWord ++ tailWord_1101847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101847).length < 2 ^ (prefixWord ++ tailWord_1101847).sum := by decide
  have hdescent : baseEnd_1101847 < baseStart_1101847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101861 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1101861 : Nat := 118140960795 + 1101861 * 2 ^ 59
def prefixEnd_1101861 : Nat := 4983230072969 + 3 ^ 40 * 1101861 * 2
def baseEnd_1101861 : Nat := 251459692197252754431173

theorem tailTrace_1101861 : CollatzResearch.WordTrace tailWord_1101861 prefixEnd_1101861 251459692197252754431173 := by
  unfold tailWord_1101861
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188172261153254721905437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26792114840768836481270291 40188172261153254721905437)
  ·
    refine ⟨15070564597932470520714539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40188172261153254721905437 15070564597932470520714539)
    ·
      refine ⟨22605846896898705781071809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15070564597932470520714539 22605846896898705781071809)
      ·
        refine ⟨16954385172674029335803857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22605846896898705781071809 16954385172674029335803857)
        ·
          refine ⟨12715788879505522001852893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16954385172674029335803857 12715788879505522001852893)
          ·
            refine ⟨4768420829814570750694835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12715788879505522001852893 4768420829814570750694835)
            ·
              refine ⟨7152631244721856126042253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768420829814570750694835 7152631244721856126042253)
              ·
                refine ⟨2682236716770696047265845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7152631244721856126042253 2682236716770696047265845)
                ·
                  refine ⟨251459692197252754431173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682236716770696047265845 251459692197252754431173)
                  ·
                    rfl

theorem cell21_1101861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1101861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101861 prefixEnd_1101861 := by exact prefixLift 1101861
  have htrace : WordTrace (prefixWord ++ tailWord_1101861) baseStart_1101861 baseEnd_1101861 := by
    simpa [prefixWord, tailWord_1101861, baseEnd_1101861] using wordTrace_append hprefix tailTrace_1101861
  have hstable : (prefixWord ++ tailWord_1101861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101861).length < 2 ^ (prefixWord ++ tailWord_1101861).sum := by decide
  have hdescent : baseEnd_1101861 < baseStart_1101861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101878 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1101878 : Nat := 118140960795 + 1101878 * 2 ^ 59
def prefixEnd_1101878 : Nat := 4983230072969 + 3 ^ 40 * 1101878 * 2
def baseEnd_1101878 : Nat := 251463571828864502647805

theorem tailTrace_1101878 : CollatzResearch.WordTrace tailWord_1101878 prefixEnd_1101878 251463571828864502647805 := by
  unfold tailWord_1101878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511799518880729164079643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26792528201394444416849525 2511799518880729164079643)
  ·
    refine ⟨3767699278321093746119465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511799518880729164079643 3767699278321093746119465)
    ·
      refine ⟨2825774458740820309589599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3767699278321093746119465 2825774458740820309589599)
      ·
        refine ⟨4238661688111230464384399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825774458740820309589599 4238661688111230464384399)
        ·
          refine ⟨6357992532166845696576599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238661688111230464384399 6357992532166845696576599)
          ·
            refine ⟨9536988798250268544864899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357992532166845696576599 9536988798250268544864899)
            ·
              refine ⟨14305483197375402817297349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9536988798250268544864899 14305483197375402817297349)
              ·
                refine ⟨2682278099507888028243253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14305483197375402817297349 2682278099507888028243253)
                ·
                  refine ⟨251463571828864502647805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682278099507888028243253 251463571828864502647805)
                  ·
                    rfl

theorem cell21_1101878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1101878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101878 prefixEnd_1101878 := by exact prefixLift 1101878
  have htrace : WordTrace (prefixWord ++ tailWord_1101878) baseStart_1101878 baseEnd_1101878 := by
    simpa [prefixWord, tailWord_1101878, baseEnd_1101878] using wordTrace_append hprefix tailTrace_1101878
  have hstable : (prefixWord ++ tailWord_1101878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101878).length < 2 ^ (prefixWord ++ tailWord_1101878).sum := by decide
  have hdescent : baseEnd_1101878 < baseStart_1101878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101881 : List Nat := [1, 2, 1, 5, 4, 1, 2, 5]
def baseStart_1101881 : Nat := 118140960795 + 1101881 * 2 ^ 59
def prefixEnd_1101881 : Nat := 4983230072969 + 3 ^ 40 * 1101881 * 2
def baseEnd_1101881 : Nat := 83821418823245721365933

theorem tailTrace_1101881 : CollatzResearch.WordTrace tailWord_1101881 prefixEnd_1101881 83821418823245721365933 := by
  unfold tailWord_1101881
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188901721080798137633497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26792601147387198758422331 40188901721080798137633497)
  ·
    refine ⟨30141676290810598603225123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40188901721080798137633497 30141676290810598603225123)
    ·
      refine ⟨45212514436215897904837685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30141676290810598603225123 45212514436215897904837685)
      ·
        refine ⟨4238673228395240428578533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45212514436215897904837685 4238673228395240428578533)
        ·
          refine ⟨794751230324107580358475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4238673228395240428578533 794751230324107580358475)
          ·
            refine ⟨1192126845486161370537713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794751230324107580358475 1192126845486161370537713)
            ·
              refine ⟨894095134114621027903285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192126845486161370537713 894095134114621027903285)
              ·
                refine ⟨83821418823245721365933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 894095134114621027903285 83821418823245721365933)
                ·
                  rfl

theorem cell21_1101881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].length) (baseStart_1101881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101881 prefixEnd_1101881 := by exact prefixLift 1101881
  have htrace : WordTrace (prefixWord ++ tailWord_1101881) baseStart_1101881 baseEnd_1101881 := by
    simpa [prefixWord, tailWord_1101881, baseEnd_1101881] using wordTrace_append hprefix tailTrace_1101881
  have hstable : (prefixWord ++ tailWord_1101881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101881).length < 2 ^ (prefixWord ++ tailWord_1101881).sum := by decide
  have hdescent : baseEnd_1101881 < baseStart_1101881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101968 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_1101968 : Nat := 118140960795 + 1101968 * 2 ^ 59
def prefixEnd_1101968 : Nat := 4983230072969 + 3 ^ 40 * 1101968 * 2
def baseEnd_1101968 : Nat := 251484111055044346147621

theorem tailTrace_1101968 : CollatzResearch.WordTrace tailWord_1101968 prefixEnd_1101968 251484111055044346147621 := by
  unfold tailWord_1101968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096037435882805998025279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26794716581177074664033705 20096037435882805998025279)
  ·
    refine ⟨30144056153824208997037919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20096037435882805998025279 30144056153824208997037919)
    ·
      refine ⟨45216084230736313495556879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30144056153824208997037919 45216084230736313495556879)
      ·
        refine ⟨67824126346104470243335319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45216084230736313495556879 67824126346104470243335319)
        ·
          refine ⟨101736189519156705365002979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67824126346104470243335319 101736189519156705365002979)
          ·
            refine ⟨152604284278735058047504469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101736189519156705365002979 152604284278735058047504469)
            ·
              refine ⟨1788331456391426461494193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 152604284278735058047504469 1788331456391426461494193)
              ·
                refine ⟨1341248592293569846120645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788331456391426461494193 1341248592293569846120645)
                ·
                  refine ⟨251484111055044346147621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341248592293569846120645 251484111055044346147621)
                  ·
                    rfl

theorem cell21_1101968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_1101968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1101968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1101968 prefixEnd_1101968 := by exact prefixLift 1101968
  have htrace : WordTrace (prefixWord ++ tailWord_1101968) baseStart_1101968 baseEnd_1101968 := by
    simpa [prefixWord, tailWord_1101968, baseEnd_1101968] using wordTrace_append hprefix tailTrace_1101968
  have hstable : (prefixWord ++ tailWord_1101968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101968).length < 2 ^ (prefixWord ++ tailWord_1101968).sum := by decide
  have hdescent : baseEnd_1101968 < baseStart_1101968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102027 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_1102027 : Nat := 118140960795 + 1102027 * 2 ^ 59
def prefixEnd_1102027 : Nat := 4983230072969 + 3 ^ 40 * 1102027 * 2
def baseEnd_1102027 : Nat := 251497575658873354664167

theorem tailTrace_1102027 : CollatzResearch.WordTrace tailWord_1102027 prefixEnd_1102027 251497575658873354664167 := by
  unfold tailWord_1102027
  simp only [CollatzResearch.WordTrace]
  refine ⟨40194226778551865072448335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26796151185701243381632223 40194226778551865072448335)
  ·
    refine ⟨60291340167827797608672503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40194226778551865072448335 60291340167827797608672503)
    ·
      refine ⟨90437010251741696413008755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60291340167827797608672503 90437010251741696413008755)
      ·
        refine ⟨135655515377612544619513133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90437010251741696413008755 135655515377612544619513133)
        ·
          refine ⟨50870818266604704232317425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135655515377612544619513133 50870818266604704232317425)
          ·
            refine ⟨38153113699953528174238069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50870818266604704232317425 38153113699953528174238069)
            ·
              refine ⟨3576854409370643266334819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38153113699953528174238069 3576854409370643266334819)
              ·
                refine ⟨5365281614055964899502229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576854409370643266334819 5365281614055964899502229)
                ·
                  refine ⟨251497575658873354664167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5365281614055964899502229 251497575658873354664167)
                  ·
                    rfl

theorem cell21_1102027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_1102027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102027 prefixEnd_1102027 := by exact prefixLift 1102027
  have htrace : WordTrace (prefixWord ++ tailWord_1102027) baseStart_1102027 baseEnd_1102027 := by
    simpa [prefixWord, tailWord_1102027, baseEnd_1102027] using wordTrace_append hprefix tailTrace_1102027
  have hstable : (prefixWord ++ tailWord_1102027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102027).length < 2 ^ (prefixWord ++ tailWord_1102027).sum := by decide
  have hdescent : baseEnd_1102027 < baseStart_1102027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102030 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1102030 : Nat := 118140960795 + 1102030 * 2 ^ 59
def prefixEnd_1102030 : Nat := 4983230072969 + 3 ^ 40 * 1102030 * 2
def baseEnd_1102030 : Nat := 251498260299746016114161

theorem tailTrace_1102030 : CollatzResearch.WordTrace tailWord_1102030 prefixEnd_1102030 251498260299746016114161 := by
  unfold tailWord_1102030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024292024692624573100943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26796224131693997723205029 5024292024692624573100943)
  ·
    refine ⟨7536438037038936859651415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5024292024692624573100943 7536438037038936859651415)
    ·
      refine ⟨11304657055558405289477123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7536438037038936859651415 11304657055558405289477123)
      ·
        refine ⟨16956985583337607934215685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11304657055558405289477123 16956985583337607934215685)
        ·
          refine ⟨3179434796875801487665441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16956985583337607934215685 3179434796875801487665441)
          ·
            refine ⟨2384576097656851115749081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179434796875801487665441 2384576097656851115749081)
            ·
              refine ⟨1788432073242638336811811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384576097656851115749081 1788432073242638336811811)
              ·
                refine ⟨2682648109863957505217717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788432073242638336811811 2682648109863957505217717)
                ·
                  refine ⟨251498260299746016114161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682648109863957505217717 251498260299746016114161)
                  ·
                    rfl

theorem cell21_1102030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1102030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102030 prefixEnd_1102030 := by exact prefixLift 1102030
  have htrace : WordTrace (prefixWord ++ tailWord_1102030) baseStart_1102030 baseEnd_1102030 := by
    simpa [prefixWord, tailWord_1102030, baseEnd_1102030] using wordTrace_append hprefix tailTrace_1102030
  have hstable : (prefixWord ++ tailWord_1102030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102030).length < 2 ^ (prefixWord ++ tailWord_1102030).sum := by decide
  have hdescent : baseEnd_1102030 < baseStart_1102030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102058 : List Nat := [3, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1102058 : Nat := 118140960795 + 1102058 * 2 ^ 59
def prefixEnd_1102058 : Nat := 4983230072969 + 3 ^ 40 * 1102058 * 2
def baseEnd_1102058 : Nat := 83834883427074729882479

theorem tailTrace_1102058 : CollatzResearch.WordTrace tailWord_1102058 prefixEnd_1102058 83834883427074729882479 := by
  unfold tailWord_1102058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048839360359889341706707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26796904960959704911217885 10048839360359889341706707)
  ·
    refine ⟨15073259040539834012560061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048839360359889341706707 15073259040539834012560061)
    ·
      refine ⟨5652472140202437754710023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15073259040539834012560061 5652472140202437754710023)
      ·
        refine ⟨8478708210303656632065035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652472140202437754710023 8478708210303656632065035)
        ·
          refine ⟨12718062315455484948097553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8478708210303656632065035 12718062315455484948097553)
          ·
            refine ⟨9538546736591613711073165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12718062315455484948097553 9538546736591613711073165)
            ·
              refine ⟨3576955026221855141652437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9538546736591613711073165 3576955026221855141652437)
              ·
                refine ⟨83834883427074729882479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3576955026221855141652437 83834883427074729882479)
                ·
                  rfl

theorem cell21_1102058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1102058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102058 prefixEnd_1102058 := by exact prefixLift 1102058
  have htrace : WordTrace (prefixWord ++ tailWord_1102058) baseStart_1102058 baseEnd_1102058 := by
    simpa [prefixWord, tailWord_1102058, baseEnd_1102058] using wordTrace_append hprefix tailTrace_1102058
  have hstable : (prefixWord ++ tailWord_1102058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102058).length < 2 ^ (prefixWord ++ tailWord_1102058).sum := by decide
  have hdescent : baseEnd_1102058 < baseStart_1102058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102072 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1102072 : Nat := 118140960795 + 1102072 * 2 ^ 59
def prefixEnd_1102072 : Nat := 4983230072969 + 3 ^ 40 * 1102072 * 2
def baseEnd_1102072 : Nat := 251507845271963276414075

theorem tailTrace_1102072 : CollatzResearch.WordTrace tailWord_1102072 prefixEnd_1102072 251507845271963276414075 := by
  unfold tailWord_1102072
  simp only [CollatzResearch.WordTrace]
  refine ⟨20097934031694418878918235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26797245375592558505224313 20097934031694418878918235)
  ·
    refine ⟨30146901047541628318377353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20097934031694418878918235 30146901047541628318377353)
    ·
      refine ⟨22610175785656221238783015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30146901047541628318377353 22610175785656221238783015)
      ·
        refine ⟨33915263678484331858174523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22610175785656221238783015 33915263678484331858174523)
        ·
          refine ⟨50872895517726497787261785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33915263678484331858174523 50872895517726497787261785)
          ·
            refine ⟨38154671638294873340446339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50872895517726497787261785 38154671638294873340446339)
            ·
              refine ⟨57232007457442310010669509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38154671638294873340446339 57232007457442310010669509)
              ·
                refine ⟨10731001398270433127000533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57232007457442310010669509 10731001398270433127000533)
                ·
                  refine ⟨251507845271963276414075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10731001398270433127000533 251507845271963276414075)
                  ·
                    rfl

theorem cell21_1102072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1102072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102072 prefixEnd_1102072 := by exact prefixLift 1102072
  have htrace : WordTrace (prefixWord ++ tailWord_1102072) baseStart_1102072 baseEnd_1102072 := by
    simpa [prefixWord, tailWord_1102072, baseEnd_1102072] using wordTrace_append hprefix tailTrace_1102072
  have hstable : (prefixWord ++ tailWord_1102072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102072).length < 2 ^ (prefixWord ++ tailWord_1102072).sum := by decide
  have hdescent : baseEnd_1102072 < baseStart_1102072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102089 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1102089 : Nat := 118140960795 + 1102089 * 2 ^ 59
def prefixEnd_1102089 : Nat := 4983230072969 + 3 ^ 40 * 1102089 * 2
def baseEnd_1102089 : Nat := 251511724903575024630707

theorem tailTrace_1102089 : CollatzResearch.WordTrace tailWord_1102089 prefixEnd_1102089 251511724903575024630707 := by
  unfold tailWord_1102089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40196488104327249661205321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26797658736218166440803547 40196488104327249661205321)
  ·
    refine ⟨30147366078245437245903991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40196488104327249661205321 30147366078245437245903991)
    ·
      refine ⟨45221049117368155868855987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30147366078245437245903991 45221049117368155868855987)
      ·
        refine ⟨67831573676052233803283981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45221049117368155868855987 67831573676052233803283981)
        ·
          refine ⟨25436840128519587676231493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67831573676052233803283981 25436840128519587676231493)
          ·
            refine ⟨4769407524097422689293405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25436840128519587676231493 4769407524097422689293405)
            ·
              refine ⟨1788527821536533508485027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4769407524097422689293405 1788527821536533508485027)
              ·
                refine ⟨2682791732304800262727541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788527821536533508485027 2682791732304800262727541)
                ·
                  refine ⟨251511724903575024630707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682791732304800262727541 251511724903575024630707)
                  ·
                    rfl

theorem cell21_1102089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1102089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102089 prefixEnd_1102089 := by exact prefixLift 1102089
  have htrace : WordTrace (prefixWord ++ tailWord_1102089) baseStart_1102089 baseEnd_1102089 := by
    simpa [prefixWord, tailWord_1102089, baseEnd_1102089] using wordTrace_append hprefix tailTrace_1102089
  have hstable : (prefixWord ++ tailWord_1102089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102089).length < 2 ^ (prefixWord ++ tailWord_1102089).sum := by decide
  have hdescent : baseEnd_1102089 < baseStart_1102089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102134 : List Nat := [5, 1, 2, 13]
def baseStart_1102134 : Nat := 118140960795 + 1102134 * 2 ^ 59
def prefixEnd_1102134 : Nat := 4983230072969 + 3 ^ 40 * 1102134 * 2
def baseEnd_1102134 : Nat := 1035069936282571795805

theorem tailTrace_1102134 : CollatzResearch.WordTrace tailWord_1102134 prefixEnd_1102134 1035069936282571795805 := by
  unfold tailWord_1102134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512383086822763896662091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26798752926109481564395637 2512383086822763896662091)
  ·
    refine ⟨3768574630234145844993137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512383086822763896662091 3768574630234145844993137)
    ·
      refine ⟨2826430972675609383744853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3768574630234145844993137 2826430972675609383744853)
      ·
        refine ⟨1035069936282571795805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2826430972675609383744853 1035069936282571795805)
        ·
          rfl

theorem cell21_1102134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 13].length) (baseStart_1102134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102134 prefixEnd_1102134 := by exact prefixLift 1102134
  have htrace : WordTrace (prefixWord ++ tailWord_1102134) baseStart_1102134 baseEnd_1102134 := by
    simpa [prefixWord, tailWord_1102134, baseEnd_1102134] using wordTrace_append hprefix tailTrace_1102134
  have hstable : (prefixWord ++ tailWord_1102134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102134).length < 2 ^ (prefixWord ++ tailWord_1102134).sum := by decide
  have hdescent : baseEnd_1102134 < baseStart_1102134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102137 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1102137 : Nat := 118140960795 + 1102137 * 2 ^ 59
def prefixEnd_1102137 : Nat := 4983230072969 + 3 ^ 40 * 1102137 * 2
def baseEnd_1102137 : Nat := 251522679157537607830609

theorem tailTrace_1102137 : CollatzResearch.WordTrace tailWord_1102137 prefixEnd_1102137 251522679157537607830609 := by
  unfold tailWord_1102137
  simp only [CollatzResearch.WordTrace]
  refine ⟨40198238808153353858952665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26798825872102235905968443 40198238808153353858952665)
  ·
    refine ⟨30148679106115015394214499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40198238808153353858952665 30148679106115015394214499)
    ·
      refine ⟨45223018659172523091321749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30148679106115015394214499 45223018659172523091321749)
      ·
        refine ⟨2119828999648712019905707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45223018659172523091321749 2119828999648712019905707)
        ·
          refine ⟨3179743499473068029858561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119828999648712019905707 3179743499473068029858561)
          ·
            refine ⟨2384807624604801022393921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179743499473068029858561 2384807624604801022393921)
            ·
              refine ⟨1788605718453600766795441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384807624604801022393921 1788605718453600766795441)
              ·
                refine ⟨1341454288840200575096581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788605718453600766795441 1341454288840200575096581)
                ·
                  refine ⟨251522679157537607830609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341454288840200575096581 251522679157537607830609)
                  ·
                    rfl

theorem cell21_1102137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1102137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102137 prefixEnd_1102137 := by exact prefixLift 1102137
  have htrace : WordTrace (prefixWord ++ tailWord_1102137) baseStart_1102137 baseEnd_1102137 := by
    simpa [prefixWord, tailWord_1102137, baseEnd_1102137] using wordTrace_append hprefix tailTrace_1102137
  have hstable : (prefixWord ++ tailWord_1102137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102137).length < 2 ^ (prefixWord ++ tailWord_1102137).sum := by decide
  have hdescent : baseEnd_1102137 < baseStart_1102137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102179 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_1102179 : Nat := 118140960795 + 1102179 * 2 ^ 59
def prefixEnd_1102179 : Nat := 4983230072969 + 3 ^ 40 * 1102179 * 2
def baseEnd_1102179 : Nat := 251532264129754868130523

theorem tailTrace_1102179 : CollatzResearch.WordTrace tailWord_1102179 prefixEnd_1102179 251532264129754868130523 := by
  unfold tailWord_1102179
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199770674001195031981591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26799847116000796687987727 40199770674001195031981591)
  ·
    refine ⟨60299656011001792547972387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40199770674001195031981591 60299656011001792547972387)
    ·
      refine ⟨90449484016502688821958581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60299656011001792547972387 90449484016502688821958581)
      ·
        refine ⟨8479639126547127077058617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90449484016502688821958581 8479639126547127077058617)
        ·
          refine ⟨6359729344910345307793963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479639126547127077058617 6359729344910345307793963)
          ·
            refine ⟨9539594017365517961690945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359729344910345307793963 9539594017365517961690945)
            ·
              refine ⟨7154695513024138471268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539594017365517961690945 7154695513024138471268209)
              ·
                refine ⟨5366021634768103853451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7154695513024138471268209 5366021634768103853451157)
                ·
                  refine ⟨251532264129754868130523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5366021634768103853451157 251532264129754868130523)
                  ·
                    rfl

theorem cell21_1102179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_1102179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102179 prefixEnd_1102179 := by exact prefixLift 1102179
  have htrace : WordTrace (prefixWord ++ tailWord_1102179) baseStart_1102179 baseEnd_1102179 := by
    simpa [prefixWord, tailWord_1102179, baseEnd_1102179] using wordTrace_append hprefix tailTrace_1102179
  have hstable : (prefixWord ++ tailWord_1102179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102179).length < 2 ^ (prefixWord ++ tailWord_1102179).sum := by decide
  have hdescent : baseEnd_1102179 < baseStart_1102179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102250 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_1102250 : Nat := 118140960795 + 1102250 * 2 ^ 59
def prefixEnd_1102250 : Nat := 4983230072969 + 3 ^ 40 * 1102250 * 2
def baseEnd_1102250 : Nat := 251548467297074522447045

theorem tailTrace_1102250 : CollatzResearch.WordTrace tailWord_1102250 prefixEnd_1102250 251548467297074522447045 := by
  unfold tailWord_1102250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050590064185993539454051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26801573504495982771877469 10050590064185993539454051)
  ·
    refine ⟨15075885096278990309181077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10050590064185993539454051 15075885096278990309181077)
    ·
      refine ⟨706682113888077670742863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15075885096278990309181077 706682113888077670742863)
      ·
        refine ⟨1060023170832116506114295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706682113888077670742863 1060023170832116506114295)
        ·
          refine ⟨1590034756248174759171443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060023170832116506114295 1590034756248174759171443)
          ·
            refine ⟨2385052134372262138757165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590034756248174759171443 2385052134372262138757165)
            ·
              refine ⟨894394550389598302033937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2385052134372262138757165 894394550389598302033937)
              ·
                refine ⟨670795912792198726525453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894394550389598302033937 670795912792198726525453)
                ·
                  refine ⟨251548467297074522447045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670795912792198726525453 251548467297074522447045)
                  ·
                    rfl

theorem cell21_1102250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_1102250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102250 prefixEnd_1102250 := by exact prefixLift 1102250
  have htrace : WordTrace (prefixWord ++ tailWord_1102250) baseStart_1102250 baseEnd_1102250 := by
    simpa [prefixWord, tailWord_1102250, baseEnd_1102250] using wordTrace_append hprefix tailTrace_1102250
  have hstable : (prefixWord ++ tailWord_1102250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102250).length < 2 ^ (prefixWord ++ tailWord_1102250).sum := by decide
  have hdescent : baseEnd_1102250 < baseStart_1102250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102309 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1102309 : Nat := 118140960795 + 1102309 * 2 ^ 59
def prefixEnd_1102309 : Nat := 4983230072969 + 3 ^ 40 * 1102309 * 2
def baseEnd_1102309 : Nat := 251561931900903530963591

theorem tailTrace_1102309 : CollatzResearch.WordTrace tailWord_1102309 prefixEnd_1102309 251561931900903530963591 := by
  unfold tailWord_1102309
  simp only [CollatzResearch.WordTrace]
  refine ⟨40204512163530227234213981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26803008109020151489475987 40204512163530227234213981)
  ·
    refine ⟨15076692061323835212830243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40204512163530227234213981 15076692061323835212830243)
    ·
      refine ⟨22615038091985752819245365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15076692061323835212830243 22615038091985752819245365)
      ·
        refine ⟨2120159821123664326804253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22615038091985752819245365 2120159821123664326804253)
        ·
          refine ⟨795059932921374122551595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2120159821123664326804253 795059932921374122551595)
          ·
            refine ⟨1192589899382061183827393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795059932921374122551595 1192589899382061183827393)
            ·
              refine ⟨894442424536545887870545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192589899382061183827393 894442424536545887870545)
              ·
                refine ⟨670831818402409415902909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894442424536545887870545 670831818402409415902909)
                ·
                  refine ⟨251561931900903530963591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670831818402409415902909 251561931900903530963591)
                  ·
                    rfl

theorem cell21_1102309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1102309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102309 prefixEnd_1102309 := by exact prefixLift 1102309
  have htrace : WordTrace (prefixWord ++ tailWord_1102309) baseStart_1102309 baseEnd_1102309 := by
    simpa [prefixWord, tailWord_1102309, baseEnd_1102309] using wordTrace_append hprefix tailTrace_1102309
  have hstable : (prefixWord ++ tailWord_1102309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102309).length < 2 ^ (prefixWord ++ tailWord_1102309).sum := by decide
  have hdescent : baseEnd_1102309 < baseStart_1102309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102365 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1102365 : Nat := 118140960795 + 1102365 * 2 ^ 59
def prefixEnd_1102365 : Nat := 4983230072969 + 3 ^ 40 * 1102365 * 2
def baseEnd_1102365 : Nat := 251574711863859878030143

theorem tailTrace_1102365 : CollatzResearch.WordTrace tailWord_1102365 prefixEnd_1102365 251574711863859878030143 := by
  unfold tailWord_1102365
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206554651327348798252549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26804369767551565865501699 40206554651327348798252549)
  ·
    refine ⟨7538728997123877899672353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40206554651327348798252549 7538728997123877899672353)
    ·
      refine ⟨5654046747842908424754265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7538728997123877899672353 5654046747842908424754265)
      ·
        refine ⟨4240535060882181318565699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5654046747842908424754265 4240535060882181318565699)
        ·
          refine ⟨6360802591323271977848549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240535060882181318565699 6360802591323271977848549)
          ·
            refine ⟨1192650485873113495846603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6360802591323271977848549 1192650485873113495846603)
            ·
              refine ⟨1788975728809670243769905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192650485873113495846603 1788975728809670243769905)
              ·
                refine ⟨1341731796607252682827429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788975728809670243769905 1341731796607252682827429)
                ·
                  refine ⟨251574711863859878030143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341731796607252682827429 251574711863859878030143)
                  ·
                    rfl

theorem cell21_1102365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1102365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102365 prefixEnd_1102365 := by exact prefixLift 1102365
  have htrace : WordTrace (prefixWord ++ tailWord_1102365) baseStart_1102365 baseEnd_1102365 := by
    simpa [prefixWord, tailWord_1102365, baseEnd_1102365] using wordTrace_append hprefix tailTrace_1102365
  have hstable : (prefixWord ++ tailWord_1102365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102365).length < 2 ^ (prefixWord ++ tailWord_1102365).sum := by decide
  have hdescent : baseEnd_1102365 < baseStart_1102365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102382 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1102382 : Nat := 118140960795 + 1102382 * 2 ^ 59
def prefixEnd_1102382 : Nat := 4983230072969 + 3 ^ 40 * 1102382 * 2
def baseEnd_1102382 : Nat := 251578591495471626246775

theorem tailTrace_1102382 : CollatzResearch.WordTrace tailWord_1102382 prefixEnd_1102382 251578591495471626246775 := by
  unfold tailWord_1102382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025896836533220087702675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26804783128177173801080933 5025896836533220087702675)
  ·
    refine ⟨7538845254799830131554013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025896836533220087702675 7538845254799830131554013)
    ·
      refine ⟨2827066970549936299332755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7538845254799830131554013 2827066970549936299332755)
      ·
        refine ⟨4240600455824904448999133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827066970549936299332755 4240600455824904448999133)
        ·
          refine ⟨1590225170934339168374675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4240600455824904448999133 1590225170934339168374675)
          ·
            refine ⟨2385337756401508752562013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590225170934339168374675 2385337756401508752562013)
            ·
              refine ⟨894501658650565782210755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2385337756401508752562013 894501658650565782210755)
              ·
                refine ⟨1341752487975848673316133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894501658650565782210755 1341752487975848673316133)
                ·
                  refine ⟨251578591495471626246775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341752487975848673316133 251578591495471626246775)
                  ·
                    rfl

theorem cell21_1102382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1102382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102382 prefixEnd_1102382 := by exact prefixLift 1102382
  have htrace : WordTrace (prefixWord ++ tailWord_1102382) baseStart_1102382 baseEnd_1102382 := by
    simpa [prefixWord, tailWord_1102382, baseEnd_1102382] using wordTrace_append hprefix tailTrace_1102382
  have hstable : (prefixWord ++ tailWord_1102382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102382).length < 2 ^ (prefixWord ++ tailWord_1102382).sum := by decide
  have hdescent : baseEnd_1102382 < baseStart_1102382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102407 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_1102407 : Nat := 118140960795 + 1102407 * 2 ^ 59
def prefixEnd_1102407 : Nat := 4983230072969 + 3 ^ 40 * 1102407 * 2
def baseEnd_1102407 : Nat := 251584296836077138330057

theorem tailTrace_1102407 : CollatzResearch.WordTrace tailWord_1102407 prefixEnd_1102407 251584296836077138330057 := by
  unfold tailWord_1102407
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208086517175189971281475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26805391011450126647520983 40208086517175189971281475)
  ·
    refine ⟨60312129775762784956922213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40208086517175189971281475 60312129775762784956922213)
    ·
      refine ⟨11308524332955522179422915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60312129775762784956922213 11308524332955522179422915)
      ·
        refine ⟨16962786499433283269134373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308524332955522179422915 16962786499433283269134373)
        ·
          refine ⟨3180522468643740612962695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16962786499433283269134373 3180522468643740612962695)
          ·
            refine ⟨4770783702965610919444043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180522468643740612962695 4770783702965610919444043)
            ·
              refine ⟨7156175554448416379166065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770783702965610919444043 7156175554448416379166065)
              ·
                refine ⟨5367131665836312284374549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156175554448416379166065 5367131665836312284374549)
                ·
                  refine ⟨251584296836077138330057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5367131665836312284374549 251584296836077138330057)
                  ·
                    rfl

theorem cell21_1102407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_1102407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102407 prefixEnd_1102407 := by exact prefixLift 1102407
  have htrace : WordTrace (prefixWord ++ tailWord_1102407) baseStart_1102407 baseEnd_1102407 := by
    simpa [prefixWord, tailWord_1102407, baseEnd_1102407] using wordTrace_append hprefix tailTrace_1102407
  have hstable : (prefixWord ++ tailWord_1102407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102407).length < 2 ^ (prefixWord ++ tailWord_1102407).sum := by decide
  have hdescent : baseEnd_1102407 < baseStart_1102407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102410 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_1102410 : Nat := 118140960795 + 1102410 * 2 ^ 59
def prefixEnd_1102410 : Nat := 4983230072969 + 3 ^ 40 * 1102410 * 2
def baseEnd_1102410 : Nat := 251584981476949799780051

theorem tailTrace_1102410 : CollatzResearch.WordTrace tailWord_1102410 prefixEnd_1102410 251584981476949799780051 := by
  unfold tailWord_1102410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052048984041080370910171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26805463957442880989093789 10052048984041080370910171)
  ·
    refine ⟨15078073476061620556365257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052048984041080370910171 15078073476061620556365257)
    ·
      refine ⟨11308555107046215417273943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15078073476061620556365257 11308555107046215417273943)
      ·
        refine ⟨16962832660569323125910915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308555107046215417273943 16962832660569323125910915)
        ·
          refine ⟨25444248990853984688866373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16962832660569323125910915 25444248990853984688866373)
          ·
            refine ⟨4770796685785122129162445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25444248990853984688866373 4770796685785122129162445)
            ·
              refine ⟨1789048757169420798435917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4770796685785122129162445 1789048757169420798435917)
              ·
                refine ⟨670893283938532799413469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789048757169420798435917 670893283938532799413469)
                ·
                  refine ⟨251584981476949799780051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670893283938532799413469 251584981476949799780051)
                  ·
                    rfl

theorem cell21_1102410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_1102410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102410 prefixEnd_1102410 := by exact prefixLift 1102410
  have htrace : WordTrace (prefixWord ++ tailWord_1102410) baseStart_1102410 baseEnd_1102410 := by
    simpa [prefixWord, tailWord_1102410, baseEnd_1102410] using wordTrace_append hprefix tailTrace_1102410
  have hstable : (prefixWord ++ tailWord_1102410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102410).length < 2 ^ (prefixWord ++ tailWord_1102410).sum := by decide
  have hdescent : baseEnd_1102410 < baseStart_1102410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102421 : List Nat := [1, 3, 2, 2, 1, 1, 11]
def baseStart_1102421 : Nat := 118140960795 + 1102421 * 2 ^ 59
def prefixEnd_1102421 : Nat := 4983230072969 + 3 ^ 40 * 1102421 * 2
def baseEnd_1102421 : Nat := 27954165758535136121855

theorem tailTrace_1102421 : CollatzResearch.WordTrace tailWord_1102421 prefixEnd_1102421 27954165758535136121855 := by
  unfold tailWord_1102421
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208597139124470362291117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26805731426082980241527411 40208597139124470362291117)
  ·
    refine ⟨15078223927171676385859169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40208597139124470362291117 15078223927171676385859169)
    ·
      refine ⟨11308667945378757289394377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15078223927171676385859169 11308667945378757289394377)
      ·
        refine ⟨8481500959034067967045783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11308667945378757289394377 8481500959034067967045783)
        ·
          refine ⟨12722251438551101950568675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481500959034067967045783 12722251438551101950568675)
          ·
            refine ⟨19083377157826652925853013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722251438551101950568675 19083377157826652925853013)
            ·
              refine ⟨27954165758535136121855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19083377157826652925853013 27954165758535136121855)
              ·
                rfl

theorem cell21_1102421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 11].length) (baseStart_1102421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102421 prefixEnd_1102421 := by exact prefixLift 1102421
  have htrace : WordTrace (prefixWord ++ tailWord_1102421) baseStart_1102421 baseEnd_1102421 := by
    simpa [prefixWord, tailWord_1102421, baseEnd_1102421] using wordTrace_append hprefix tailTrace_1102421
  have hstable : (prefixWord ++ tailWord_1102421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102421).length < 2 ^ (prefixWord ++ tailWord_1102421).sum := by decide
  have hdescent : baseEnd_1102421 < baseStart_1102421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102534 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1102534 : Nat := 118140960795 + 1102534 * 2 ^ 59
def prefixEnd_1102534 : Nat := 4983230072969 + 3 ^ 40 * 1102534 * 2
def baseEnd_1102534 : Nat := 251613279966353139713131

theorem tailTrace_1102534 : CollatzResearch.WordTrace tailWord_1102534 prefixEnd_1102534 251613279966353139713131 := by
  unfold tailWord_1102534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256647455866096583161083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26808479058476727107436437 1256647455866096583161083)
  ·
    refine ⟨1884971183799144874741625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256647455866096583161083 1884971183799144874741625)
    ·
      refine ⟨1413728387849358656056219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884971183799144874741625 1413728387849358656056219)
      ·
        refine ⟨2120592581774037984084329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413728387849358656056219 2120592581774037984084329)
        ·
          refine ⟨1590444436330528488063247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120592581774037984084329 1590444436330528488063247)
          ·
            refine ⟨2385666654495792732094871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590444436330528488063247 2385666654495792732094871)
            ·
              refine ⟨3578499981743689098142307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385666654495792732094871 3578499981743689098142307)
              ·
                refine ⟨5367749972615533647213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578499981743689098142307 5367749972615533647213461)
                ·
                  refine ⟨251613279966353139713131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5367749972615533647213461 251613279966353139713131)
                  ·
                    rfl

theorem cell21_1102534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1102534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102534 prefixEnd_1102534 := by exact prefixLift 1102534
  have htrace : WordTrace (prefixWord ++ tailWord_1102534) baseStart_1102534 baseEnd_1102534 := by
    simpa [prefixWord, tailWord_1102534, baseEnd_1102534] using wordTrace_append hprefix tailTrace_1102534
  have hstable : (prefixWord ++ tailWord_1102534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102534).length < 2 ^ (prefixWord ++ tailWord_1102534).sum := by decide
  have hdescent : baseEnd_1102534 < baseStart_1102534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102545 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 3]
def baseStart_1102545 : Nat := 118140960795 + 1102545 * 2 ^ 59
def prefixEnd_1102545 : Nat := 4983230072969 + 3 ^ 40 * 1102545 * 2
def baseEnd_1102545 : Nat := 251615790316219565029775

theorem tailTrace_1102545 : CollatzResearch.WordTrace tailWord_1102545 prefixEnd_1102545 251615790316219565029775 := by
  unfold tailWord_1102545
  simp only [CollatzResearch.WordTrace]
  refine ⟨40213119790675239539805089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26808746527116826359870059 40213119790675239539805089)
  ·
    refine ⟨30159839843006429654853817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40213119790675239539805089 30159839843006429654853817)
    ·
      refine ⟨22619879882254822241140363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30159839843006429654853817 22619879882254822241140363)
      ·
        refine ⟨33929819823382233361710545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22619879882254822241140363 33929819823382233361710545)
        ·
          refine ⟨25447364867536675021282909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33929819823382233361710545 25447364867536675021282909)
          ·
            refine ⟨9542761825326253132981091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25447364867536675021282909 9542761825326253132981091)
            ·
              refine ⟨14314142737989379699471637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542761825326253132981091 14314142737989379699471637)
              ·
                refine ⟨670975440843252173412733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14314142737989379699471637 670975440843252173412733)
                ·
                  refine ⟨251615790316219565029775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670975440843252173412733 251615790316219565029775)
                  ·
                    rfl

theorem cell21_1102545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_1102545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102545 prefixEnd_1102545 := by exact prefixLift 1102545
  have htrace : WordTrace (prefixWord ++ tailWord_1102545) baseStart_1102545 baseEnd_1102545 := by
    simpa [prefixWord, tailWord_1102545, baseEnd_1102545] using wordTrace_append hprefix tailTrace_1102545
  have hstable : (prefixWord ++ tailWord_1102545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102545).length < 2 ^ (prefixWord ++ tailWord_1102545).sum := by decide
  have hdescent : baseEnd_1102545 < baseStart_1102545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102590 : List Nat := [4, 2, 2, 1, 2, 1, 9]
def baseStart_1102590 : Nat := 118140960795 + 1102590 * 2 ^ 59
def prefixEnd_1102590 : Nat := 4983230072969 + 3 ^ 40 * 1102590 * 2
def baseEnd_1102590 : Nat := 27958451103256609642187

theorem tailTrace_1102590 : CollatzResearch.WordTrace tailWord_1102590 prefixEnd_1102590 27958451103256609642187 := by
  unfold tailWord_1102590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026845134439026528149153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26809840717008141483462149 5026845134439026528149153)
  ·
    refine ⟨3770133850829269896111865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5026845134439026528149153 3770133850829269896111865)
    ·
      refine ⟨2827600388121952422083899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3770133850829269896111865 2827600388121952422083899)
      ·
        refine ⟨4241400582182928633125849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827600388121952422083899 4241400582182928633125849)
        ·
          refine ⟨3181050436637196474844387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4241400582182928633125849 3181050436637196474844387)
          ·
            refine ⟨4771575654955794712266581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181050436637196474844387 4771575654955794712266581)
            ·
              refine ⟨27958451103256609642187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4771575654955794712266581 27958451103256609642187)
              ·
                rfl

theorem cell21_1102590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 9].length) (baseStart_1102590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102590 prefixEnd_1102590 := by exact prefixLift 1102590
  have htrace : WordTrace (prefixWord ++ tailWord_1102590) baseStart_1102590 baseEnd_1102590 := by
    simpa [prefixWord, tailWord_1102590, baseEnd_1102590] using wordTrace_append hprefix tailTrace_1102590
  have hstable : (prefixWord ++ tailWord_1102590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102590).length < 2 ^ (prefixWord ++ tailWord_1102590).sum := by decide
  have hdescent : baseEnd_1102590 < baseStart_1102590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102655 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 3]
def baseStart_1102655 : Nat := 118140960795 + 1102655 * 2 ^ 59
def prefixEnd_1102655 : Nat := 4983230072969 + 3 ^ 40 * 1102655 * 2
def baseEnd_1102655 : Nat := 251640893814883818196217

theorem tailTrace_1102655 : CollatzResearch.WordTrace tailWord_1102655 prefixEnd_1102655 251640893814883818196217 := by
  unfold tailWord_1102655
  simp only [CollatzResearch.WordTrace]
  refine ⟨40217131820276728326309419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26811421213517818884206279 40217131820276728326309419)
  ·
    refine ⟨60325697730415092489464129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40217131820276728326309419 60325697730415092489464129)
    ·
      refine ⟨45244273297811319367098097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60325697730415092489464129 45244273297811319367098097)
      ·
        refine ⟨33933204973358489525323573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45244273297811319367098097 33933204973358489525323573)
        ·
          refine ⟨3181237966252358392999085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33933204973358489525323573 3181237966252358392999085)
          ·
            refine ⟨1192964237344634397374657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3181237966252358392999085 1192964237344634397374657)
            ·
              refine ⟨894723178008475798030993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192964237344634397374657 894723178008475798030993)
              ·
                refine ⟨671042383506356848523245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894723178008475798030993 671042383506356848523245)
                ·
                  refine ⟨251640893814883818196217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671042383506356848523245 251640893814883818196217)
                  ·
                    rfl

theorem cell21_1102655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].length) (baseStart_1102655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102655 prefixEnd_1102655 := by exact prefixLift 1102655
  have htrace : WordTrace (prefixWord ++ tailWord_1102655) baseStart_1102655 baseEnd_1102655 := by
    simpa [prefixWord, tailWord_1102655, baseEnd_1102655] using wordTrace_append hprefix tailTrace_1102655
  have hstable : (prefixWord ++ tailWord_1102655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102655).length < 2 ^ (prefixWord ++ tailWord_1102655).sum := by decide
  have hdescent : baseEnd_1102655 < baseStart_1102655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102739 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_1102739 : Nat := 118140960795 + 1102739 * 2 ^ 59
def prefixEnd_1102739 : Nat := 4983230072969 + 3 ^ 40 * 1102739 * 2
def baseEnd_1102739 : Nat := 251660063759318338796045

theorem tailTrace_1102739 : CollatzResearch.WordTrace tailWord_1102739 prefixEnd_1102739 251660063759318338796045 := by
  unfold tailWord_1102739
  simp only [CollatzResearch.WordTrace]
  refine ⟨40220195551972410672367271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26813463701314940448244847 40220195551972410672367271)
  ·
    refine ⟨60330293327958616008550907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40220195551972410672367271 60330293327958616008550907)
    ·
      refine ⟨90495439991937924012826361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60330293327958616008550907 90495439991937924012826361)
      ·
        refine ⟨67871579993953443009619771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90495439991937924012826361 67871579993953443009619771)
        ·
          refine ⟨101807369990930164514429657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67871579993953443009619771 101807369990930164514429657)
          ·
            refine ⟨76355527493197623385822243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101807369990930164514429657 76355527493197623385822243)
            ·
              refine ⟨114533291239796435078733365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76355527493197623385822243 114533291239796435078733365)
              ·
                refine ⟨10737496053730915788631253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114533291239796435078733365 10737496053730915788631253)
                ·
                  refine ⟨251660063759318338796045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10737496053730915788631253 251660063759318338796045)
                  ·
                    rfl

theorem cell21_1102739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_1102739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102739 prefixEnd_1102739 := by exact prefixLift 1102739
  have htrace : WordTrace (prefixWord ++ tailWord_1102739) baseStart_1102739 baseEnd_1102739 := by
    simpa [prefixWord, tailWord_1102739, baseEnd_1102739] using wordTrace_append hprefix tailTrace_1102739
  have hstable : (prefixWord ++ tailWord_1102739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102739).length < 2 ^ (prefixWord ++ tailWord_1102739).sum := by decide
  have hdescent : baseEnd_1102739 < baseStart_1102739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102748 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_1102748 : Nat := 118140960795 + 1102748 * 2 ^ 59
def prefixEnd_1102748 : Nat := 4983230072969 + 3 ^ 40 * 1102748 * 2
def baseEnd_1102748 : Nat := 251662117681936323146027

theorem tailTrace_1102748 : CollatzResearch.WordTrace tailWord_1102748 prefixEnd_1102748 251662117681936323146027 := by
  unfold tailWord_1102748
  simp only [CollatzResearch.WordTrace]
  refine ⟨20110261904469902604722449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26813682539293203472963265 20110261904469902604722449)
  ·
    refine ⟨15082696428352426953541837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20110261904469902604722449 15082696428352426953541837)
    ·
      refine ⟨5656011160632160107578189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15082696428352426953541837 5656011160632160107578189)
      ·
        refine ⟨2121004185237060040341821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5656011160632160107578189 2121004185237060040341821)
        ·
          refine ⟨795376569463897515128183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2121004185237060040341821 795376569463897515128183)
          ·
            refine ⟨1193064854195846272692275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795376569463897515128183 1193064854195846272692275)
            ·
              refine ⟨1789597281293769409038413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193064854195846272692275 1789597281293769409038413)
              ·
                refine ⟨671098980485163528389405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789597281293769409038413 671098980485163528389405)
                ·
                  refine ⟨251662117681936323146027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671098980485163528389405 251662117681936323146027)
                  ·
                    rfl

theorem cell21_1102748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_1102748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102748 prefixEnd_1102748 := by exact prefixLift 1102748
  have htrace : WordTrace (prefixWord ++ tailWord_1102748) baseStart_1102748 baseEnd_1102748 := by
    simpa [prefixWord, tailWord_1102748, baseEnd_1102748] using wordTrace_append hprefix tailTrace_1102748
  have hstable : (prefixWord ++ tailWord_1102748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102748).length < 2 ^ (prefixWord ++ tailWord_1102748).sum := by decide
  have hdescent : baseEnd_1102748 < baseStart_1102748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
