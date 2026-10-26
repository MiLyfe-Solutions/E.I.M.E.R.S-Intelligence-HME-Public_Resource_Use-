import V185TrunkScan23Chunk1074

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6364765 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6364765 : Nat := 118140960795 + 6364765 * 2 ^ 59
def prefixEnd_6364765 : Nat := 4983230072969 + 3 ^ 40 * 6364765 * 2
def baseEnd_6364765 : Nat := 1089394565971298520455495

theorem tailTrace_6364765 : CollatzResearch.WordTrace tailWord_6364765 prefixEnd_6364765 1089394565971298520455495 := by
  unfold tailWord_6364765
  simp only [CollatzResearch.WordTrace]
  refine ⟨232142050786550895165399749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154761367191033930110266499 232142050786550895165399749)
  ·
    refine ⟨43526634522478292843512453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232142050786550895165399749 43526634522478292843512453)
    ·
      refine ⟨8161243972964679908158585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43526634522478292843512453 8161243972964679908158585)
      ·
        refine ⟨6120932979723509931118939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8161243972964679908158585 6120932979723509931118939)
        ·
          refine ⟨9181399469585264896678409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6120932979723509931118939 9181399469585264896678409)
          ·
            refine ⟨6886049602188948672508807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9181399469585264896678409 6886049602188948672508807)
            ·
              refine ⟨10329074403283423008763211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886049602188948672508807 10329074403283423008763211)
              ·
                refine ⟨15493611604925134513144817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329074403283423008763211 15493611604925134513144817)
                ·
                  refine ⟨11620208703693850884858613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15493611604925134513144817 11620208703693850884858613)
                  ·
                    refine ⟨1089394565971298520455495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11620208703693850884858613 1089394565971298520455495)
                    ·
                      rfl

theorem cell23_6364765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6364765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364765 prefixEnd_6364765 := by exact prefixLift 6364765
  have htrace : WordTrace (prefixWord ++ tailWord_6364765) baseStart_6364765 baseEnd_6364765 := by
    simpa [prefixWord, tailWord_6364765, baseEnd_6364765] using wordTrace_append hprefix tailTrace_6364765
  have hstable : (prefixWord ++ tailWord_6364765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364765).length < 2 ^ (prefixWord ++ tailWord_6364765).sum := by decide
  have hdescent : baseEnd_6364765 < baseStart_6364765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364771 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3]
def baseStart_6364771 : Nat := 118140960795 + 6364771 * 2 ^ 59
def prefixEnd_6364771 : Nat := 4983230072969 + 3 ^ 40 * 6364771 * 2
def baseEnd_6364771 : Nat := 3268186778797822537891457

theorem tailTrace_6364771 : CollatzResearch.WordTrace tailWord_6364771 prefixEnd_6364771 3268186778797822537891457 := by
  unfold tailWord_6364771
  simp only [CollatzResearch.WordTrace]
  refine ⟨232142269624529158190118167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154761513083019438793412111 232142269624529158190118167)
  ·
    refine ⟨348213404436793737285177251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232142269624529158190118167 348213404436793737285177251)
    ·
      refine ⟨522320106655190605927765877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348213404436793737285177251 522320106655190605927765877)
      ·
        refine ⟨48967509998924119305728051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 522320106655190605927765877 48967509998924119305728051)
        ·
          refine ⟨73451264998386178958592077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48967509998924119305728051 73451264998386178958592077)
          ·
            refine ⟨27544224374394817109472029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73451264998386178958592077 27544224374394817109472029)
            ·
              refine ⟨10329084140398056416052011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27544224374394817109472029 10329084140398056416052011)
              ·
                refine ⟨15493626210597084624078017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329084140398056416052011 15493626210597084624078017)
                ·
                  refine ⟨11620219657947813468058513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15493626210597084624078017 11620219657947813468058513)
                  ·
                    refine ⟨8715164743460860101043885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11620219657947813468058513 8715164743460860101043885)
                    ·
                      refine ⟨3268186778797822537891457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715164743460860101043885 3268186778797822537891457)
                      ·
                        rfl

theorem cell23_6364771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_6364771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364771 prefixEnd_6364771 := by exact prefixLift 6364771
  have htrace : WordTrace (prefixWord ++ tailWord_6364771) baseStart_6364771 baseEnd_6364771 := by
    simpa [prefixWord, tailWord_6364771, baseEnd_6364771] using wordTrace_append hprefix tailTrace_6364771
  have hstable : (prefixWord ++ tailWord_6364771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364771).length < 2 ^ (prefixWord ++ tailWord_6364771).sum := by decide
  have hdescent : baseEnd_6364771 < baseStart_6364771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364778 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_6364778 : Nat := 118140960795 + 6364778 * 2 ^ 59
def prefixEnd_6364778 : Nat := 4983230072969 + 3 ^ 40 * 6364778 * 2
def baseEnd_6364778 : Nat := 1089396791054134670167975

theorem tailTrace_6364778 : CollatzResearch.WordTrace tailWord_6364778 prefixEnd_6364778 1089396791054134670167975 := by
  unfold tailWord_6364778
  simp only [CollatzResearch.WordTrace]
  refine ⟨58035631233875949596405747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154761683290335865590415325 58035631233875949596405747)
  ·
    refine ⟨87053446850813924394608621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58035631233875949596405747 87053446850813924394608621)
    ·
      refine ⟨32645042569055221647978233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87053446850813924394608621 32645042569055221647978233)
      ·
        refine ⟨24483781926791416235983675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32645042569055221647978233 24483781926791416235983675)
        ·
          refine ⟨36725672890187124353975513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24483781926791416235983675 36725672890187124353975513)
          ·
            refine ⟨27544254667640343265481635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36725672890187124353975513 27544254667640343265481635)
            ·
              refine ⟨41316382001460514898222453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27544254667640343265481635 41316382001460514898222453)
              ·
                refine ⟨3873410812636923271708355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41316382001460514898222453 3873410812636923271708355)
                ·
                  refine ⟨5810116218955384907562533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873410812636923271708355 5810116218955384907562533)
                  ·
                    refine ⟨1089396791054134670167975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810116218955384907562533 1089396791054134670167975)
                    ·
                      rfl

theorem cell23_6364778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_6364778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364778 prefixEnd_6364778 := by exact prefixLift 6364778
  have htrace : WordTrace (prefixWord ++ tailWord_6364778) baseStart_6364778 baseEnd_6364778 := by
    simpa [prefixWord, tailWord_6364778, baseEnd_6364778] using wordTrace_append hprefix tailTrace_6364778
  have hstable : (prefixWord ++ tailWord_6364778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364778).length < 2 ^ (prefixWord ++ tailWord_6364778).sum := by decide
  have hdescent : baseEnd_6364778 < baseStart_6364778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364851 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 2, 4]
def baseStart_6364851 : Nat := 118140960795 + 6364851 * 2 ^ 59
def prefixEnd_6364851 : Nat := 4983230072969 + 3 ^ 40 * 6364851 * 2
def baseEnd_6364851 : Nat := 1089409285750060741630363

theorem tailTrace_6364851 : CollatzResearch.WordTrace tailWord_6364851 prefixEnd_6364851 1089409285750060741630363 := by
  unfold tailWord_6364851
  simp only [CollatzResearch.WordTrace]
  refine ⟨232145187464239331853030407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154763458309492887902020271 232145187464239331853030407)
  ·
    refine ⟨348217781196358997779545611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232145187464239331853030407 348217781196358997779545611)
    ·
      refine ⟨522326671794538496669318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348217781196358997779545611 522326671794538496669318417)
      ·
        refine ⟨391745003845903872501988813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522326671794538496669318417 391745003845903872501988813)
        ·
          refine ⟨146904376442213952188245805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391745003845903872501988813 146904376442213952188245805)
          ·
            refine ⟨55089141165830232070592177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146904376442213952188245805 55089141165830232070592177)
            ·
              refine ⟨41316855874372674052944133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55089141165830232070592177 41316855874372674052944133)
              ·
                refine ⟨7746910476444876384927025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41316855874372674052944133 7746910476444876384927025)
                ·
                  refine ⟨5810182857333657288695269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746910476444876384927025 5810182857333657288695269)
                  ·
                    refine ⟨1089409285750060741630363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810182857333657288695269 1089409285750060741630363)
                    ·
                      rfl

theorem cell23_6364851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 4].length) (baseStart_6364851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364851 prefixEnd_6364851 := by exact prefixLift 6364851
  have htrace : WordTrace (prefixWord ++ tailWord_6364851) baseStart_6364851 baseEnd_6364851 := by
    simpa [prefixWord, tailWord_6364851, baseEnd_6364851] using wordTrace_append hprefix tailTrace_6364851
  have hstable : (prefixWord ++ tailWord_6364851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364851).length < 2 ^ (prefixWord ++ tailWord_6364851).sum := by decide
  have hdescent : baseEnd_6364851 < baseStart_6364851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364861 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_6364861 : Nat := 118140960795 + 6364861 * 2 ^ 59
def prefixEnd_6364861 : Nat := 4983230072969 + 3 ^ 40 * 6364861 * 2
def baseEnd_6364861 : Nat := 3268232992056727185766043

theorem tailTrace_6364861 : CollatzResearch.WordTrace tailWord_6364861 prefixEnd_6364861 3268232992056727185766043 := by
  unfold tailWord_6364861
  simp only [CollatzResearch.WordTrace]
  refine ⟨232145552194203103560894437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154763701462802069040596291 232145552194203103560894437)
  ·
    refine ⟨43527291036413081917667707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232145552194203103560894437 43527291036413081917667707)
    ·
      refine ⟨65290936554619622876501561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43527291036413081917667707 65290936554619622876501561)
      ·
        refine ⟨48968202415964717157376171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65290936554619622876501561 48968202415964717157376171)
        ·
          refine ⟨73452303623947075736064257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48968202415964717157376171 73452303623947075736064257)
          ·
            refine ⟨55089227717960306802048193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73452303623947075736064257 55089227717960306802048193)
            ·
              refine ⟨41316920788470230101536145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55089227717960306802048193 41316920788470230101536145)
              ·
                refine ⟨30987690591352672576152109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41316920788470230101536145 30987690591352672576152109)
                ·
                  refine ⟨11620383971757252216057041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30987690591352672576152109 11620383971757252216057041)
                  ·
                    refine ⟨8715287978817939162042781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11620383971757252216057041 8715287978817939162042781)
                    ·
                      refine ⟨3268232992056727185766043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715287978817939162042781 3268232992056727185766043)
                      ·
                        rfl

theorem cell23_6364861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_6364861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364861 prefixEnd_6364861 := by exact prefixLift 6364861
  have htrace : WordTrace (prefixWord ++ tailWord_6364861) baseStart_6364861 baseEnd_6364861 := by
    simpa [prefixWord, tailWord_6364861, baseEnd_6364861] using wordTrace_append hprefix tailTrace_6364861
  have hstable : (prefixWord ++ tailWord_6364861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364861).length < 2 ^ (prefixWord ++ tailWord_6364861).sum := by decide
  have hdescent : baseEnd_6364861 < baseStart_6364861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364864 : List Nat := [2, 1, 1, 2, 4, 1, 4, 8]
def baseStart_6364864 : Nat := 118140960795 + 6364864 * 2 ^ 59
def prefixEnd_6364864 : Nat := 4983230072969 + 3 ^ 40 * 6364864 * 2
def baseEnd_6364864 : Nat := 121045723425877432371427

theorem tailTrace_6364864 : CollatzResearch.WordTrace tailWord_6364864 prefixEnd_6364864 121045723425877432371427 := by
  unfold tailWord_6364864
  simp only [CollatzResearch.WordTrace]
  refine ⟨116072830806596117536626823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154763774408794823382169097 116072830806596117536626823)
  ·
    refine ⟨174109246209894176304940235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116072830806596117536626823 174109246209894176304940235)
    ·
      refine ⟨261163869314841264457410353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174109246209894176304940235 261163869314841264457410353)
      ·
        refine ⟨195872901986130948343057765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261163869314841264457410353 195872901986130948343057765)
        ·
          refine ⟨36726169122399552814323331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195872901986130948343057765 36726169122399552814323331)
          ·
            refine ⟨55089253683599329221484997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36726169122399552814323331 55089253683599329221484997)
            ·
              refine ⟨10329235065674874229028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55089253683599329221484997 10329235065674874229028437)
              ·
                refine ⟨121045723425877432371427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10329235065674874229028437 121045723425877432371427)
                ·
                  rfl

theorem cell23_6364864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_6364864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364864 prefixEnd_6364864 := by exact prefixLift 6364864
  have htrace : WordTrace (prefixWord ++ tailWord_6364864) baseStart_6364864 baseEnd_6364864 := by
    simpa [prefixWord, tailWord_6364864, baseEnd_6364864] using wordTrace_append hprefix tailTrace_6364864
  have hstable : (prefixWord ++ tailWord_6364864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364864).length < 2 ^ (prefixWord ++ tailWord_6364864).sum := by decide
  have hdescent : baseEnd_6364864 < baseStart_6364864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364868 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6364868 : Nat := 118140960795 + 6364868 * 2 ^ 59
def prefixEnd_6364868 : Nat := 4983230072969 + 3 ^ 40 * 6364868 * 2
def baseEnd_6364868 : Nat := 1089412195473769552792837

theorem tailTrace_6364868 : CollatzResearch.WordTrace tailWord_6364868 prefixEnd_6364868 1089412195473769552792837 := by
  unfold tailWord_6364868
  simp only [CollatzResearch.WordTrace]
  refine ⟨116072903752588871878199629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154763871670118495837599505 116072903752588871878199629)
  ·
    refine ⟨43527338907220826954324861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116072903752588871878199629 43527338907220826954324861)
    ·
      refine ⟨16322752090207810107871823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43527338907220826954324861 16322752090207810107871823)
      ·
        refine ⟨24484128135311715161807735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16322752090207810107871823 24484128135311715161807735)
        ·
          refine ⟨36726192202967572742711603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24484128135311715161807735 36726192202967572742711603)
          ·
            refine ⟨55089288304451359114067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36726192202967572742711603 55089288304451359114067405)
            ·
              refine ⟨20658483114169259667775277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55089288304451359114067405 20658483114169259667775277)
              ·
                refine ⟨7746931167813472375415729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20658483114169259667775277 7746931167813472375415729)
                ·
                  refine ⟨5810198375860104281561797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746931167813472375415729 5810198375860104281561797)
                  ·
                    refine ⟨1089412195473769552792837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810198375860104281561797 1089412195473769552792837)
                    ·
                      rfl

theorem cell23_6364868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6364868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364868 prefixEnd_6364868 := by exact prefixLift 6364868
  have htrace : WordTrace (prefixWord ++ tailWord_6364868) baseStart_6364868 baseEnd_6364868 := by
    simpa [prefixWord, tailWord_6364868, baseEnd_6364868] using wordTrace_append hprefix tailTrace_6364868
  have hstable : (prefixWord ++ tailWord_6364868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364868).length < 2 ^ (prefixWord ++ tailWord_6364868).sum := by decide
  have hdescent : baseEnd_6364868 < baseStart_6364868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364892 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6364892 : Nat := 118140960795 + 6364892 * 2 ^ 59
def prefixEnd_6364892 : Nat := 4983230072969 + 3 ^ 40 * 6364892 * 2
def baseEnd_6364892 : Nat := 3268248909957016564478401

theorem tailTrace_6364892 : CollatzResearch.WordTrace tailWord_6364892 prefixEnd_6364892 3268248909957016564478401 := by
  unfold tailWord_6364892
  simp only [CollatzResearch.WordTrace]
  refine ⟨116073341428545397927636465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154764455238060530570181953 116073341428545397927636465)
  ·
    refine ⟨87055006071409048445727349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116073341428545397927636465 87055006071409048445727349)
    ·
      refine ⟨8161406819194598291786939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87055006071409048445727349 8161406819194598291786939)
      ·
        refine ⟨12242110228791897437680409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161406819194598291786939 12242110228791897437680409)
        ·
          refine ⟨9181582671593923078260307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12242110228791897437680409 9181582671593923078260307)
          ·
            refine ⟨13772374007390884617390461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181582671593923078260307 13772374007390884617390461)
            ·
              refine ⟨5164640252771581731521423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13772374007390884617390461 5164640252771581731521423)
              ·
                refine ⟨7746960379157372597282135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164640252771581731521423 7746960379157372597282135)
                ·
                  refine ⟨11620440568736058895923203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746960379157372597282135 11620440568736058895923203)
                  ·
                    refine ⟨17430660853104088343884805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11620440568736058895923203 17430660853104088343884805)
                    ·
                      refine ⟨3268248909957016564478401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17430660853104088343884805 3268248909957016564478401)
                      ·
                        rfl

theorem cell23_6364892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6364892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364892 prefixEnd_6364892 := by exact prefixLift 6364892
  have htrace : WordTrace (prefixWord ++ tailWord_6364892) baseStart_6364892 baseEnd_6364892 := by
    simpa [prefixWord, tailWord_6364892, baseEnd_6364892] using wordTrace_append hprefix tailTrace_6364892
  have hstable : (prefixWord ++ tailWord_6364892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364892).length < 2 ^ (prefixWord ++ tailWord_6364892).sum := by decide
  have hdescent : baseEnd_6364892 < baseStart_6364892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364908 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_6364908 : Nat := 118140960795 + 6364908 * 2 ^ 59
def prefixEnd_6364908 : Nat := 4983230072969 + 3 ^ 40 * 6364908 * 2
def baseEnd_6364908 : Nat := 3268257125647488501878327

theorem tailTrace_6364908 : CollatzResearch.WordTrace tailWord_6364908 prefixEnd_6364908 3268257125647488501878327 := by
  unfold tailWord_6364908
  simp only [CollatzResearch.WordTrace]
  refine ⟨116073633212516415293927689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154764844283355220391903585 116073633212516415293927689)
  ·
    refine ⟨87055224909387311470445767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116073633212516415293927689 87055224909387311470445767)
    ·
      refine ⟨130582837364080967205668651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87055224909387311470445767 130582837364080967205668651)
      ·
        refine ⟨195874256046121450808502977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130582837364080967205668651 195874256046121450808502977)
        ·
          refine ⟨146905692034591088106377233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195874256046121450808502977 146905692034591088106377233)
          ·
            refine ⟨110179269025943316079782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146905692034591088106377233 110179269025943316079782925)
            ·
              refine ⟨41317225884728743529918597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110179269025943316079782925 41317225884728743529918597)
              ·
                refine ⟨7746979853386639411859737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41317225884728743529918597 7746979853386639411859737)
                ·
                  refine ⟨5810234890039979558894803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746979853386639411859737 5810234890039979558894803)
                  ·
                    refine ⟨8715352335059969338342205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810234890039979558894803 8715352335059969338342205)
                    ·
                      refine ⟨3268257125647488501878327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715352335059969338342205 3268257125647488501878327)
                      ·
                        rfl

theorem cell23_6364908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_6364908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364908 prefixEnd_6364908 := by exact prefixLift 6364908
  have htrace : WordTrace (prefixWord ++ tailWord_6364908) baseStart_6364908 baseEnd_6364908 := by
    simpa [prefixWord, tailWord_6364908, baseEnd_6364908] using wordTrace_append hprefix tailTrace_6364908
  have hstable : (prefixWord ++ tailWord_6364908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364908).length < 2 ^ (prefixWord ++ tailWord_6364908).sum := by decide
  have hdescent : baseEnd_6364908 < baseStart_6364908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364909 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6364909 : Nat := 118140960795 + 6364909 * 2 ^ 59
def prefixEnd_6364909 : Nat := 4983230072969 + 3 ^ 40 * 6364909 * 2
def baseEnd_6364909 : Nat := 3268257639128142997965823

theorem tailTrace_6364909 : CollatzResearch.WordTrace tailWord_6364909 prefixEnd_6364909 3268257639128142997965823 := by
  unfold tailWord_6364909
  simp only [CollatzResearch.WordTrace]
  refine ⟨232147302898029207758641781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154764868598686138505761187 232147302898029207758641781)
  ·
    refine ⟨21763809646690238227372667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232147302898029207758641781 21763809646690238227372667)
    ·
      refine ⟨32645714470035357341059001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21763809646690238227372667 32645714470035357341059001)
      ·
        refine ⟨24484285852526518005794251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32645714470035357341059001 24484285852526518005794251)
        ·
          refine ⟨36726428778789777008691377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24484285852526518005794251 36726428778789777008691377)
          ·
            refine ⟨27544821584092332756518533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36726428778789777008691377 27544821584092332756518533)
            ·
              refine ⟨5164654047017312391847225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27544821584092332756518533 5164654047017312391847225)
              ·
                refine ⟨3873490535262984293885419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164654047017312391847225 3873490535262984293885419)
                ·
                  refine ⟨5810235802894476440828129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873490535262984293885419 5810235802894476440828129)
                  ·
                    refine ⟨4357676852170857330621097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810235802894476440828129 4357676852170857330621097)
                    ·
                      refine ⟨3268257639128142997965823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357676852170857330621097 3268257639128142997965823)
                      ·
                        rfl

theorem cell23_6364909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6364909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364909 prefixEnd_6364909 := by exact prefixLift 6364909
  have htrace : WordTrace (prefixWord ++ tailWord_6364909) baseStart_6364909 baseEnd_6364909 := by
    simpa [prefixWord, tailWord_6364909, baseEnd_6364909] using wordTrace_append hprefix tailTrace_6364909
  have hstable : (prefixWord ++ tailWord_6364909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364909).length < 2 ^ (prefixWord ++ tailWord_6364909).sum := by decide
  have hdescent : baseEnd_6364909 < baseStart_6364909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364961 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6364961 : Nat := 118140960795 + 6364961 * 2 ^ 59
def prefixEnd_6364961 : Nat := 4983230072969 + 3 ^ 40 * 6364961 * 2
def baseEnd_6364961 : Nat := 3268284340122176794515583

theorem tailTrace_6364961 : CollatzResearch.WordTrace tailWord_6364961 prefixEnd_6364961 3268284340122176794515583 := by
  unfold tailWord_6364961
  simp only [CollatzResearch.WordTrace]
  refine ⟨232149199493840820639534737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154766132995893880426356491 232149199493840820639534737)
  ·
    refine ⟨174111899620380615479651053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232149199493840820639534737 174111899620380615479651053)
    ·
      refine ⟨65291962357642730804869145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174111899620380615479651053 65291962357642730804869145)
      ·
        refine ⟨48968971768232048103651859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65291962357642730804869145 48968971768232048103651859)
        ·
          refine ⟨73453457652348072155477789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48968971768232048103651859 73453457652348072155477789)
          ·
            refine ⟨27545046619630527058304171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73453457652348072155477789 27545046619630527058304171)
            ·
              refine ⟨41317569929445790587456257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27545046619630527058304171 41317569929445790587456257)
              ·
                refine ⟨30988177447084342940592193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41317569929445790587456257 30988177447084342940592193)
                ·
                  refine ⟨23241133085313257205444145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30988177447084342940592193 23241133085313257205444145)
                  ·
                    refine ⟨17430849813984942904083109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23241133085313257205444145 17430849813984942904083109)
                    ·
                      refine ⟨3268284340122176794515583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17430849813984942904083109 3268284340122176794515583)
                      ·
                        rfl

theorem cell23_6364961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6364961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364961 prefixEnd_6364961 := by exact prefixLift 6364961
  have htrace : WordTrace (prefixWord ++ tailWord_6364961) baseStart_6364961 baseEnd_6364961 := by
    simpa [prefixWord, tailWord_6364961, baseEnd_6364961] using wordTrace_append hprefix tailTrace_6364961
  have hstable : (prefixWord ++ tailWord_6364961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364961).length < 2 ^ (prefixWord ++ tailWord_6364961).sum := by decide
  have hdescent : baseEnd_6364961 < baseStart_6364961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364965 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_6364965 : Nat := 118140960795 + 6364965 * 2 ^ 59
def prefixEnd_6364965 : Nat := 4983230072969 + 3 ^ 40 * 6364965 * 2
def baseEnd_6364965 : Nat := 3268286394044794778865565

theorem tailTrace_6364965 : CollatzResearch.WordTrace tailWord_6364965 prefixEnd_6364965 3268286394044794778865565 := by
  unfold tailWord_6364965
  simp only [CollatzResearch.WordTrace]
  refine ⟨232149345385826329322680349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154766230257217552881786899 232149345385826329322680349)
  ·
    refine ⟨87056004519684873496005131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232149345385826329322680349 87056004519684873496005131)
    ·
      refine ⟨130584006779527310244007697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87056004519684873496005131 130584006779527310244007697)
      ·
        refine ⟨97938005084645482683005773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130584006779527310244007697 97938005084645482683005773)
        ·
          refine ⟨36726751906742056006127165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97938005084645482683005773 36726751906742056006127165)
          ·
            refine ⟨13772531965028271002297687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36726751906742056006127165 13772531965028271002297687)
            ·
              refine ⟨20658797947542406503446531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772531965028271002297687 20658797947542406503446531)
              ·
                refine ⟨30988196921313609755169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20658797947542406503446531 30988196921313609755169797)
                ·
                  refine ⟨5810286922746301829094337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30988196921313609755169797 5810286922746301829094337)
                  ·
                    refine ⟨4357715192059726371820753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810286922746301829094337 4357715192059726371820753)
                    ·
                      refine ⟨3268286394044794778865565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357715192059726371820753 3268286394044794778865565)
                      ·
                        rfl

theorem cell23_6364965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_6364965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364965 prefixEnd_6364965 := by exact prefixLift 6364965
  have htrace : WordTrace (prefixWord ++ tailWord_6364965) baseStart_6364965 baseEnd_6364965 := by
    simpa [prefixWord, tailWord_6364965, baseEnd_6364965] using wordTrace_append hprefix tailTrace_6364965
  have hstable : (prefixWord ++ tailWord_6364965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364965).length < 2 ^ (prefixWord ++ tailWord_6364965).sum := by decide
  have hdescent : baseEnd_6364965 < baseStart_6364965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364982 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6364982 : Nat := 118140960795 + 6364982 * 2 ^ 59
def prefixEnd_6364982 : Nat := 4983230072969 + 3 ^ 40 * 6364982 * 2
def baseEnd_6364982 : Nat := 3268295123215921212352987

theorem tailTrace_6364982 : CollatzResearch.WordTrace tailWord_6364982 prefixEnd_6364982 3268295123215921212352987 := by
  unfold tailWord_6364982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14509372839172796326628075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154766643617843160817366133 14509372839172796326628075)
  ·
    refine ⟨21764059258759194489942113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14509372839172796326628075 21764059258759194489942113)
    ·
      refine ⟨16323044444069395867456585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21764059258759194489942113 16323044444069395867456585)
      ·
        refine ⟨12242283333052046900592439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16323044444069395867456585 12242283333052046900592439)
        ·
          refine ⟨18363424999578070350888659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12242283333052046900592439 18363424999578070350888659)
          ·
            refine ⟨27545137499367105526332989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363424999578070350888659 27545137499367105526332989)
            ·
              refine ⟨10329426562262664572374871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27545137499367105526332989 10329426562262664572374871)
              ·
                refine ⟨15494139843393996858562307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329426562262664572374871 15494139843393996858562307)
                ·
                  refine ⟨23241209765090995287843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15494139843393996858562307 23241209765090995287843461)
                  ·
                    refine ⟨4357726830954561616470649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23241209765090995287843461 4357726830954561616470649)
                    ·
                      refine ⟨3268295123215921212352987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357726830954561616470649 3268295123215921212352987)
                      ·
                        rfl

theorem cell23_6364982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6364982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364982 prefixEnd_6364982 := by exact prefixLift 6364982
  have htrace : WordTrace (prefixWord ++ tailWord_6364982) baseStart_6364982 baseEnd_6364982 := by
    simpa [prefixWord, tailWord_6364982, baseEnd_6364982] using wordTrace_append hprefix tailTrace_6364982
  have hstable : (prefixWord ++ tailWord_6364982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364982).length < 2 ^ (prefixWord ++ tailWord_6364982).sum := by decide
  have hdescent : baseEnd_6364982 < baseStart_6364982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365001 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_6365001 : Nat := 118140960795 + 6365001 * 2 ^ 59
def prefixEnd_6365001 : Nat := 4983230072969 + 3 ^ 40 * 6365001 * 2
def baseEnd_6365001 : Nat := 1089434959782785546005133

theorem tailTrace_6365001 : CollatzResearch.WordTrace tailWord_6365001 prefixEnd_6365001 1089434959782785546005133 := by
  unfold tailWord_6365001
  simp only [CollatzResearch.WordTrace]
  refine ⟨232150658413695907470990857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154767105609130604980660571 232150658413695907470990857)
  ·
    refine ⟨174112993810271930603243143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232150658413695907470990857 174112993810271930603243143)
    ·
      refine ⟨261169490715407895904864715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174112993810271930603243143 261169490715407895904864715)
      ·
        refine ⟨391754236073111843857297073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261169490715407895904864715 391754236073111843857297073)
        ·
          refine ⟨293815677054833882892972805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391754236073111843857297073 293815677054833882892972805)
          ·
            refine ⟨55090439447781353042432401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293815677054833882892972805 55090439447781353042432401)
            ·
              refine ⟨41317829585836014781824301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55090439447781353042432401 41317829585836014781824301)
              ·
                refine ⟨15494186094688505543184113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41317829585836014781824301 15494186094688505543184113)
                ·
                  refine ⟨11620639571016379157388085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15494186094688505543184113 11620639571016379157388085)
                  ·
                    refine ⟨1089434959782785546005133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11620639571016379157388085 1089434959782785546005133)
                    ·
                      rfl

theorem cell23_6365001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_6365001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365001 prefixEnd_6365001 := by exact prefixLift 6365001
  have htrace : WordTrace (prefixWord ++ tailWord_6365001) baseStart_6365001 baseEnd_6365001 := by
    simpa [prefixWord, tailWord_6365001, baseEnd_6365001] using wordTrace_append hprefix tailTrace_6365001
  have hstable : (prefixWord ++ tailWord_6365001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365001).length < 2 ^ (prefixWord ++ tailWord_6365001).sum := by decide
  have hdescent : baseEnd_6365001 < baseStart_6365001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365028 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_6365028 : Nat := 118140960795 + 6365028 * 2 ^ 59
def prefixEnd_6365028 : Nat := 4983230072969 + 3 ^ 40 * 6365028 * 2
def baseEnd_6365028 : Nat := 3268318743326028032377775

theorem tailTrace_6365028 : CollatzResearch.WordTrace tailWord_6365028 prefixEnd_6365028 3268318743326028032377775 := by
  unfold tailWord_6365028
  simp only [CollatzResearch.WordTrace]
  refine ⟨116075821592299045541111869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154767762123065394054815825 116075821592299045541111869)
  ·
    refine ⟨43528433097112142077916951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116075821592299045541111869 43528433097112142077916951)
    ·
      refine ⟨65292649645668213116875427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43528433097112142077916951 65292649645668213116875427)
      ·
        refine ⟨97938974468502319675313141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65292649645668213116875427 97938974468502319675313141)
        ·
          refine ⟨9181778856422092469560607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97938974468502319675313141 9181778856422092469560607)
          ·
            refine ⟨13772668284633138704340911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181778856422092469560607 13772668284633138704340911)
            ·
              refine ⟨20659002426949708056511367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772668284633138704340911 20659002426949708056511367)
              ·
                refine ⟨30988503640424562084767051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20659002426949708056511367 30988503640424562084767051)
                ·
                  refine ⟨46482755460636843127150577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30988503640424562084767051 46482755460636843127150577)
                  ·
                    refine ⟨34862066595477632345362933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46482755460636843127150577 34862066595477632345362933)
                    ·
                      refine ⟨3268318743326028032377775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34862066595477632345362933 3268318743326028032377775)
                      ·
                        rfl

theorem cell23_6365028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_6365028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365028 prefixEnd_6365028 := by exact prefixLift 6365028
  have htrace : WordTrace (prefixWord ++ tailWord_6365028) baseStart_6365028 baseEnd_6365028 := by
    simpa [prefixWord, tailWord_6365028, baseEnd_6365028] using wordTrace_append hprefix tailTrace_6365028
  have hstable : (prefixWord ++ tailWord_6365028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365028).length < 2 ^ (prefixWord ++ tailWord_6365028).sum := by decide
  have hdescent : baseEnd_6365028 < baseStart_6365028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365065 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 1, 4]
def baseStart_6365065 : Nat := 118140960795 + 6365065 * 2 ^ 59
def prefixEnd_6365065 : Nat := 4983230072969 + 3 ^ 40 * 6365065 * 2
def baseEnd_6365065 : Nat := 1089445914036748129205035

theorem tailTrace_6365065 : CollatzResearch.WordTrace tailWord_6365065 prefixEnd_6365065 1089445914036748129205035 := by
  unfold tailWord_6365065
  simp only [CollatzResearch.WordTrace]
  refine ⟨232152992685464046401320649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154768661790309364267547099 232152992685464046401320649)
  ·
    refine ⟨174114744514098034800990487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232152992685464046401320649 174114744514098034800990487)
    ·
      refine ⟨261172116771147052201485731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174114744514098034800990487 261172116771147052201485731)
      ·
        refine ⟨391758175156720578302228597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261172116771147052201485731 391758175156720578302228597)
        ·
          refine ⟨36727328920942554215833931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391758175156720578302228597 36727328920942554215833931)
          ·
            refine ⟨55090993381413831323750897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36727328920942554215833931 55090993381413831323750897)
            ·
              refine ⟨41318245036060373492813173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55090993381413831323750897 41318245036060373492813173)
              ·
                refine ⟨3873585472130660014951235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41318245036060373492813173 3873585472130660014951235)
                ·
                  refine ⟨5810378208195990022426853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873585472130660014951235 5810378208195990022426853)
                  ·
                    refine ⟨1089445914036748129205035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810378208195990022426853 1089445914036748129205035)
                    ·
                      rfl

theorem cell23_6365065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_6365065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365065 prefixEnd_6365065 := by exact prefixLift 6365065
  have htrace : WordTrace (prefixWord ++ tailWord_6365065) baseStart_6365065 baseEnd_6365065 := by
    simpa [prefixWord, tailWord_6365065, baseEnd_6365065] using wordTrace_append hprefix tailTrace_6365065
  have hstable : (prefixWord ++ tailWord_6365065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365065).length < 2 ^ (prefixWord ++ tailWord_6365065).sum := by decide
  have hdescent : baseEnd_6365065 < baseStart_6365065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_6365071 : Nat := 118140960795 + 6365071 * 2 ^ 59
def prefixEnd_6365071 : Nat := 4983230072969 + 3 ^ 40 * 6365071 * 2
def baseEnd_6365071 : Nat := 3268340822994171364140077

theorem tailTrace_6365071 : CollatzResearch.WordTrace tailWord_6365071 prefixEnd_6365071 3268340822994171364140077 := by
  unfold tailWord_6365071
  simp only [CollatzResearch.WordTrace]
  refine ⟨232153211523442309426039067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154768807682294872950692711 232153211523442309426039067)
  ·
    refine ⟨348229817285163464139058601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232153211523442309426039067 348229817285163464139058601)
    ·
      refine ⟨261172362963872598104293951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348229817285163464139058601 261172362963872598104293951)
      ·
        refine ⟨391758544445808897156440927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261172362963872598104293951 391758544445808897156440927)
        ·
          refine ⟨587637816668713345734661391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391758544445808897156440927 587637816668713345734661391)
          ·
            refine ⟨881456725003070018601992087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587637816668713345734661391 881456725003070018601992087)
            ·
              refine ⟨1322185087504605027902988131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881456725003070018601992087 1322185087504605027902988131)
              ·
                refine ⟨1983277631256907541854482197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322185087504605027902988131 1983277631256907541854482197)
                ·
                  refine ⟨92966138965167541024428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1983277631256907541854482197 92966138965167541024428853)
                  ·
                    refine ⟨8715575527984456971040205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92966138965167541024428853 8715575527984456971040205)
                    ·
                      refine ⟨3268340822994171364140077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715575527984456971040205 3268340822994171364140077)
                      ·
                        rfl

theorem cell23_6365071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_6365071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365071 prefixEnd_6365071 := by exact prefixLift 6365071
  have htrace : WordTrace (prefixWord ++ tailWord_6365071) baseStart_6365071 baseEnd_6365071 := by
    simpa [prefixWord, tailWord_6365071, baseEnd_6365071] using wordTrace_append hprefix tailTrace_6365071
  have hstable : (prefixWord ++ tailWord_6365071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365071).length < 2 ^ (prefixWord ++ tailWord_6365071).sum := by decide
  have hdescent : baseEnd_6365071 < baseStart_6365071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365082 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_6365082 : Nat := 118140960795 + 6365082 * 2 ^ 59
def prefixEnd_6365082 : Nat := 4983230072969 + 3 ^ 40 * 6365082 * 2
def baseEnd_6365082 : Nat := 1089448823760456940367509

theorem tailTrace_6365082 : CollatzResearch.WordTrace tailWord_6365082 prefixEnd_6365082 1089448823760456940367509 := by
  unfold tailWord_6365082
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038403181600614576172375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154769075150934972203126333 58038403181600614576172375)
  ·
    refine ⟨87057604772400921864258563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58038403181600614576172375 87057604772400921864258563)
    ·
      refine ⟨130586407158601382796387845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87057604772400921864258563 130586407158601382796387845)
      ·
        refine ⟨24484951342237759274322721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130586407158601382796387845 24484951342237759274322721)
        ·
          refine ⟨18363713506678319455742041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24484951342237759274322721 18363713506678319455742041)
          ·
            refine ⟨13772785130008739591806531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18363713506678319455742041 13772785130008739591806531)
            ·
              refine ⟨20659177695013109387709797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772785130008739591806531 20659177695013109387709797)
              ·
                refine ⟨3873595817814958010195587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20659177695013109387709797 3873595817814958010195587)
                ·
                  refine ⟨5810393726722437015293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873595817814958010195587 5810393726722437015293381)
                  ·
                    refine ⟨1089448823760456940367509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810393726722437015293381 1089448823760456940367509)
                    ·
                      rfl

theorem cell23_6365082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_6365082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365082 prefixEnd_6365082 := by exact prefixLift 6365082
  have htrace : WordTrace (prefixWord ++ tailWord_6365082) baseStart_6365082 baseEnd_6365082 := by
    simpa [prefixWord, tailWord_6365082, baseEnd_6365082] using wordTrace_append hprefix tailTrace_6365082
  have hstable : (prefixWord ++ tailWord_6365082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365082).length < 2 ^ (prefixWord ++ tailWord_6365082).sum := by decide
  have hdescent : baseEnd_6365082 < baseStart_6365082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365105 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6365105 : Nat := 118140960795 + 6365105 * 2 ^ 59
def prefixEnd_6365105 : Nat := 4983230072969 + 3 ^ 40 * 6365105 * 2
def baseEnd_6365105 : Nat := 3268358281336424231114921

theorem tailTrace_6365105 : CollatzResearch.WordTrace tailWord_6365105 prefixEnd_6365105 3268358281336424231114921 := by
  unfold tailWord_6365105
  simp only [CollatzResearch.WordTrace]
  refine ⟨232154451605319133232776769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154769634403546088821851179 232154451605319133232776769)
  ·
    refine ⟨174115838703989349924582577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232154451605319133232776769 174115838703989349924582577)
    ·
      refine ⟨130586879027992012443436933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174115838703989349924582577 130586879027992012443436933)
      ·
        refine ⟨24485039817748502333144425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130586879027992012443436933 24485039817748502333144425)
        ·
          refine ⟨18363779863311376749858319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24485039817748502333144425 18363779863311376749858319)
          ·
            refine ⟨27545669794967065124787479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363779863311376749858319 27545669794967065124787479)
            ·
              refine ⟨41318504692450597687181219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27545669794967065124787479 41318504692450597687181219)
              ·
                refine ⟨61977757038675896530771829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41318504692450597687181219 61977757038675896530771829)
                ·
                  refine ⟨5810414722375865299759859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61977757038675896530771829 5810414722375865299759859)
                  ·
                    refine ⟨8715622083563797949639789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810414722375865299759859 8715622083563797949639789)
                    ·
                      refine ⟨3268358281336424231114921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715622083563797949639789 3268358281336424231114921)
                      ·
                        rfl

theorem cell23_6365105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6365105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365105 prefixEnd_6365105 := by exact prefixLift 6365105
  have htrace : WordTrace (prefixWord ++ tailWord_6365105) baseStart_6365105 baseEnd_6365105 := by
    simpa [prefixWord, tailWord_6365105, baseEnd_6365105] using wordTrace_append hprefix tailTrace_6365105
  have hstable : (prefixWord ++ tailWord_6365105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365105).length < 2 ^ (prefixWord ++ tailWord_6365105).sum := by decide
  have hdescent : baseEnd_6365105 < baseStart_6365105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365155 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 6]
def baseStart_6365155 : Nat := 118140960795 + 6365155 * 2 ^ 59
def prefixEnd_6365155 : Nat := 4983230072969 + 3 ^ 40 * 6365155 * 2
def baseEnd_6365155 : Nat := 1089461318456383011829897

theorem tailTrace_6365155 : CollatzResearch.WordTrace tailWord_6365155 prefixEnd_6365155 1089461318456383011829897 := by
  unfold tailWord_6365155
  simp only [CollatzResearch.WordTrace]
  refine ⟨232156275255137991772096919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154770850170091994514731279 232156275255137991772096919)
  ·
    refine ⟨348234412882706987658145379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232156275255137991772096919 348234412882706987658145379)
    ·
      refine ⟨522351619324060481487218069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348234412882706987658145379 522351619324060481487218069)
      ·
        refine ⟨24485232155815335069713347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 522351619324060481487218069 24485232155815335069713347)
        ·
          refine ⟨36727848233723002604570021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24485232155815335069713347 36727848233723002604570021)
          ·
            refine ⟨6886471543823062988356879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36727848233723002604570021 6886471543823062988356879)
            ·
              refine ⟨10329707315734594482535319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886471543823062988356879 10329707315734594482535319)
              ·
                refine ⟨15494560973601891723802979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329707315734594482535319 15494560973601891723802979)
                ·
                  refine ⟨23241841460402837585704469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15494560973601891723802979 23241841460402837585704469)
                  ·
                    refine ⟨1089461318456383011829897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23241841460402837585704469 1089461318456383011829897)
                    ·
                      rfl

theorem cell23_6365155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 6].length) (baseStart_6365155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365155 prefixEnd_6365155 := by exact prefixLift 6365155
  have htrace : WordTrace (prefixWord ++ tailWord_6365155) baseStart_6365155 baseEnd_6365155 := by
    simpa [prefixWord, tailWord_6365155, baseEnd_6365155] using wordTrace_append hprefix tailTrace_6365155
  have hstable : (prefixWord ++ tailWord_6365155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365155).length < 2 ^ (prefixWord ++ tailWord_6365155).sum := by decide
  have hdescent : baseEnd_6365155 < baseStart_6365155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365162 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_6365162 : Nat := 118140960795 + 6365162 * 2 ^ 59
def prefixEnd_6365162 : Nat := 4983230072969 + 3 ^ 40 * 6365162 * 2
def baseEnd_6365162 : Nat := 3268387549733730508102159

theorem tailTrace_6365162 : CollatzResearch.WordTrace tailWord_6365162 prefixEnd_6365162 3268387549733730508102159 := by
  unfold tailWord_6365162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58039132641528157991900435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154771020377408421311734493 58039132641528157991900435)
  ·
    refine ⟨87058698962292236987850653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58039132641528157991900435 87058698962292236987850653)
    ·
      refine ⟨32647012110859588870443995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87058698962292236987850653 32647012110859588870443995)
      ·
        refine ⟨48970518166289383305665993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32647012110859588870443995 48970518166289383305665993)
        ·
          refine ⟨36727888624717037479249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48970518166289383305665993 36727888624717037479249495)
          ·
            refine ⟨55091832937075556218874243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36727888624717037479249495 55091832937075556218874243)
            ·
              refine ⟨82637749405613334328311365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55091832937075556218874243 82637749405613334328311365)
              ·
                refine ⟨15494578013552500186558381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82637749405613334328311365 15494578013552500186558381)
                ·
                  refine ⟨5810466755082187569959393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15494578013552500186558381 5810466755082187569959393)
                  ·
                    refine ⟨4357850066311640677469545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810466755082187569959393 4357850066311640677469545)
                    ·
                      refine ⟨3268387549733730508102159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357850066311640677469545 3268387549733730508102159)
                      ·
                        rfl

theorem cell23_6365162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_6365162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365162 prefixEnd_6365162 := by exact prefixLift 6365162
  have htrace : WordTrace (prefixWord ++ tailWord_6365162) baseStart_6365162 baseEnd_6365162 := by
    simpa [prefixWord, tailWord_6365162, baseEnd_6365162] using wordTrace_append hprefix tailTrace_6365162
  have hstable : (prefixWord ++ tailWord_6365162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365162).length < 2 ^ (prefixWord ++ tailWord_6365162).sum := by decide
  have hdescent : baseEnd_6365162 < baseStart_6365162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365168 : List Nat := [2, 1, 1, 1, 3, 2, 6, 7]
def baseStart_6365168 : Nat := 118140960795 + 6365168 * 2 ^ 59
def prefixEnd_6365168 : Nat := 4983230072969 + 3 ^ 40 * 6365168 * 2
def baseEnd_6365168 : Nat := 121051504837691017949153

theorem tailTrace_6365168 : CollatzResearch.WordTrace tailWord_6365168 prefixEnd_6365168 121051504837691017949153 := by
  unfold tailWord_6365168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116078374702045447496160079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154771166269393929994880105 116078374702045447496160079)
  ·
    refine ⟨174117562053068171244240119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116078374702045447496160079 174117562053068171244240119)
    ·
      refine ⟨261176343079602256866360179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174117562053068171244240119 261176343079602256866360179)
      ·
        refine ⟨391764514619403385299540269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261176343079602256866360179 391764514619403385299540269)
        ·
          refine ⟨146911692982276269487327601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391764514619403385299540269 146911692982276269487327601)
          ·
            refine ⟨110183769736707202115495701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146911692982276269487327601 110183769736707202115495701)
            ·
              refine ⟨5164864206408150099163861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110183769736707202115495701 5164864206408150099163861)
              ·
                refine ⟨121051504837691017949153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5164864206408150099163861 121051504837691017949153)
                ·
                  rfl

theorem cell23_6365168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 7].length) (baseStart_6365168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365168 prefixEnd_6365168 := by exact prefixLift 6365168
  have htrace : WordTrace (prefixWord ++ tailWord_6365168) baseStart_6365168 baseEnd_6365168 := by
    simpa [prefixWord, tailWord_6365168, baseEnd_6365168] using wordTrace_append hprefix tailTrace_6365168
  have hstable : (prefixWord ++ tailWord_6365168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365168).length < 2 ^ (prefixWord ++ tailWord_6365168).sum := by decide
  have hdescent : baseEnd_6365168 < baseStart_6365168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_6365171 : Nat := 118140960795 + 6365171 * 2 ^ 59
def prefixEnd_6365171 : Nat := 4983230072969 + 3 ^ 40 * 6365171 * 2
def baseEnd_6365171 : Nat := 3268392171059620972889617

theorem tailTrace_6365171 : CollatzResearch.WordTrace tailWord_6365171 prefixEnd_6365171 3268392171059620972889617 := by
  unfold tailWord_6365171
  simp only [CollatzResearch.WordTrace]
  refine ⟨232156858823080026504679367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154771239215386684336452911 232156858823080026504679367)
  ·
    refine ⟨348235288234620039757019051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232156858823080026504679367 348235288234620039757019051)
    ·
      refine ⟨522352932351930059635528577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348235288234620039757019051 522352932351930059635528577)
      ·
        refine ⟨391764699263947544726646433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522352932351930059635528577 391764699263947544726646433)
        ·
          refine ⟨293823524447960658544984825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391764699263947544726646433 293823524447960658544984825)
          ·
            refine ⟨220367643335970493908738619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293823524447960658544984825 220367643335970493908738619)
            ·
              refine ⟨330551465003955740863107929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220367643335970493908738619 330551465003955740863107929)
              ·
                refine ⟨247913598752966805647330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330551465003955740863107929 247913598752966805647330947)
                ·
                  refine ⟨371870398129450208470996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247913598752966805647330947 371870398129450208470996421)
                  ·
                    refine ⟨69725699649271914088311829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371870398129450208470996421 69725699649271914088311829)
                    ·
                      refine ⟨3268392171059620972889617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69725699649271914088311829 3268392171059620972889617)
                      ·
                        rfl

theorem cell23_6365171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_6365171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365171 prefixEnd_6365171 := by exact prefixLift 6365171
  have htrace : WordTrace (prefixWord ++ tailWord_6365171) baseStart_6365171 baseEnd_6365171 := by
    simpa [prefixWord, tailWord_6365171, baseEnd_6365171] using wordTrace_append hprefix tailTrace_6365171
  have hstable : (prefixWord ++ tailWord_6365171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365171).length < 2 ^ (prefixWord ++ tailWord_6365171).sum := by decide
  have hdescent : baseEnd_6365171 < baseStart_6365171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365179 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 1, 2, 2]
def baseStart_6365179 : Nat := 118140960795 + 6365179 * 2 ^ 59
def prefixEnd_6365179 : Nat := 4983230072969 + 3 ^ 40 * 6365179 * 2
def baseEnd_6365179 : Nat := 3268396278904856941589581

theorem tailTrace_6365179 : CollatzResearch.WordTrace tailWord_6365179 prefixEnd_6365179 3268396278904856941589581 := by
  unfold tailWord_6365179
  simp only [CollatzResearch.WordTrace]
  refine ⟨232157150607051043870970591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154771433738034029247313727 232157150607051043870970591)
  ·
    refine ⟨348235725910576565806455887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232157150607051043870970591 348235725910576565806455887)
    ·
      refine ⟨522353588865864848709683831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348235725910576565806455887 522353588865864848709683831)
      ·
        refine ⟨783530383298797273064525747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522353588865864848709683831 783530383298797273064525747)
        ·
          refine ⟨1175295574948195909596788621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783530383298797273064525747 1175295574948195909596788621)
          ·
            refine ⟨440735840605573466098795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175295574948195909596788621 440735840605573466098795733)
            ·
              refine ⟨10329746264193128111690525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440735840605573466098795733 10329746264193128111690525)
              ·
                refine ⟨3873654849072423041883947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10329746264193128111690525 3873654849072423041883947)
                ·
                  refine ⟨5810482273608634562825921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873654849072423041883947 5810482273608634562825921)
                  ·
                    refine ⟨4357861705206475922119441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810482273608634562825921 4357861705206475922119441)
                    ·
                      refine ⟨3268396278904856941589581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357861705206475922119441 3268396278904856941589581)
                      ·
                        rfl

theorem cell23_6365179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 2, 2].length) (baseStart_6365179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365179 prefixEnd_6365179 := by exact prefixLift 6365179
  have htrace : WordTrace (prefixWord ++ tailWord_6365179) baseStart_6365179 baseEnd_6365179 := by
    simpa [prefixWord, tailWord_6365179, baseEnd_6365179] using wordTrace_append hprefix tailTrace_6365179
  have hstable : (prefixWord ++ tailWord_6365179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365179).length < 2 ^ (prefixWord ++ tailWord_6365179).sum := by decide
  have hdescent : baseEnd_6365179 < baseStart_6365179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365182 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6365182 : Nat := 118140960795 + 6365182 * 2 ^ 59
def prefixEnd_6365182 : Nat := 4983230072969 + 3 ^ 40 * 6365182 * 2
def baseEnd_6365182 : Nat := 3268397819346820429852067

theorem tailTrace_6365182 : CollatzResearch.WordTrace tailWord_6365182 prefixEnd_6365182 3268397819346820429852067 := by
  unfold tailWord_6365182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019657503255021922916225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154771506684026783588886533 29019657503255021922916225)
  ·
    refine ⟨21764743127441266442187169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29019657503255021922916225 21764743127441266442187169)
    ·
      refine ⟨16323557345580949831640377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21764743127441266442187169 16323557345580949831640377)
      ·
        refine ⟨12242668009185712373730283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16323557345580949831640377 12242668009185712373730283)
        ·
          refine ⟨18364002013778568560595425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12242668009185712373730283 18364002013778568560595425)
          ·
            refine ⟨13773001510333926420446569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18364002013778568560595425 13773001510333926420446569)
            ·
              refine ⟨10329751132750444815334927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773001510333926420446569 10329751132750444815334927)
              ·
                refine ⟨15494626699125667223002391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329751132750444815334927 15494626699125667223002391)
                ·
                  refine ⟨23241940048688500834503587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15494626699125667223002391 23241940048688500834503587)
                  ·
                    refine ⟨34862910073032751251755381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23241940048688500834503587 34862910073032751251755381)
                    ·
                      refine ⟨3268397819346820429852067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34862910073032751251755381 3268397819346820429852067)
                      ·
                        rfl

theorem cell23_6365182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6365182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365182 prefixEnd_6365182 := by exact prefixLift 6365182
  have htrace : WordTrace (prefixWord ++ tailWord_6365182) baseStart_6365182 baseEnd_6365182 := by
    simpa [prefixWord, tailWord_6365182, baseEnd_6365182] using wordTrace_append hprefix tailTrace_6365182
  have hstable : (prefixWord ++ tailWord_6365182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365182).length < 2 ^ (prefixWord ++ tailWord_6365182).sum := by decide
  have hdescent : baseEnd_6365182 < baseStart_6365182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365190 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6365190 : Nat := 118140960795 + 6365190 * 2 ^ 59
def prefixEnd_6365190 : Nat := 4983230072969 + 3 ^ 40 * 6365190 * 2
def baseEnd_6365190 : Nat := 3268401927192056398552031

theorem tailTrace_6365190 : CollatzResearch.WordTrace tailWord_6365190 prefixEnd_6365190 3268401927192056398552031 := by
  unfold tailWord_6365190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254923494062849773425657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154771701206674128499747349 7254923494062849773425657)
  ·
    refine ⟨5441192620547137330069243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7254923494062849773425657 5441192620547137330069243)
    ·
      refine ⟨8161788930820705995103865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441192620547137330069243 8161788930820705995103865)
      ·
        refine ⟨6121341698115529496327899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8161788930820705995103865 6121341698115529496327899)
        ·
          refine ⟨9182012547173294244491849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121341698115529496327899 9182012547173294244491849)
          ·
            refine ⟨6886509410379970683368887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9182012547173294244491849 6886509410379970683368887)
            ·
              refine ⟨10329764115569956025053331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886509410379970683368887 10329764115569956025053331)
              ·
                refine ⟨15494646173354934037579997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10329764115569956025053331 15494646173354934037579997)
                ·
                  refine ⟨5810492315008100264092499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15494646173354934037579997 5810492315008100264092499)
                  ·
                    refine ⟨8715738472512150396138749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810492315008100264092499 8715738472512150396138749)
                    ·
                      refine ⟨3268401927192056398552031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715738472512150396138749 3268401927192056398552031)
                      ·
                        rfl

theorem cell23_6365190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6365190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365190 prefixEnd_6365190 := by exact prefixLift 6365190
  have htrace : WordTrace (prefixWord ++ tailWord_6365190) baseStart_6365190 baseEnd_6365190 := by
    simpa [prefixWord, tailWord_6365190, baseEnd_6365190] using wordTrace_append hprefix tailTrace_6365190
  have hstable : (prefixWord ++ tailWord_6365190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365190).length < 2 ^ (prefixWord ++ tailWord_6365190).sum := by decide
  have hdescent : baseEnd_6365190 < baseStart_6365190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365195 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 3]
def baseStart_6365195 : Nat := 118140960795 + 6365195 * 2 ^ 59
def prefixEnd_6365195 : Nat := 4983230072969 + 3 ^ 40 * 6365195 * 2
def baseEnd_6365195 : Nat := 3268404494595328878989507

theorem tailTrace_6365195 : CollatzResearch.WordTrace tailWord_6365195 prefixEnd_6365195 3268404494595328878989507 := by
  unfold tailWord_6365195
  simp only [CollatzResearch.WordTrace]
  refine ⟨232157734174993078603553039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154771822783328719069035359 232157734174993078603553039)
  ·
    refine ⟨348236601262489617905329559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232157734174993078603553039 348236601262489617905329559)
    ·
      refine ⟨522354901893734426857994339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348236601262489617905329559 522354901893734426857994339)
      ·
        refine ⟨783532352840601640286991509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522354901893734426857994339 783532352840601640286991509)
        ·
          refine ⟨36728079039403201888452727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 783532352840601640286991509 36728079039403201888452727)
          ·
            refine ⟨55092118559104802832679091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36728079039403201888452727 55092118559104802832679091)
            ·
              refine ⟨82638177838657204249018637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55092118559104802832679091 82638177838657204249018637)
              ·
                refine ⟨30989316689496451593381989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82638177838657204249018637 30989316689496451593381989)
                ·
                  refine ⟨5810496879280584673759123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30989316689496451593381989 5810496879280584673759123)
                  ·
                    refine ⟨8715745318920877010638685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810496879280584673759123 8715745318920877010638685)
                    ·
                      refine ⟨3268404494595328878989507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715745318920877010638685 3268404494595328878989507)
                      ·
                        rfl

theorem cell23_6365195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 3].length) (baseStart_6365195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365195 prefixEnd_6365195 := by exact prefixLift 6365195
  have htrace : WordTrace (prefixWord ++ tailWord_6365195) baseStart_6365195 baseEnd_6365195 := by
    simpa [prefixWord, tailWord_6365195, baseEnd_6365195] using wordTrace_append hprefix tailTrace_6365195
  have hstable : (prefixWord ++ tailWord_6365195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365195).length < 2 ^ (prefixWord ++ tailWord_6365195).sum := by decide
  have hdescent : baseEnd_6365195 < baseStart_6365195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365196 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6365196 : Nat := 118140960795 + 6365196 * 2 ^ 59
def prefixEnd_6365196 : Nat := 4983230072969 + 3 ^ 40 * 6365196 * 2
def baseEnd_6365196 : Nat := 3268405008075983375077003

theorem tailTrace_6365196 : CollatzResearch.WordTrace tailWord_6365196 prefixEnd_6365196 3268405008075983375077003 := by
  unfold tailWord_6365196
  simp only [CollatzResearch.WordTrace]
  refine ⟨116078885323994727887169721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154771847098659637182892961 116078885323994727887169721)
  ·
    refine ⟨87059163992996045915377291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116078885323994727887169721 87059163992996045915377291)
    ·
      refine ⟨130588745989494068873065937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87059163992996045915377291 130588745989494068873065937)
      ·
        refine ⟨97941559492120551654799453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130588745989494068873065937 97941559492120551654799453)
        ·
          refine ⟨36728084809545206870549795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97941559492120551654799453 36728084809545206870549795)
          ·
            refine ⟨55092127214317810305824693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36728084809545206870549795 55092127214317810305824693)
            ·
              refine ⟨5164886926342294716171065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55092127214317810305824693 5164886926342294716171065)
              ·
                refine ⟨3873665194756721037128299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164886926342294716171065 3873665194756721037128299)
                ·
                  refine ⟨5810497792135081555692449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873665194756721037128299 5810497792135081555692449)
                  ·
                    refine ⟨4357873344101311166769337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810497792135081555692449 4357873344101311166769337)
                    ·
                      refine ⟨3268405008075983375077003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357873344101311166769337 3268405008075983375077003)
                      ·
                        rfl

theorem cell23_6365196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6365196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365196 prefixEnd_6365196 := by exact prefixLift 6365196
  have htrace : WordTrace (prefixWord ++ tailWord_6365196) baseStart_6365196 baseEnd_6365196 := by
    simpa [prefixWord, tailWord_6365196, baseEnd_6365196] using wordTrace_append hprefix tailTrace_6365196
  have hstable : (prefixWord ++ tailWord_6365196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365196).length < 2 ^ (prefixWord ++ tailWord_6365196).sum := by decide
  have hdescent : baseEnd_6365196 < baseStart_6365196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365198 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_6365198 : Nat := 118140960795 + 6365198 * 2 ^ 59
def prefixEnd_6365198 : Nat := 4983230072969 + 3 ^ 40 * 6365198 * 2
def baseEnd_6365198 : Nat := 1089468678345764122417331

theorem tailTrace_6365198 : CollatzResearch.WordTrace tailWord_6365198 prefixEnd_6365198 1089468678345764122417331 := by
  unfold tailWord_6365198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019730449247776264489031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154771895729321473410608165 29019730449247776264489031)
  ·
    refine ⟨43529595673871664396733547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29019730449247776264489031 43529595673871664396733547)
    ·
      refine ⟨65294393510807496595100321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43529595673871664396733547 65294393510807496595100321)
      ·
        refine ⟨48970795133105622446325241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65294393510807496595100321 48970795133105622446325241)
        ·
          refine ⟨36728096349829216834743931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48970795133105622446325241 36728096349829216834743931)
          ·
            refine ⟨55092144524743825252115897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36728096349829216834743931 55092144524743825252115897)
            ·
              refine ⟨41319108393557868939086923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55092144524743825252115897 41319108393557868939086923)
              ·
                refine ⟨61978662590336803408630385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41319108393557868939086923 61978662590336803408630385)
                ·
                  refine ⟨46483996942752602556472789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61978662590336803408630385 46483996942752602556472789)
                  ·
                    refine ⟨1089468678345764122417331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46483996942752602556472789 1089468678345764122417331)
                    ·
                      rfl

theorem cell23_6365198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_6365198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365198 prefixEnd_6365198 := by exact prefixLift 6365198
  have htrace : WordTrace (prefixWord ++ tailWord_6365198) baseStart_6365198 baseEnd_6365198 := by
    simpa [prefixWord, tailWord_6365198, baseEnd_6365198] using wordTrace_append hprefix tailTrace_6365198
  have hstable : (prefixWord ++ tailWord_6365198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365198).length < 2 ^ (prefixWord ++ tailWord_6365198).sum := by decide
  have hdescent : baseEnd_6365198 < baseStart_6365198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365235 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 4, 2]
def baseStart_6365235 : Nat := 118140960795 + 6365235 * 2 ^ 59
def prefixEnd_6365235 : Nat := 4983230072969 + 3 ^ 40 * 6365235 * 2
def baseEnd_6365235 : Nat := 3268425033821508722489323

theorem tailTrace_6365235 : CollatzResearch.WordTrace tailWord_6365235 prefixEnd_6365235 3268425033821508722489323 := by
  unfold tailWord_6365235
  simp only [CollatzResearch.WordTrace]
  refine ⟨232159193094848165435009159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154772795396565443623339439 232159193094848165435009159)
  ·
    refine ⟨348238789642272248152513739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232159193094848165435009159 348238789642272248152513739)
    ·
      refine ⟨522358184463408372228770609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348238789642272248152513739 522358184463408372228770609)
      ·
        refine ⟨391768638347556279171577957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522358184463408372228770609 391768638347556279171577957)
        ·
          refine ⟨73456619690166802344670867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391768638347556279171577957 73456619690166802344670867)
          ·
            refine ⟨110184929535250203517006301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73456619690166802344670867 110184929535250203517006301)
            ·
              refine ⟨41319348575718826318877363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110184929535250203517006301 41319348575718826318877363)
              ·
                refine ⟨61979022863578239478316045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41319348575718826318877363 61979022863578239478316045)
                ·
                  refine ⟨23242133573841839804368517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61979022863578239478316045 23242133573841839804368517)
                  ·
                    refine ⟨4357900045095344963319097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23242133573841839804368517 4357900045095344963319097)
                    ·
                      refine ⟨3268425033821508722489323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357900045095344963319097 3268425033821508722489323)
                      ·
                        rfl

theorem cell23_6365235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4, 2].length) (baseStart_6365235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365235 prefixEnd_6365235 := by exact prefixLift 6365235
  have htrace : WordTrace (prefixWord ++ tailWord_6365235) baseStart_6365235 baseEnd_6365235 := by
    simpa [prefixWord, tailWord_6365235, baseEnd_6365235] using wordTrace_append hprefix tailTrace_6365235
  have hstable : (prefixWord ++ tailWord_6365235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365235).length < 2 ^ (prefixWord ++ tailWord_6365235).sum := by decide
  have hdescent : baseEnd_6365235 < baseStart_6365235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365246 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6365246 : Nat := 118140960795 + 6365246 * 2 ^ 59
def prefixEnd_6365246 : Nat := 4983230072969 + 3 ^ 40 * 6365246 * 2
def baseEnd_6365246 : Nat := 3268430682108708179451773

theorem tailTrace_6365246 : CollatzResearch.WordTrace tailWord_6365246 prefixEnd_6365246 3268430682108708179451773 := by
  unfold tailWord_6365246
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019949287226039289207449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154773062865205542875773061 29019949287226039289207449)
  ·
    refine ⟨21764961965419529466905587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29019949287226039289207449 21764961965419529466905587)
    ·
      refine ⟨32647442948129294200358381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21764961965419529466905587 32647442948129294200358381)
      ·
        refine ⟨12242791105548485325134393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32647442948129294200358381 12242791105548485325134393)
        ·
          refine ⟨9182093329161363993850795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12242791105548485325134393 9182093329161363993850795)
          ·
            refine ⟨13773139993742045990776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182093329161363993850795 13773139993742045990776193)
            ·
              refine ⟨10329854995306534493082145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773139993742045990776193 10329854995306534493082145)
              ·
                refine ⟨7747391246479900869811609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10329854995306534493082145 7747391246479900869811609)
                ·
                  refine ⟨5810543434859925652358707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7747391246479900869811609 5810543434859925652358707)
                  ·
                    refine ⟨8715815152289888478538061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810543434859925652358707 8715815152289888478538061)
                    ·
                      refine ⟨3268430682108708179451773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715815152289888478538061 3268430682108708179451773)
                      ·
                        rfl

theorem cell23_6365246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6365246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365246 prefixEnd_6365246 := by exact prefixLift 6365246
  have htrace : WordTrace (prefixWord ++ tailWord_6365246) baseStart_6365246 baseEnd_6365246 := by
    simpa [prefixWord, tailWord_6365246, baseEnd_6365246] using wordTrace_append hprefix tailTrace_6365246
  have hstable : (prefixWord ++ tailWord_6365246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365246).length < 2 ^ (prefixWord ++ tailWord_6365246).sum := by decide
  have hdescent : baseEnd_6365246 < baseStart_6365246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365258 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_6365258 : Nat := 118140960795 + 6365258 * 2 ^ 59
def prefixEnd_6365258 : Nat := 4983230072969 + 3 ^ 40 * 6365258 * 2
def baseEnd_6365258 : Nat := 363159649319618014722413

theorem tailTrace_6365258 : CollatzResearch.WordTrace tailWord_6365258 prefixEnd_6365258 363159649319618014722413 := by
  unfold tailWord_6365258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58040007993441210090774107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154773354649176560242064285 58040007993441210090774107)
  ·
    refine ⟨87060011990161815136161161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58040007993441210090774107 87060011990161815136161161)
    ·
      refine ⟨65295008992621361352120871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87060011990161815136161161 65295008992621361352120871)
      ·
        refine ⟨97942513488932042028181307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65295008992621361352120871 97942513488932042028181307)
        ·
          refine ⟨146913770233398063042271961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97942513488932042028181307 146913770233398063042271961)
          ·
            refine ⟨110185327675048547281703971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146913770233398063042271961 110185327675048547281703971)
            ·
              refine ⟨165277991512572820922555957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110185327675048547281703971 165277991512572820922555957)
              ·
                refine ⟨15494811704303701961489621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165277991512572820922555957 15494811704303701961489621)
                ·
                  refine ⟨363159649319618014722413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15494811704303701961489621 363159649319618014722413)
                  ·
                    rfl

theorem cell23_6365258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_6365258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365258 prefixEnd_6365258 := by exact prefixLift 6365258
  have htrace : WordTrace (prefixWord ++ tailWord_6365258) baseStart_6365258 baseEnd_6365258 := by
    simpa [prefixWord, tailWord_6365258, baseEnd_6365258] using wordTrace_append hprefix tailTrace_6365258
  have hstable : (prefixWord ++ tailWord_6365258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365258).length < 2 ^ (prefixWord ++ tailWord_6365258).sum := by decide
  have hdescent : baseEnd_6365258 < baseStart_6365258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365269 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6365269 : Nat := 118140960795 + 6365269 * 2 ^ 59
def prefixEnd_6365269 : Nat := 4983230072969 + 3 ^ 40 * 6365269 * 2
def baseEnd_6365269 : Nat := 3268442492163761589464167

theorem tailTrace_6365269 : CollatzResearch.WordTrace tailWord_6365269 prefixEnd_6365269 3268442492163761589464167 := by
  unfold tailWord_6365269
  simp only [CollatzResearch.WordTrace]
  refine ⟨232160433176724989241746861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154773622117816659494497907 232160433176724989241746861)
  ·
    refine ⟨87060162441271870965655073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232160433176724989241746861 87060162441271870965655073)
    ·
      refine ⟨65295121830953903224241305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87060162441271870965655073 65295121830953903224241305)
      ·
        refine ⟨48971341373215427418180979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65295121830953903224241305 48971341373215427418180979)
        ·
          refine ⟨73457012059823141127271469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48971341373215427418180979 73457012059823141127271469)
          ·
            refine ⟨27546379522433677922726801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73457012059823141127271469 27546379522433677922726801)
            ·
              refine ⟨20659784641825258442045101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27546379522433677922726801 20659784641825258442045101)
              ·
                refine ⟨7747419240684471915766913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20659784641825258442045101 7747419240684471915766913)
                ·
                  refine ⟨5810564430513353936825185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7747419240684471915766913 5810564430513353936825185)
                  ·
                    refine ⟨4357923322885015452618889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810564430513353936825185 4357923322885015452618889)
                    ·
                      refine ⟨3268442492163761589464167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357923322885015452618889 3268442492163761589464167)
                      ·
                        rfl

theorem cell23_6365269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6365269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365269 prefixEnd_6365269 := by exact prefixLift 6365269
  have htrace : WordTrace (prefixWord ++ tailWord_6365269) baseStart_6365269 baseEnd_6365269 := by
    simpa [prefixWord, tailWord_6365269, baseEnd_6365269] using wordTrace_append hprefix tailTrace_6365269
  have hstable : (prefixWord ++ tailWord_6365269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365269).length < 2 ^ (prefixWord ++ tailWord_6365269).sum := by decide
  have hdescent : baseEnd_6365269 < baseStart_6365269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365292 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 5]
def baseStart_6365292 : Nat := 118140960795 + 6365292 * 2 ^ 59
def prefixEnd_6365292 : Nat := 4983230072969 + 3 ^ 40 * 6365292 * 2
def baseEnd_6365292 : Nat := 363161589135423888830729

theorem tailTrace_6365292 : CollatzResearch.WordTrace tailWord_6365292 prefixEnd_6365292 363161589135423888830729 := by
  unfold tailWord_6365292
  simp only [CollatzResearch.WordTrace]
  refine ⟨116080636027820832084917065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154774181370427776113222753 116080636027820832084917065)
  ·
    refine ⟨87060477020865624063687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116080636027820832084917065 87060477020865624063687799)
    ·
      refine ⟨130590715531298436095531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87060477020865624063687799 130590715531298436095531699)
      ·
        refine ⟨195886073296947654143297549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130590715531298436095531699 195886073296947654143297549)
        ·
          refine ⟨73457277486355370303736581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195886073296947654143297549 73457277486355370303736581)
          ·
            refine ⟨13773239528691631931950609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73457277486355370303736581 13773239528691631931950609)
            ·
              refine ⟨10329929646518723948962957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773239528691631931950609 10329929646518723948962957)
              ·
                refine ⟨3873723617444521480861109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10329929646518723948962957 3873723617444521480861109)
                ·
                  refine ⟨363161589135423888830729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3873723617444521480861109 363161589135423888830729)
                  ·
                    rfl

theorem cell23_6365292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_6365292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365292 prefixEnd_6365292 := by exact prefixLift 6365292
  have htrace : WordTrace (prefixWord ++ tailWord_6365292) baseStart_6365292 baseEnd_6365292 := by
    simpa [prefixWord, tailWord_6365292, baseEnd_6365292] using wordTrace_append hprefix tailTrace_6365292
  have hstable : (prefixWord ++ tailWord_6365292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365292).length < 2 ^ (prefixWord ++ tailWord_6365292).sum := by decide
  have hdescent : baseEnd_6365292 < baseStart_6365292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365302 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6365302 : Nat := 118140960795 + 6365302 * 2 ^ 59
def prefixEnd_6365302 : Nat := 4983230072969 + 3 ^ 40 * 6365302 * 2
def baseEnd_6365302 : Nat := 3268459437025359960351515

theorem tailTrace_6365302 : CollatzResearch.WordTrace tailWord_6365302 prefixEnd_6365302 3268459437025359960351515 := by
  unfold tailWord_6365302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510102299100339742356135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154774424523736957251798773 14510102299100339742356135)
  ·
    refine ⟨21765153448650509613534203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14510102299100339742356135 21765153448650509613534203)
    ·
      refine ⟨32647730172975764420301305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21765153448650509613534203 32647730172975764420301305)
      ·
        refine ⟨24485797629731823315225979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32647730172975764420301305 24485797629731823315225979)
        ·
          refine ⟨36728696444597734972838969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24485797629731823315225979 36728696444597734972838969)
          ·
            refine ⟨27546522333448301229629227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36728696444597734972838969 27546522333448301229629227)
            ·
              refine ⟨41319783500172451844443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27546522333448301229629227 41319783500172451844443841)
              ·
                refine ⟨30989837625129338883332881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41319783500172451844443841 30989837625129338883332881)
                ·
                  refine ⟨23242378218847004162499661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30989837625129338883332881 23242378218847004162499661)
                  ·
                    refine ⟨8715891832067626560937373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23242378218847004162499661 8715891832067626560937373)
                    ·
                      refine ⟨3268459437025359960351515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715891832067626560937373 3268459437025359960351515)
                      ·
                        rfl

theorem cell23_6365302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6365302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365302 prefixEnd_6365302 := by exact prefixLift 6365302
  have htrace : WordTrace (prefixWord ++ tailWord_6365302) baseStart_6365302 baseEnd_6365302 := by
    simpa [prefixWord, tailWord_6365302, baseEnd_6365302] using wordTrace_append hprefix tailTrace_6365302
  have hstable : (prefixWord ++ tailWord_6365302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365302).length < 2 ^ (prefixWord ++ tailWord_6365302).sum := by decide
  have hdescent : baseEnd_6365302 < baseStart_6365302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365362 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_6365362 : Nat := 118140960795 + 6365362 * 2 ^ 59
def prefixEnd_6365362 : Nat := 4983230072969 + 3 ^ 40 * 6365362 * 2
def baseEnd_6365362 : Nat := 3268490245864629725601239

theorem tailTrace_6365362 : CollatzResearch.WordTrace tailWord_6365362 prefixEnd_6365362 3268490245864629725601239 := by
  unfold tailWord_6365362
  simp only [CollatzResearch.WordTrace]
  refine ⟨58040956291347016531220585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154775883443592044083254893 58040956291347016531220585)
  ·
    refine ⟨43530717218510262398415439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58040956291347016531220585 43530717218510262398415439)
    ·
      refine ⟨65296075827765393597623159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43530717218510262398415439 65296075827765393597623159)
      ·
        refine ⟨97944113741648090396434739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65296075827765393597623159 97944113741648090396434739)
        ·
          refine ⟨146916170612472135594652109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97944113741648090396434739 146916170612472135594652109)
          ·
            refine ⟨55093563979677050847994541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146916170612472135594652109 55093563979677050847994541)
            ·
              refine ⟨20660086492378894067997953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55093563979677050847994541 20660086492378894067997953)
              ·
                refine ⟨15495064869284170550998465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20660086492378894067997953 15495064869284170550998465)
                ·
                  refine ⟨11621298651963127913248849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15495064869284170550998465 11621298651963127913248849)
                  ·
                    refine ⟨8715973988972345934936637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11621298651963127913248849 8715973988972345934936637)
                    ·
                      refine ⟨3268490245864629725601239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8715973988972345934936637 3268490245864629725601239)
                      ·
                        rfl

theorem cell23_6365362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_6365362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365362 prefixEnd_6365362 := by exact prefixLift 6365362
  have htrace : WordTrace (prefixWord ++ tailWord_6365362) baseStart_6365362 baseEnd_6365362 := by
    simpa [prefixWord, tailWord_6365362, baseEnd_6365362] using wordTrace_append hprefix tailTrace_6365362
  have hstable : (prefixWord ++ tailWord_6365362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365362).length < 2 ^ (prefixWord ++ tailWord_6365362).sum := by decide
  have hdescent : baseEnd_6365362 < baseStart_6365362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365402 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_6365402 : Nat := 118140960795 + 6365402 * 2 ^ 59
def prefixEnd_6365402 : Nat := 4983230072969 + 3 ^ 40 * 6365402 * 2
def baseEnd_6365402 : Nat := 3268510785090809569101055

theorem tailTrace_6365402 : CollatzResearch.WordTrace tailWord_6365402 prefixEnd_6365402 3268510785090809569101055 := by
  unfold tailWord_6365402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041321021310788239084615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154776856056828768637558973 58041321021310788239084615)
  ·
    refine ⟨87061981531966182358626923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58041321021310788239084615 87061981531966182358626923)
    ·
      refine ⟨130592972297949273537940385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87061981531966182358626923 130592972297949273537940385)
      ·
        refine ⟨97944729223461955153455289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130592972297949273537940385 97944729223461955153455289)
        ·
          refine ⟨73458546917596466365091467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97944729223461955153455289 73458546917596466365091467)
          ·
            refine ⟨110187820376394699547637201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73458546917596466365091467 110187820376394699547637201)
            ·
              refine ⟨82640865282296024660727901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110187820376394699547637201 82640865282296024660727901)
              ·
                refine ⟨30990324480861009247772963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82640865282296024660727901 30990324480861009247772963)
                ·
                  refine ⟨46485486721291513871659445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30990324480861009247772963 46485486721291513871659445)
                  ·
                    refine ⟨4358014380121079425468073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46485486721291513871659445 4358014380121079425468073)
                    ·
                      refine ⟨3268510785090809569101055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358014380121079425468073 3268510785090809569101055)
                      ·
                        rfl

theorem cell23_6365402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_6365402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365402 prefixEnd_6365402 := by exact prefixLift 6365402
  have htrace : WordTrace (prefixWord ++ tailWord_6365402) baseStart_6365402 baseEnd_6365402 := by
    simpa [prefixWord, tailWord_6365402, baseEnd_6365402] using wordTrace_append hprefix tailTrace_6365402
  have hstable : (prefixWord ++ tailWord_6365402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365402).length < 2 ^ (prefixWord ++ tailWord_6365402).sum := by decide
  have hdescent : baseEnd_6365402 < baseStart_6365402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365449 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 5, 2, 2]
def baseStart_6365449 : Nat := 118140960795 + 6365449 * 2 ^ 59
def prefixEnd_6365449 : Nat := 4983230072969 + 3 ^ 40 * 6365449 * 2
def baseEnd_6365449 : Nat := 3268534918681570885213339

theorem tailTrace_6365449 : CollatzResearch.WordTrace tailWord_6365449 prefixEnd_6365449 3268534918681570885213339 := by
  unfold tailWord_6365449
  simp only [CollatzResearch.WordTrace]
  refine ⟨232166998316072879983299401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154777998877381919988866267 232166998316072879983299401)
  ·
    refine ⟨174125248737054659987474551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232166998316072879983299401 174125248737054659987474551)
    ·
      refine ⟨261187873105581989981211827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174125248737054659987474551 261187873105581989981211827)
      ·
        refine ⟨391781809658372984971817741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261187873105581989981211827 391781809658372984971817741)
        ·
          refine ⟨146918178621889869364431653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391781809658372984971817741 146918178621889869364431653)
          ·
            refine ⟨27547158491604350505830935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146918178621889869364431653 27547158491604350505830935)
            ·
              refine ⟨41320737737406525758746403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27547158491604350505830935 41320737737406525758746403)
              ·
                refine ⟨61981106606109788638119605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41320737737406525758746403 61981106606109788638119605)
                ·
                  refine ⟨5810728744322792684823713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61981106606109788638119605 5810728744322792684823713)
                  ·
                    refine ⟨4358046558242094513617785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810728744322792684823713 4358046558242094513617785)
                    ·
                      refine ⟨3268534918681570885213339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358046558242094513617785 3268534918681570885213339)
                      ·
                        rfl

theorem cell23_6365449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2, 2].length) (baseStart_6365449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365449 prefixEnd_6365449 := by exact prefixLift 6365449
  have htrace : WordTrace (prefixWord ++ tailWord_6365449) baseStart_6365449 baseEnd_6365449 := by
    simpa [prefixWord, tailWord_6365449, baseEnd_6365449] using wordTrace_append hprefix tailTrace_6365449
  have hstable : (prefixWord ++ tailWord_6365449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365449).length < 2 ^ (prefixWord ++ tailWord_6365449).sum := by decide
  have hdescent : baseEnd_6365449 < baseStart_6365449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365452 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6365452 : Nat := 118140960795 + 6365452 * 2 ^ 59
def prefixEnd_6365452 : Nat := 4983230072969 + 3 ^ 40 * 6365452 * 2
def baseEnd_6365452 : Nat := 3268536459123534373475825

theorem tailTrace_6365452 : CollatzResearch.WordTrace tailWord_6365452 prefixEnd_6365452 3268536459123534373475825 := by
  unfold tailWord_6365452
  simp only [CollatzResearch.WordTrace]
  refine ⟨116083553867531005747829305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154778071823374674330439073 116083553867531005747829305)
  ·
    refine ⟨87062665400648254310871979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116083553867531005747829305 87062665400648254310871979)
    ·
      refine ⟨130593998100972381466307969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87062665400648254310871979 130593998100972381466307969)
      ·
        refine ⟨97945498575729286099730977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130593998100972381466307969 97945498575729286099730977)
        ·
          refine ⟨73459123931796964574798233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97945498575729286099730977 73459123931796964574798233)
          ·
            refine ⟨55094342948847723431098675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73459123931796964574798233 55094342948847723431098675)
            ·
              refine ⟨82641514423271585146648013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55094342948847723431098675 82641514423271585146648013)
              ·
                refine ⟨30990567908726844429993005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82641514423271585146648013 30990567908726844429993005)
                ·
                  refine ⟨11621462965772566661247377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30990567908726844429993005 11621462965772566661247377)
                  ·
                    refine ⟨8716097224329424995935533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11621462965772566661247377 8716097224329424995935533)
                    ·
                      refine ⟨3268536459123534373475825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8716097224329424995935533 3268536459123534373475825)
                      ·
                        rfl

theorem cell23_6365452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6365452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365452 prefixEnd_6365452 := by exact prefixLift 6365452
  have htrace : WordTrace (prefixWord ++ tailWord_6365452) baseStart_6365452 baseEnd_6365452 := by
    simpa [prefixWord, tailWord_6365452, baseEnd_6365452] using wordTrace_append hprefix tailTrace_6365452
  have hstable : (prefixWord ++ tailWord_6365452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365452).length < 2 ^ (prefixWord ++ tailWord_6365452).sum := by decide
  have hdescent : baseEnd_6365452 < baseStart_6365452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365476 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_6365476 : Nat := 118140960795 + 6365476 * 2 ^ 59
def prefixEnd_6365476 : Nat := 4983230072969 + 3 ^ 40 * 6365476 * 2
def baseEnd_6365476 : Nat := 1089516260886414093191905

theorem tailTrace_6365476 : CollatzResearch.WordTrace tailWord_6365476 prefixEnd_6365476 1089516260886414093191905 := by
  unfold tailWord_6365476
  simp only [CollatzResearch.WordTrace]
  refine ⟨116083991543487531797266141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154778655391316709063021521 116083991543487531797266141)
  ·
    refine ⟨43531496828807824423974803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116083991543487531797266141 43531496828807824423974803)
    ·
      refine ⟨65297245243211736635962205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43531496828807824423974803 65297245243211736635962205)
      ·
        refine ⟨24486466966204401238485827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65297245243211736635962205 24486466966204401238485827)
        ·
          refine ⟨36729700449306601857728741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24486466966204401238485827 36729700449306601857728741)
          ·
            refine ⟨6886818834244987848324139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36729700449306601857728741 6886818834244987848324139)
            ·
              refine ⟨10330228251367481772486209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886818834244987848324139 10330228251367481772486209)
              ·
                refine ⟨7747671188525611329364657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10330228251367481772486209 7747671188525611329364657)
                ·
                  refine ⟨5810753391394208497023493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7747671188525611329364657 5810753391394208497023493)
                  ·
                    refine ⟨1089516260886414093191905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810753391394208497023493 1089516260886414093191905)
                    ·
                      rfl

theorem cell23_6365476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_6365476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365476 prefixEnd_6365476 := by exact prefixLift 6365476
  have htrace : WordTrace (prefixWord ++ tailWord_6365476) baseStart_6365476 baseEnd_6365476 := by
    simpa [prefixWord, tailWord_6365476, baseEnd_6365476] using wordTrace_append hprefix tailTrace_6365476
  have hstable : (prefixWord ++ tailWord_6365476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365476).length < 2 ^ (prefixWord ++ tailWord_6365476).sum := by decide
  have hdescent : baseEnd_6365476 < baseStart_6365476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365486 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6365486 : Nat := 118140960795 + 6365486 * 2 ^ 59
def prefixEnd_6365486 : Nat := 4983230072969 + 3 ^ 40 * 6365486 * 2
def baseEnd_6365486 : Nat := 3268553917465787240450669

theorem tailTrace_6365486 : CollatzResearch.WordTrace tailWord_6365486 prefixEnd_6365486 3268553917465787240450669 := by
  unfold tailWord_6365486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021043477117354412799539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154778898544625890201597541 29021043477117354412799539)
  ·
    refine ⟨43531565215676031619199309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29021043477117354412799539 43531565215676031619199309)
    ·
      refine ⟨16324336955878511857199741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43531565215676031619199309 16324336955878511857199741)
      ·
        refine ⟨6121626358454441946449903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16324336955878511857199741 6121626358454441946449903)
        ·
          refine ⟨9182439537681662919674855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121626358454441946449903 9182439537681662919674855)
          ·
            refine ⟨13773659306522494379512283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182439537681662919674855 13773659306522494379512283)
            ·
              refine ⟨20660488959783741569268425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773659306522494379512283 20660488959783741569268425)
              ·
                refine ⟨15495366719837806176951319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20660488959783741569268425 15495366719837806176951319)
                ·
                  refine ⟨23243050079756709265426979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15495366719837806176951319 23243050079756709265426979)
                  ·
                    refine ⟨34864575119635063898140469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23243050079756709265426979 34864575119635063898140469)
                    ·
                      refine ⟨3268553917465787240450669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34864575119635063898140469 3268553917465787240450669)
                      ·
                        rfl

theorem cell23_6365486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6365486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365486 prefixEnd_6365486 := by exact prefixLift 6365486
  have htrace : WordTrace (prefixWord ++ tailWord_6365486) baseStart_6365486 baseEnd_6365486 := by
    simpa [prefixWord, tailWord_6365486, baseEnd_6365486] using wordTrace_append hprefix tailTrace_6365486
  have hstable : (prefixWord ++ tailWord_6365486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365486).length < 2 ^ (prefixWord ++ tailWord_6365486).sum := by decide
  have hdescent : baseEnd_6365486 < baseStart_6365486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365495 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_6365495 : Nat := 118140960795 + 6365495 * 2 ^ 59
def prefixEnd_6365495 : Nat := 4983230072969 + 3 ^ 40 * 6365495 * 2
def baseEnd_6365495 : Nat := 3268558538791677705238127

theorem tailTrace_6365495 : CollatzResearch.WordTrace tailWord_6365495 prefixEnd_6365495 3268558538791677705238127 := by
  unfold tailWord_6365495
  simp only [CollatzResearch.WordTrace]
  refine ⟨232168676073906229839473939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154779117382604153226315959 232168676073906229839473939)
  ·
    refine ⟨348253014110859344759210909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232168676073906229839473939 348253014110859344759210909)
    ·
      refine ⟨130594880291572254284704091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348253014110859344759210909 130594880291572254284704091)
      ·
        refine ⟨195892320437358381427056137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130594880291572254284704091 195892320437358381427056137)
        ·
          refine ⟨146919240328018786070292103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195892320437358381427056137 146919240328018786070292103)
          ·
            refine ⟨220378860492028179105438155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146919240328018786070292103 220378860492028179105438155)
            ·
              refine ⟨330568290738042268658157233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220378860492028179105438155 330568290738042268658157233)
              ·
                refine ⟨247926218053531701493617925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330568290738042268658157233 247926218053531701493617925)
                ·
                  refine ⟨46486165885037194030053361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247926218053531701493617925 46486165885037194030053361)
                  ·
                    refine ⟨34864624413777895522540021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46486165885037194030053361 34864624413777895522540021)
                    ·
                      refine ⟨3268558538791677705238127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34864624413777895522540021 3268558538791677705238127)
                      ·
                        rfl

theorem cell23_6365495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_6365495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365495 prefixEnd_6365495 := by exact prefixLift 6365495
  have htrace : WordTrace (prefixWord ++ tailWord_6365495) baseStart_6365495 baseEnd_6365495 := by
    simpa [prefixWord, tailWord_6365495, baseEnd_6365495] using wordTrace_append hprefix tailTrace_6365495
  have hstable : (prefixWord ++ tailWord_6365495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365495).length < 2 ^ (prefixWord ++ tailWord_6365495).sum := by decide
  have hdescent : baseEnd_6365495 < baseStart_6365495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 6]
def baseStart_6365515 : Nat := 118140960795 + 6365515 * 2 ^ 59
def prefixEnd_6365515 : Nat := 4983230072969 + 3 ^ 40 * 6365515 * 2
def baseEnd_6365515 : Nat := 1089522936134922542329345

theorem tailTrace_6365515 : CollatzResearch.WordTrace tailWord_6365515 prefixEnd_6365515 1089522936134922542329345 := by
  unfold tailWord_6365515
  simp only [CollatzResearch.WordTrace]
  refine ⟨232169405533833773255201999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154779603689222515503467999 232169405533833773255201999)
  ·
    refine ⟨348254108300750659882802999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232169405533833773255201999 348254108300750659882802999)
    ·
      refine ⟨522381162451125989824204499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348254108300750659882802999 522381162451125989824204499)
      ·
        refine ⟨783571743676688984736306749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522381162451125989824204499 783571743676688984736306749)
        ·
          refine ⟨293839403878758369276115031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783571743676688984736306749 293839403878758369276115031)
          ·
            refine ⟨440759105818137553914172547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293839403878758369276115031 440759105818137553914172547)
            ·
              refine ⟨661138658727206330871258821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440759105818137553914172547 661138658727206330871258821)
              ·
                refine ⟨123963498511351187038361029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661138658727206330871258821 123963498511351187038361029)
                ·
                  refine ⟨23243155970878347569692693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123963498511351187038361029 23243155970878347569692693)
                  ·
                    refine ⟨1089522936134922542329345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23243155970878347569692693 1089522936134922542329345)
                    ·
                      rfl

theorem cell23_6365515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_6365515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365515 prefixEnd_6365515 := by exact prefixLift 6365515
  have htrace : WordTrace (prefixWord ++ tailWord_6365515) baseStart_6365515 baseEnd_6365515 := by
    simpa [prefixWord, tailWord_6365515, baseEnd_6365515] using wordTrace_append hprefix tailTrace_6365515
  have hstable : (prefixWord ++ tailWord_6365515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365515).length < 2 ^ (prefixWord ++ tailWord_6365515).sum := by decide
  have hdescent : baseEnd_6365515 < baseStart_6365515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_6365555 : Nat := 118140960795 + 6365555 * 2 ^ 59
def prefixEnd_6365555 : Nat := 4983230072969 + 3 ^ 40 * 6365555 * 2
def baseEnd_6365555 : Nat := 3268589347630947470487851

theorem tailTrace_6365555 : CollatzResearch.WordTrace tailWord_6365555 prefixEnd_6365555 3268589347630947470487851 := by
  unfold tailWord_6365555
  simp only [CollatzResearch.WordTrace]
  refine ⟨232170864453688860086658119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154780576302459240057772079 232170864453688860086658119)
  ·
    refine ⟨348256296680533290129987179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232170864453688860086658119 348256296680533290129987179)
    ·
      refine ⟨522384445020799935194980769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348256296680533290129987179 522384445020799935194980769)
      ·
        refine ⟨391788333765599951396235577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522384445020799935194980769 391788333765599951396235577)
        ·
          refine ⟨293841250324199963547176683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391788333765599951396235577 293841250324199963547176683)
          ·
            refine ⟨440761875486299945320765025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293841250324199963547176683 440761875486299945320765025)
            ·
              refine ⟨330571406614724958990573769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440761875486299945320765025 330571406614724958990573769)
              ·
                refine ⟨247928554961043719242930327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330571406614724958990573769 247928554961043719242930327)
                ·
                  refine ⟨371892832441565578864395491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247928554961043719242930327 371892832441565578864395491)
                  ·
                    refine ⟨557839248662348368296593237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371892832441565578864395491 557839248662348368296593237)
                    ·
                      refine ⟨3268589347630947470487851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 557839248662348368296593237 3268589347630947470487851)
                      ·
                        rfl

theorem cell23_6365555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_6365555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365555 prefixEnd_6365555 := by exact prefixLift 6365555
  have htrace : WordTrace (prefixWord ++ tailWord_6365555) baseStart_6365555 baseEnd_6365555 := by
    simpa [prefixWord, tailWord_6365555, baseEnd_6365555] using wordTrace_append hprefix tailTrace_6365555
  have hstable : (prefixWord ++ tailWord_6365555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365555).length < 2 ^ (prefixWord ++ tailWord_6365555).sum := by decide
  have hdescent : baseEnd_6365555 < baseStart_6365555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365599 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6365599 : Nat := 118140960795 + 6365599 * 2 ^ 59
def prefixEnd_6365599 : Nat := 4983230072969 + 3 ^ 40 * 6365599 * 2
def baseEnd_6365599 : Nat := 3268611940779745298337649

theorem tailTrace_6365599 : CollatzResearch.WordTrace tailWord_6365599 prefixEnd_6365599 3268611940779745298337649 := by
  unfold tailWord_6365599
  simp only [CollatzResearch.WordTrace]
  refine ⟨232172469265529455601259851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154781646177019637067506567 232172469265529455601259851)
  ·
    refine ⟨348258703898294183401889777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232172469265529455601259851 348258703898294183401889777)
    ·
      refine ⟨261194027923720637551417333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348258703898294183401889777 261194027923720637551417333)
      ·
        refine ⟨24486940117848809770445375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261194027923720637551417333 24486940117848809770445375)
        ·
          refine ⟨36730410176773214655668063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24486940117848809770445375 36730410176773214655668063)
          ·
            refine ⟨55095615265159821983502095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36730410176773214655668063 55095615265159821983502095)
            ·
              refine ⟨82643422897739732975253143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55095615265159821983502095 82643422897739732975253143)
              ·
                refine ⟨123965134346609599462879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82643422897739732975253143 123965134346609599462879715)
                ·
                  refine ⟨185947701519914399194319573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123965134346609599462879715 185947701519914399194319573)
                  ·
                    refine ⟨4358149254372993731116865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185947701519914399194319573 4358149254372993731116865)
                    ·
                      refine ⟨3268611940779745298337649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358149254372993731116865 3268611940779745298337649)
                      ·
                        rfl

theorem cell23_6365599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6365599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365599 prefixEnd_6365599 := by exact prefixLift 6365599
  have htrace : WordTrace (prefixWord ++ tailWord_6365599) baseStart_6365599 baseEnd_6365599 := by
    simpa [prefixWord, tailWord_6365599, baseEnd_6365599] using wordTrace_append hprefix tailTrace_6365599
  have hstable : (prefixWord ++ tailWord_6365599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365599).length < 2 ^ (prefixWord ++ tailWord_6365599).sum := by decide
  have hdescent : baseEnd_6365599 < baseStart_6365599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365612 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_6365612 : Nat := 118140960795 + 6365612 * 2 ^ 59
def prefixEnd_6365612 : Nat := 4983230072969 + 3 ^ 40 * 6365612 * 2
def baseEnd_6365612 : Nat := 3268618616028253747475089

theorem tailTrace_6365612 : CollatzResearch.WordTrace tailWord_6365612 prefixEnd_6365612 3268618616028253747475089 := by
  unfold tailWord_6365612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116086471707241179410741545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154781962276321572547655393 116086471707241179410741545)
  ·
    refine ⟨87064853780430884558056159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116086471707241179410741545 87064853780430884558056159)
    ·
      refine ⟨130597280670646326837084239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87064853780430884558056159 130597280670646326837084239)
      ·
        refine ⟨195895921005969490255626359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130597280670646326837084239 195895921005969490255626359)
        ·
          refine ⟨293843881508954235383439539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195895921005969490255626359 293843881508954235383439539)
          ·
            refine ⟨440765822263431353075159309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293843881508954235383439539 440765822263431353075159309)
            ·
              refine ⟨165287183348786757403184741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440765822263431353075159309 165287183348786757403184741)
              ·
                refine ⟨30991346877897517013097139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165287183348786757403184741 30991346877897517013097139)
                ·
                  refine ⟨46487020316846275519645709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30991346877897517013097139 46487020316846275519645709)
                  ·
                    refine ⟨17432632618817353319867141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46487020316846275519645709 17432632618817353319867141)
                    ·
                      refine ⟨3268618616028253747475089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17432632618817353319867141 3268618616028253747475089)
                      ·
                        rfl

theorem cell23_6365612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_6365612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365612 prefixEnd_6365612 := by exact prefixLift 6365612
  have htrace : WordTrace (prefixWord ++ tailWord_6365612) baseStart_6365612 baseEnd_6365612 := by
    simpa [prefixWord, tailWord_6365612, baseEnd_6365612] using wordTrace_append hprefix tailTrace_6365612
  have hstable : (prefixWord ++ tailWord_6365612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365612).length < 2 ^ (prefixWord ++ tailWord_6365612).sum := by decide
  have hdescent : baseEnd_6365612 < baseStart_6365612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365629 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_6365629 : Nat := 118140960795 + 6365629 * 2 ^ 59
def prefixEnd_6365629 : Nat := 4983230072969 + 3 ^ 40 * 6365629 * 2
def baseEnd_6365629 : Nat := 3268627345199380180962511

theorem tailTrace_6365629 : CollatzResearch.WordTrace tailWord_6365629 prefixEnd_6365629 3268627345199380180962511 := by
  unfold tailWord_6365629
  simp only [CollatzResearch.WordTrace]
  refine ⟨232173563455420770724851941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154782375636947180483234627 232173563455420770724851941)
  ·
    refine ⟨43532543147891394510909739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232173563455420770724851941 43532543147891394510909739)
    ·
      refine ⟨65298814721837091766364609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43532543147891394510909739 65298814721837091766364609)
      ·
        refine ⟨48974111041377818824773457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65298814721837091766364609 48974111041377818824773457)
        ·
          refine ⟨36730583281033364118580093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48974111041377818824773457 36730583281033364118580093)
          ·
            refine ⟨13773968730387511544467535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36730583281033364118580093 13773968730387511544467535)
            ·
              refine ⟨20660953095581267316701303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773968730387511544467535 20660953095581267316701303)
              ·
                refine ⟨30991429643371900975051955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20660953095581267316701303 30991429643371900975051955)
                ·
                  refine ⟨46487144465057851462577933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30991429643371900975051955 46487144465057851462577933)
                  ·
                    refine ⟨17432679174396694298466725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46487144465057851462577933 17432679174396694298466725)
                    ·
                      refine ⟨3268627345199380180962511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17432679174396694298466725 3268627345199380180962511)
                      ·
                        rfl

theorem cell23_6365629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_6365629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365629 prefixEnd_6365629 := by exact prefixLift 6365629
  have htrace : WordTrace (prefixWord ++ tailWord_6365629) baseStart_6365629 baseEnd_6365629 := by
    simpa [prefixWord, tailWord_6365629, baseEnd_6365629] using wordTrace_append hprefix tailTrace_6365629
  have hstable : (prefixWord ++ tailWord_6365629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365629).length < 2 ^ (prefixWord ++ tailWord_6365629).sum := by decide
  have hdescent : baseEnd_6365629 < baseStart_6365629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365642 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6365642 : Nat := 118140960795 + 6365642 * 2 ^ 59
def prefixEnd_6365642 : Nat := 4983230072969 + 3 ^ 40 * 6365642 * 2
def baseEnd_6365642 : Nat := 3268634020447888630099951

theorem tailTrace_6365642 : CollatzResearch.WordTrace tailWord_6365642 prefixEnd_6365642 3268634020447888630099951 := by
  unfold tailWord_6365642
  simp only [CollatzResearch.WordTrace]
  refine ⟨58043509401093418486268795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154782691736249115963383453 58043509401093418486268795)
  ·
    refine ⟨87065264101640127729403193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58043509401093418486268795 87065264101640127729403193)
    ·
      refine ⟨65298948076230095797052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87065264101640127729403193 65298948076230095797052395)
      ·
        refine ⟨97948422114345143695578593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65298948076230095797052395 97948422114345143695578593)
        ·
          refine ⟨73461316585758857771683945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97948422114345143695578593 73461316585758857771683945)
          ·
            refine ⟨55095987439319143328762959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73461316585758857771683945 55095987439319143328762959)
            ·
              refine ⟨82643981158978714993144439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55095987439319143328762959 82643981158978714993144439)
              ·
                refine ⟨123965971738468072489716659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82643981158978714993144439 123965971738468072489716659)
                ·
                  refine ⟨185948957607702108734574989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123965971738468072489716659 185948957607702108734574989)
                  ·
                    refine ⟨69730859102888290775465621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185948957607702108734574989 69730859102888290775465621)
                    ·
                      refine ⟨3268634020447888630099951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69730859102888290775465621 3268634020447888630099951)
                      ·
                        rfl

theorem cell23_6365642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6365642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365642 prefixEnd_6365642 := by exact prefixLift 6365642
  have htrace : WordTrace (prefixWord ++ tailWord_6365642) baseStart_6365642 baseEnd_6365642 := by
    simpa [prefixWord, tailWord_6365642, baseEnd_6365642] using wordTrace_append hprefix tailTrace_6365642
  have hstable : (prefixWord ++ tailWord_6365642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365642).length < 2 ^ (prefixWord ++ tailWord_6365642).sum := by decide
  have hdescent : baseEnd_6365642 < baseStart_6365642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365649 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_6365649 : Nat := 118140960795 + 6365649 * 2 ^ 59
def prefixEnd_6365649 : Nat := 4983230072969 + 3 ^ 40 * 6365649 * 2
def baseEnd_6365649 : Nat := 3268637614812470102712419

theorem tailTrace_6365649 : CollatzResearch.WordTrace tailWord_6365649 prefixEnd_6365649 3268637614812470102712419 := by
  unfold tailWord_6365649
  simp only [CollatzResearch.WordTrace]
  refine ⟨232174292915348314140580001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154782861943565542760386667 232174292915348314140580001)
  ·
    refine ⟨174130719686511235605435001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232174292915348314140580001 174130719686511235605435001)
    ·
      refine ⟨130598039764883426704076251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174130719686511235605435001 130598039764883426704076251)
      ·
        refine ⟨195897059647325140056114377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130598039764883426704076251 195897059647325140056114377)
        ·
          refine ⟨146922794735493855042085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195897059647325140056114377 146922794735493855042085783)
          ·
            refine ⟨220384192103240782563128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146922794735493855042085783 220384192103240782563128675)
            ·
              refine ⟨330576288154861173844693013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220384192103240782563128675 330576288154861173844693013)
              ·
                refine ⟨15495763507259117523969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 330576288154861173844693013 15495763507259117523969985)
                ·
                  refine ⟨11621822630444338142977489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15495763507259117523969985 11621822630444338142977489)
                  ·
                    refine ⟨8716366972833253607233117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11621822630444338142977489 8716366972833253607233117)
                    ·
                      refine ⟨3268637614812470102712419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8716366972833253607233117 3268637614812470102712419)
                      ·
                        rfl

theorem cell23_6365649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_6365649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365649 prefixEnd_6365649 := by exact prefixLift 6365649
  have htrace : WordTrace (prefixWord ++ tailWord_6365649) baseStart_6365649 baseEnd_6365649 := by
    simpa [prefixWord, tailWord_6365649, baseEnd_6365649] using wordTrace_append hprefix tailTrace_6365649
  have hstable : (prefixWord ++ tailWord_6365649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365649).length < 2 ^ (prefixWord ++ tailWord_6365649).sum := by decide
  have hdescent : baseEnd_6365649 < baseStart_6365649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365699 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 1, 5]
def baseStart_6365699 : Nat := 118140960795 + 6365699 * 2 ^ 59
def prefixEnd_6365699 : Nat := 4983230072969 + 3 ^ 40 * 6365699 * 2
def baseEnd_6365699 : Nat := 1089554429615064969029063

theorem tailTrace_6365699 : CollatzResearch.WordTrace tailWord_6365699 prefixEnd_6365699 1089554429615064969029063 := by
  unfold tailWord_6365699
  simp only [CollatzResearch.WordTrace]
  refine ⟨232176116565167172679900151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154784077710111448453266767 232176116565167172679900151)
  ·
    refine ⟨348264174847750759019850227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232176116565167172679900151 348264174847750759019850227)
    ·
      refine ⟨522396262271626138529775341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348264174847750759019850227 522396262271626138529775341)
      ·
        refine ⟨195898598351859801948665753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522396262271626138529775341 195898598351859801948665753)
        ·
          refine ⟨146923948763894851461499315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195898598351859801948665753 146923948763894851461499315)
          ·
            refine ⟨220385923145842277192248973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146923948763894851461499315 220385923145842277192248973)
            ·
              refine ⟨82644721179690853947093365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220385923145842277192248973 82644721179690853947093365)
              ·
                refine ⟨7747942610596017557540003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82644721179690853947093365 7747942610596017557540003)
                ·
                  refine ⟨11621913915894026336310005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747942610596017557540003 11621913915894026336310005)
                  ·
                    refine ⟨1089554429615064969029063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11621913915894026336310005 1089554429615064969029063)
                    ·
                      rfl

theorem cell23_6365699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 5].length) (baseStart_6365699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365699 prefixEnd_6365699 := by exact prefixLift 6365699
  have htrace : WordTrace (prefixWord ++ tailWord_6365699) baseStart_6365699 baseEnd_6365699 := by
    simpa [prefixWord, tailWord_6365699, baseEnd_6365699] using wordTrace_append hprefix tailTrace_6365699
  have hstable : (prefixWord ++ tailWord_6365699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365699).length < 2 ^ (prefixWord ++ tailWord_6365699).sum := by decide
  have hdescent : baseEnd_6365699 < baseStart_6365699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365729 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_6365729 : Nat := 118140960795 + 6365729 * 2 ^ 59
def prefixEnd_6365729 : Nat := 4983230072969 + 3 ^ 40 * 6365729 * 2
def baseEnd_6365729 : Nat := 1089559564421609929904017

theorem tailTrace_6365729 : CollatzResearch.WordTrace tailWord_6365729 prefixEnd_6365729 1089559564421609929904017 := by
  unfold tailWord_6365729
  simp only [CollatzResearch.WordTrace]
  refine ⟨232177210755058487803492241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154784807170038991868994827 232177210755058487803492241)
  ·
    refine ⟨174132908066293865852619181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232177210755058487803492241 174132908066293865852619181)
    ·
      refine ⟨65299840524860199694732193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174132908066293865852619181 65299840524860199694732193)
      ·
        refine ⟨48974880393645149771049145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65299840524860199694732193 48974880393645149771049145)
        ·
          refine ⟨36731160295233862328286859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48974880393645149771049145 36731160295233862328286859)
          ·
            refine ⟨55096740442850793492430289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36731160295233862328286859 55096740442850793492430289)
            ·
              refine ⟨41322555332138095119322717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55096740442850793492430289 41322555332138095119322717)
              ·
                refine ⟨15495958249551785669746019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41322555332138095119322717 15495958249551785669746019)
                ·
                  refine ⟨23243937374327678504619029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15495958249551785669746019 23243937374327678504619029)
                  ·
                    refine ⟨1089559564421609929904017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23243937374327678504619029 1089559564421609929904017)
                    ·
                      rfl

theorem cell23_6365729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_6365729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365729 prefixEnd_6365729 := by exact prefixLift 6365729
  have htrace : WordTrace (prefixWord ++ tailWord_6365729) baseStart_6365729 baseEnd_6365729 := by
    simpa [prefixWord, tailWord_6365729, baseEnd_6365729] using wordTrace_append hprefix tailTrace_6365729
  have hstable : (prefixWord ++ tailWord_6365729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365729).length < 2 ^ (prefixWord ++ tailWord_6365729).sum := by decide
  have hdescent : baseEnd_6365729 < baseStart_6365729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365750 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6365750 : Nat := 118140960795 + 6365750 * 2 ^ 59
def prefixEnd_6365750 : Nat := 4983230072969 + 3 ^ 40 * 6365750 * 2
def baseEnd_6365750 : Nat := 1089563158786191402516485

theorem tailTrace_6365750 : CollatzResearch.WordTrace tailWord_6365750 prefixEnd_6365750 1089563158786191402516485 := by
  unfold tailWord_6365750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511123542998900524375419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154785317791988272260004469 14511123542998900524375419)
  ·
    refine ⟨21766685314498350786563129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14511123542998900524375419 21766685314498350786563129)
    ·
      refine ⟨16325013985873763089922347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21766685314498350786563129 16325013985873763089922347)
      ·
        refine ⟨24487520978810644634883521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16325013985873763089922347 24487520978810644634883521)
        ·
          refine ⟨18365640734107983476162641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24487520978810644634883521 18365640734107983476162641)
          ·
            refine ⟨13774230550580987607121981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18365640734107983476162641 13774230550580987607121981)
            ·
              refine ⟨5165336456467870352670743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13774230550580987607121981 5165336456467870352670743)
              ·
                refine ⟨7748004684701805529006115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165336456467870352670743 7748004684701805529006115)
                ·
                  refine ⟨11622007027052708293509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748004684701805529006115 11622007027052708293509173)
                  ·
                    refine ⟨1089563158786191402516485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11622007027052708293509173 1089563158786191402516485)
                    ·
                      rfl

theorem cell23_6365750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6365750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365750 prefixEnd_6365750 := by exact prefixLift 6365750
  have htrace : WordTrace (prefixWord ++ tailWord_6365750) baseStart_6365750 baseEnd_6365750 := by
    simpa [prefixWord, tailWord_6365750, baseEnd_6365750] using wordTrace_append hprefix tailTrace_6365750
  have hstable : (prefixWord ++ tailWord_6365750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365750).length < 2 ^ (prefixWord ++ tailWord_6365750).sum := by decide
  have hdescent : baseEnd_6365750 < baseStart_6365750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365753 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6365753 : Nat := 118140960795 + 6365753 * 2 ^ 59
def prefixEnd_6365753 : Nat := 4983230072969 + 3 ^ 40 * 6365753 * 2
def baseEnd_6365753 : Nat := 3268691016800537695811941

theorem tailTrace_6365753 : CollatzResearch.WordTrace tailWord_6365753 prefixEnd_6365753 3268691016800537695811941 := by
  unfold tailWord_6365753
  simp only [CollatzResearch.WordTrace]
  refine ⟨232178086106971539902365913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154785390737981026601577275 232178086106971539902365913)
  ·
    refine ⟨174133564580228654926774435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232178086106971539902365913 174133564580228654926774435)
    ·
      refine ⟨261200346870342982390161653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174133564580228654926774435 261200346870342982390161653)
      ·
        refine ⟨24487532519094654599077655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261200346870342982390161653 24487532519094654599077655)
        ·
          refine ⟨36731298778641981898616483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24487532519094654599077655 36731298778641981898616483)
          ·
            refine ⟨55096948167962972847924725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36731298778641981898616483 55096948167962972847924725)
            ·
              refine ⟨5165338890746528704492943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55096948167962972847924725 5165338890746528704492943)
              ·
                refine ⟨7748008336119793056739415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165338890746528704492943 7748008336119793056739415)
                ·
                  refine ⟨11622012504179689585109123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748008336119793056739415 11622012504179689585109123)
                  ·
                    refine ⟨17433018756269534377663685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11622012504179689585109123 17433018756269534377663685)
                    ·
                      refine ⟨3268691016800537695811941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17433018756269534377663685 3268691016800537695811941)
                      ·
                        rfl

theorem cell23_6365753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6365753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365753 prefixEnd_6365753 := by exact prefixLift 6365753
  have htrace : WordTrace (prefixWord ++ tailWord_6365753) baseStart_6365753 baseEnd_6365753 := by
    simpa [prefixWord, tailWord_6365753, baseEnd_6365753] using wordTrace_append hprefix tailTrace_6365753
  have hstable : (prefixWord ++ tailWord_6365753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365753).length < 2 ^ (prefixWord ++ tailWord_6365753).sum := by decide
  have hdescent : baseEnd_6365753 < baseStart_6365753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365756 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_6365756 : Nat := 118140960795 + 6365756 * 2 ^ 59
def prefixEnd_6365756 : Nat := 4983230072969 + 3 ^ 40 * 6365756 * 2
def baseEnd_6365756 : Nat := 3268692557242501184074427

theorem tailTrace_6365756 : CollatzResearch.WordTrace tailWord_6365756 prefixEnd_6365756 3268692557242501184074427 := by
  unfold tailWord_6365756
  simp only [CollatzResearch.WordTrace]
  refine ⟨116089097762980335707362561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154785463683973780943150081 116089097762980335707362561)
  ·
    refine ⟨87066823322235251780521921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116089097762980335707362561 87066823322235251780521921)
    ·
      refine ⟨65300117491676438835391441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87066823322235251780521921 65300117491676438835391441)
      ·
        refine ⟨48975088118757329126543581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65300117491676438835391441 48975088118757329126543581)
        ·
          refine ⟨18365658044533998422453843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48975088118757329126543581 18365658044533998422453843)
          ·
            refine ⟨27548487066800997633680765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18365658044533998422453843 27548487066800997633680765)
            ·
              refine ⟨10330682650050374112630287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27548487066800997633680765 10330682650050374112630287)
              ·
                refine ⟨15496023975075561168945431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10330682650050374112630287 15496023975075561168945431)
                ·
                  refine ⟨23244035962613341753418147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15496023975075561168945431 23244035962613341753418147)
                  ·
                    refine ⟨34866053943920012630127221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23244035962613341753418147 34866053943920012630127221)
                    ·
                      refine ⟨3268692557242501184074427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34866053943920012630127221 3268692557242501184074427)
                      ·
                        rfl

theorem cell23_6365756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_6365756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365756 prefixEnd_6365756 := by exact prefixLift 6365756
  have htrace : WordTrace (prefixWord ++ tailWord_6365756) baseStart_6365756 baseEnd_6365756 := by
    simpa [prefixWord, tailWord_6365756, baseEnd_6365756] using wordTrace_append hprefix tailTrace_6365756
  have hstable : (prefixWord ++ tailWord_6365756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365756).length < 2 ^ (prefixWord ++ tailWord_6365756).sum := by decide
  have hdescent : baseEnd_6365756 < baseStart_6365756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365773 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6365773 : Nat := 118140960795 + 6365773 * 2 ^ 59
def prefixEnd_6365773 : Nat := 4983230072969 + 3 ^ 40 * 6365773 * 2
def baseEnd_6365773 : Nat := 3268701286413627617561849

theorem tailTrace_6365773 : CollatzResearch.WordTrace tailWord_6365773 prefixEnd_6365773 3268701286413627617561849 := by
  unfold tailWord_6365773
  simp only [CollatzResearch.WordTrace]
  refine ⟨232178815566899083318093973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154785877044599388878729315 232178815566899083318093973)
  ·
    refine ⟨10883381979698394530535655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232178815566899083318093973 10883381979698394530535655)
    ·
      refine ⟨16325072969547591795803483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10883381979698394530535655 16325072969547591795803483)
      ·
        refine ⟨24487609454321387693705225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16325072969547591795803483 24487609454321387693705225)
        ·
          refine ⟨18365707090741040770278919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24487609454321387693705225 18365707090741040770278919)
          ·
            refine ⟨27548560636111561155418379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18365707090741040770278919 27548560636111561155418379)
            ·
              refine ⟨41322840954167341733127569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27548560636111561155418379 41322840954167341733127569)
              ·
                refine ⟨30992130715625506299845677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41322840954167341733127569 30992130715625506299845677)
                ·
                  refine ⟨11622049018359564862442129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30992130715625506299845677 11622049018359564862442129)
                  ·
                    refine ⟨8716536763769673646831597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11622049018359564862442129 8716536763769673646831597)
                    ·
                      refine ⟨3268701286413627617561849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8716536763769673646831597 3268701286413627617561849)
                      ·
                        rfl

theorem cell23_6365773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6365773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365773 prefixEnd_6365773 := by exact prefixLift 6365773
  have htrace : WordTrace (prefixWord ++ tailWord_6365773) baseStart_6365773 baseEnd_6365773 := by
    simpa [prefixWord, tailWord_6365773, baseEnd_6365773] using wordTrace_append hprefix tailTrace_6365773
  have hstable : (prefixWord ++ tailWord_6365773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365773).length < 2 ^ (prefixWord ++ tailWord_6365773).sum := by decide
  have hdescent : baseEnd_6365773 < baseStart_6365773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365786 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_6365786 : Nat := 118140960795 + 6365786 * 2 ^ 59
def prefixEnd_6365786 : Nat := 4983230072969 + 3 ^ 40 * 6365786 * 2
def baseEnd_6365786 : Nat := 3268707961662136066699289

theorem tailTrace_6365786 : CollatzResearch.WordTrace tailWord_6365786 prefixEnd_6365786 3268707961662136066699289 := by
  unfold tailWord_6365786
  simp only [CollatzResearch.WordTrace]
  refine ⟨58044822428962996634579303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154786193143901324358878141 58044822428962996634579303)
  ·
    refine ⟨87067233643444494951868955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58044822428962996634579303 87067233643444494951868955)
    ·
      refine ⟨130600850465166742427803433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87067233643444494951868955 130600850465166742427803433)
      ·
        refine ⟨97950637848875056820852575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130600850465166742427803433 97950637848875056820852575)
        ·
          refine ⟨146925956773312585231278863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97950637848875056820852575 146925956773312585231278863)
          ·
            refine ⟨220388935159968877846918295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146925956773312585231278863 220388935159968877846918295)
            ·
              refine ⟨330583402739953316770377443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220388935159968877846918295 330583402739953316770377443)
              ·
                refine ⟨495875104109929975155566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330583402739953316770377443 495875104109929975155566165)
                ·
                  refine ⟨5811036376288241896354291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 495875104109929975155566165 5811036376288241896354291)
                  ·
                    refine ⟨8716554564432362844531437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5811036376288241896354291 8716554564432362844531437)
                    ·
                      refine ⟨3268707961662136066699289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8716554564432362844531437 3268707961662136066699289)
                      ·
                        rfl

theorem cell23_6365786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_6365786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365786 prefixEnd_6365786 := by exact prefixLift 6365786
  have htrace : WordTrace (prefixWord ++ tailWord_6365786) baseStart_6365786 baseEnd_6365786 := by
    simpa [prefixWord, tailWord_6365786, baseEnd_6365786] using wordTrace_append hprefix tailTrace_6365786
  have hstable : (prefixWord ++ tailWord_6365786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365786).length < 2 ^ (prefixWord ++ tailWord_6365786).sum := by decide
  have hdescent : baseEnd_6365786 < baseStart_6365786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365799 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6365799 : Nat := 118140960795 + 6365799 * 2 ^ 59
def prefixEnd_6365799 : Nat := 4983230072969 + 3 ^ 40 * 6365799 * 2
def baseEnd_6365799 : Nat := 3268714636910644515836729

theorem tailTrace_6365799 : CollatzResearch.WordTrace tailWord_6365799 prefixEnd_6365799 3268714636910644515836729 := by
  unfold tailWord_6365799
  simp only [CollatzResearch.WordTrace]
  refine ⟨232179763864804889758540451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154786509243203259839026967 232179763864804889758540451)
  ·
    refine ⟨348269645797207334637810677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232179763864804889758540451 348269645797207334637810677)
    ·
      refine ⟨32650279293488187622294751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 348269645797207334637810677 32650279293488187622294751)
      ·
        refine ⟨48975418940232281433442127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32650279293488187622294751 48975418940232281433442127)
        ·
          refine ⟨73463128410348422150163191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48975418940232281433442127 73463128410348422150163191)
          ·
            refine ⟨110194692615522633225244787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73463128410348422150163191 110194692615522633225244787)
            ·
              refine ⟨165292038923283949837867181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110194692615522633225244787 165292038923283949837867181)
              ·
                refine ⟨61984514596231481189200193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165292038923283949837867181 61984514596231481189200193)
                ·
                  refine ⟨46488385947173610891900145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61984514596231481189200193 46488385947173610891900145)
                  ·
                    refine ⟨34866289460380208168925109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46488385947173610891900145 34866289460380208168925109)
                    ·
                      refine ⟨3268714636910644515836729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34866289460380208168925109 3268714636910644515836729)
                      ·
                        rfl

theorem cell23_6365799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6365799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365799 prefixEnd_6365799 := by exact prefixLift 6365799
  have htrace : WordTrace (prefixWord ++ tailWord_6365799) baseStart_6365799 baseEnd_6365799 := by
    simpa [prefixWord, tailWord_6365799, baseEnd_6365799] using wordTrace_append hprefix tailTrace_6365799
  have hstable : (prefixWord ++ tailWord_6365799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365799).length < 2 ^ (prefixWord ++ tailWord_6365799).sum := by decide
  have hdescent : baseEnd_6365799 < baseStart_6365799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365849 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 7]
def baseStart_6365849 : Nat := 118140960795 + 6365849 * 2 ^ 59
def prefixEnd_6365849 : Nat := 4983230072969 + 3 ^ 40 * 6365849 * 2
def baseEnd_6365849 : Nat := 363193367882596591134611

theorem tailTrace_6365849 : CollatzResearch.WordTrace tailWord_6365849 prefixEnd_6365849 363193367882596591134611 := by
  unfold tailWord_6365849
  simp only [CollatzResearch.WordTrace]
  refine ⟨232181587514623748297860601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154787725009749165531907067 232181587514623748297860601)
  ·
    refine ⟨174136190635967811223395451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232181587514623748297860601 174136190635967811223395451)
    ·
      refine ⟨261204285953951716835093177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174136190635967811223395451 261204285953951716835093177)
      ·
        refine ⟨195903214465463787626319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261204285953951716835093177 195903214465463787626319883)
        ·
          refine ⟨293854821698195681439479825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195903214465463787626319883 293854821698195681439479825)
          ·
            refine ⟨220391116273646761079609869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293854821698195681439479825 220391116273646761079609869)
            ·
              refine ⟨82646668602617535404853701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220391116273646761079609869 82646668602617535404853701)
              ·
                refine ⟨15496250362990787888410069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82646668602617535404853701 15496250362990787888410069)
                ·
                  refine ⟨363193367882596591134611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15496250362990787888410069 363193367882596591134611)
                  ·
                    rfl

theorem cell23_6365849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_6365849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365849 prefixEnd_6365849 := by exact prefixLift 6365849
  have htrace : WordTrace (prefixWord ++ tailWord_6365849) baseStart_6365849 baseEnd_6365849 := by
    simpa [prefixWord, tailWord_6365849, baseEnd_6365849] using wordTrace_append hprefix tailTrace_6365849
  have hstable : (prefixWord ++ tailWord_6365849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365849).length < 2 ^ (prefixWord ++ tailWord_6365849).sum := by decide
  have hdescent : baseEnd_6365849 < baseStart_6365849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365933 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6365933 : Nat := 118140960795 + 6365933 * 2 ^ 59
def prefixEnd_6365933 : Nat := 4983230072969 + 3 ^ 40 * 6365933 * 2
def baseEnd_6365933 : Nat := 3268783443318346991561113

theorem tailTrace_6365933 : CollatzResearch.WordTrace tailWord_6365933 prefixEnd_6365933 3268783443318346991561113 := by
  unfold tailWord_6365933
  simp only [CollatzResearch.WordTrace]
  refine ⟨232184651246319430643918453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154789767497546287095945635 232184651246319430643918453)
  ·
    refine ⟨21767311054342446622867355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232184651246319430643918453 21767311054342446622867355)
    ·
      refine ⟨32650966581513669934301033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21767311054342446622867355 32650966581513669934301033)
      ·
        refine ⟨24488224936135252450725775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32650966581513669934301033 24488224936135252450725775)
        ·
          refine ⟨36732337404202878676088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24488224936135252450725775 36732337404202878676088663)
          ·
            refine ⟨55098506106304318014132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36732337404202878676088663 55098506106304318014132995)
            ·
              refine ⟨82647759159456477021199493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55098506106304318014132995 82647759159456477021199493)
              ·
                refine ⟨15496454842398089441474905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82647759159456477021199493 15496454842398089441474905)
                ·
                  refine ⟨11622341131798567081106179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15496454842398089441474905 11622341131798567081106179)
                  ·
                    refine ⟨17433511697697850621659269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11622341131798567081106179 17433511697697850621659269)
                    ·
                      refine ⟨3268783443318346991561113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17433511697697850621659269 3268783443318346991561113)
                      ·
                        rfl

theorem cell23_6365933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6365933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365933 prefixEnd_6365933 := by exact prefixLift 6365933
  have htrace : WordTrace (prefixWord ++ tailWord_6365933) baseStart_6365933 baseEnd_6365933 := by
    simpa [prefixWord, tailWord_6365933, baseEnd_6365933] using wordTrace_append hprefix tailTrace_6365933
  have hstable : (prefixWord ++ tailWord_6365933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365933).length < 2 ^ (prefixWord ++ tailWord_6365933).sum := by decide
  have hdescent : baseEnd_6365933 < baseStart_6365933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6365950 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6365950 : Nat := 118140960795 + 6365950 * 2 ^ 59
def prefixEnd_6365950 : Nat := 4983230072969 + 3 ^ 40 * 6365950 * 2
def baseEnd_6365950 : Nat := 3268792172489473425048535

theorem tailTrace_6365950 : CollatzResearch.WordTrace tailWord_6365950 prefixEnd_6365950 3268792172489473425048535 := by
  unfold tailWord_6365950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023158910907230318410913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154790180858171895031524869 29023158910907230318410913)
  ·
    refine ⟨21767369183180422738808185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29023158910907230318410913 21767369183180422738808185)
    ·
      refine ⟨16325526887385317054106139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21767369183180422738808185 16325526887385317054106139)
      ·
        refine ⟨24488290331077975581159209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16325526887385317054106139 24488290331077975581159209)
        ·
          refine ⟨18366217748308481685869407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24488290331077975581159209 18366217748308481685869407)
          ·
            refine ⟨27549326622462722528804111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366217748308481685869407 27549326622462722528804111)
            ·
              refine ⟨41323989933694083793206167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27549326622462722528804111 41323989933694083793206167)
              ·
                refine ⟨61985984900541125689809251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41323989933694083793206167 61985984900541125689809251)
                ·
                  refine ⟨92978977350811688534713877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61985984900541125689809251 92978977350811688534713877)
                  ·
                    refine ⟨4358389563319297900064713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92978977350811688534713877 4358389563319297900064713)
                    ·
                      refine ⟨3268792172489473425048535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358389563319297900064713 3268792172489473425048535)
                      ·
                        rfl

theorem cell23_6365950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6365950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6365950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6365950 prefixEnd_6365950 := by exact prefixLift 6365950
  have htrace : WordTrace (prefixWord ++ tailWord_6365950) baseStart_6365950 baseEnd_6365950 := by
    simpa [prefixWord, tailWord_6365950, baseEnd_6365950] using wordTrace_append hprefix tailTrace_6365950
  have hstable : (prefixWord ++ tailWord_6365950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6365950).length < 2 ^ (prefixWord ++ tailWord_6365950).sum := by decide
  have hdescent : baseEnd_6365950 < baseStart_6365950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6365950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366023 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_6366023 : Nat := 118140960795 + 6366023 * 2 ^ 59
def prefixEnd_6366023 : Nat := 4983230072969 + 3 ^ 40 * 6366023 * 2
def baseEnd_6366023 : Nat := 3268829656577251639435699

theorem tailTrace_6366023 : CollatzResearch.WordTrace tailWord_6366023 prefixEnd_6366023 3268829656577251639435699 := by
  unfold tailWord_6366023
  simp only [CollatzResearch.WordTrace]
  refine ⟨232187933815993376014694723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154791955877328917343129815 232187933815993376014694723)
  ·
    refine ⟨348281900723990064022042085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232187933815993376014694723 348281900723990064022042085)
    ·
      refine ⟨65302856385748137004132891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348281900723990064022042085 65302856385748137004132891)
      ·
        refine ⟨97954284578622205506199337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65302856385748137004132891 97954284578622205506199337)
        ·
          refine ⟨73465713433966654129649503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97954284578622205506199337 73465713433966654129649503)
          ·
            refine ⟨110198570150949981194474255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73465713433966654129649503 110198570150949981194474255)
            ·
              refine ⟨165297855226424971791711383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110198570150949981194474255 165297855226424971791711383)
              ·
                refine ⟨247946782839637457687567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165297855226424971791711383 247946782839637457687567075)
                ·
                  refine ⟨371920174259456186531350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247946782839637457687567075 371920174259456186531350613)
                  ·
                    refine ⟨4358439542103002185914265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 371920174259456186531350613 4358439542103002185914265)
                    ·
                      refine ⟨3268829656577251639435699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358439542103002185914265 3268829656577251639435699)
                      ·
                        rfl

theorem cell23_6366023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_6366023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366023 prefixEnd_6366023 := by exact prefixLift 6366023
  have htrace : WordTrace (prefixWord ++ tailWord_6366023) baseStart_6366023 baseEnd_6366023 := by
    simpa [prefixWord, tailWord_6366023, baseEnd_6366023] using wordTrace_append hprefix tailTrace_6366023
  have hstable : (prefixWord ++ tailWord_6366023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366023).length < 2 ^ (prefixWord ++ tailWord_6366023).sum := by decide
  have hdescent : baseEnd_6366023 < baseStart_6366023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366040 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_6366040 : Nat := 118140960795 + 6366040 * 2 ^ 59
def prefixEnd_6366040 : Nat := 4983230072969 + 3 ^ 40 * 6366040 * 2
def baseEnd_6366040 : Nat := 3268838385748378072923121

theorem tailTrace_6366040 : CollatzResearch.WordTrace tailWord_6366040 prefixEnd_6366040 3268838385748378072923121 := by
  unfold tailWord_6366040
  simp only [CollatzResearch.WordTrace]
  refine ⟨116094276928465893959031787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154792369237954525278709049 116094276928465893959031787)
  ·
    refine ⟨174141415392698840938547681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116094276928465893959031787 174141415392698840938547681)
    ·
      refine ⟨130606061544524130703910761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174141415392698840938547681 130606061544524130703910761)
      ·
        refine ⟨97954546158393098027933071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130606061544524130703910761 97954546158393098027933071)
        ·
          refine ⟨146931819237589647041899607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97954546158393098027933071 146931819237589647041899607)
          ·
            refine ⟨220397728856384470562849411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146931819237589647041899607 220397728856384470562849411)
            ·
              refine ⟨330596593284576705844274117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220397728856384470562849411 330596593284576705844274117)
              ·
                refine ⟨61986861240858132345801397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330596593284576705844274117 61986861240858132345801397)
                ·
                  refine ⟨5811268241330449907418881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61986861240858132345801397 5811268241330449907418881)
                  ·
                    refine ⟨4358451180997837430564161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5811268241330449907418881 4358451180997837430564161)
                    ·
                      refine ⟨3268838385748378072923121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358451180997837430564161 3268838385748378072923121)
                      ·
                        rfl

theorem cell23_6366040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_6366040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366040 prefixEnd_6366040 := by exact prefixLift 6366040
  have htrace : WordTrace (prefixWord ++ tailWord_6366040) baseStart_6366040 baseEnd_6366040 := by
    simpa [prefixWord, tailWord_6366040, baseEnd_6366040] using wordTrace_append hprefix tailTrace_6366040
  have hstable : (prefixWord ++ tailWord_6366040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366040).length < 2 ^ (prefixWord ++ tailWord_6366040).sum := by decide
  have hdescent : baseEnd_6366040 < baseStart_6366040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366070 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6366070 : Nat := 118140960795 + 6366070 * 2 ^ 59
def prefixEnd_6366070 : Nat := 4983230072969 + 3 ^ 40 * 6366070 * 2
def baseEnd_6366070 : Nat := 3268853790168012955547983

theorem tailTrace_6366070 : CollatzResearch.WordTrace tailWord_6366070 prefixEnd_6366070 3268853790168012955547983 := by
  unfold tailWord_6366070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511853002926443940103479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154793098697882068694437109 14511853002926443940103479)
  ·
    refine ⟨21767779504389665910155219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14511853002926443940103479 21767779504389665910155219)
    ·
      refine ⟨32651669256584498865232829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21767779504389665910155219 32651669256584498865232829)
      ·
        refine ⟨12244375971219187074462311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32651669256584498865232829 12244375971219187074462311)
        ·
          refine ⟨18366563956828780611693467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244375971219187074462311 18366563956828780611693467)
          ·
            refine ⟨27549845935243170917540201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366563956828780611693467 27549845935243170917540201)
            ·
              refine ⟨20662384451432378188155151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27549845935243170917540201 20662384451432378188155151)
              ·
                refine ⟨30993576677148567282232727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20662384451432378188155151 30993576677148567282232727)
                ·
                  refine ⟨46490365015722850923349091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30993576677148567282232727 46490365015722850923349091)
                  ·
                    refine ⟨69735547523584276385023637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46490365015722850923349091 69735547523584276385023637)
                    ·
                      refine ⟨3268853790168012955547983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69735547523584276385023637 3268853790168012955547983)
                      ·
                        rfl

theorem cell23_6366070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6366070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366070 prefixEnd_6366070 := by exact prefixLift 6366070
  have htrace : WordTrace (prefixWord ++ tailWord_6366070) baseStart_6366070 baseEnd_6366070 := by
    simpa [prefixWord, tailWord_6366070, baseEnd_6366070] using wordTrace_append hprefix tailTrace_6366070
  have hstable : (prefixWord ++ tailWord_6366070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366070).length < 2 ^ (prefixWord ++ tailWord_6366070).sum := by decide
  have hdescent : baseEnd_6366070 < baseStart_6366070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366090 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6366090 : Nat := 118140960795 + 6366090 * 2 ^ 59
def prefixEnd_6366090 : Nat := 4983230072969 + 3 ^ 40 * 6366090 * 2
def baseEnd_6366090 : Nat := 3268864059781102877297891

theorem tailTrace_6366090 : CollatzResearch.WordTrace tailWord_6366090 prefixEnd_6366090 3268864059781102877297891 := by
  unfold tailWord_6366090
  simp only [CollatzResearch.WordTrace]
  refine ⟨58047594376687661614345931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154793585004500430971589149 58047594376687661614345931)
  ·
    refine ⟨87071391565031492421518897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58047594376687661614345931 87071391565031492421518897)
    ·
      refine ⟨65303543673773619316139173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87071391565031492421518897 65303543673773619316139173)
      ·
        refine ⟨12244414438832553621776095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65303543673773619316139173 12244414438832553621776095)
        ·
          refine ⟨18366621658248830432664143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244414438832553621776095 18366621658248830432664143)
          ·
            refine ⟨27549932487373245648996215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366621658248830432664143 27549932487373245648996215)
            ·
              refine ⟨41324898731059868473494323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27549932487373245648996215 41324898731059868473494323)
              ·
                refine ⟨61987348096589802710241485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41324898731059868473494323 61987348096589802710241485)
                ·
                  refine ⟨23245255536221176016340557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61987348096589802710241485 23245255536221176016340557)
                  ·
                    refine ⟨8716970826082941006127709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23245255536221176016340557 8716970826082941006127709)
                    ·
                      refine ⟨3268864059781102877297891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8716970826082941006127709 3268864059781102877297891)
                      ·
                        rfl

theorem cell23_6366090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6366090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366090 prefixEnd_6366090 := by exact prefixLift 6366090
  have htrace : WordTrace (prefixWord ++ tailWord_6366090) baseStart_6366090 baseEnd_6366090 := by
    simpa [prefixWord, tailWord_6366090, baseEnd_6366090] using wordTrace_append hprefix tailTrace_6366090
  have hstable : (prefixWord ++ tailWord_6366090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366090).length < 2 ^ (prefixWord ++ tailWord_6366090).sum := by decide
  have hdescent : baseEnd_6366090 < baseStart_6366090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366164 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6366164 : Nat := 118140960795 + 6366164 * 2 ^ 59
def prefixEnd_6366164 : Nat := 4983230072969 + 3 ^ 40 * 6366164 * 2
def baseEnd_6366164 : Nat := 3268902057349535587772551

theorem tailTrace_6366164 : CollatzResearch.WordTrace tailWord_6366164 prefixEnd_6366164 3268902057349535587772551 := by
  unfold tailWord_6366164
  simp only [CollatzResearch.WordTrace]
  refine ⟨116096538254241278547788773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154795384338988371397051697 116096538254241278547788773)
  ·
    refine ⟨21768100922670239727710395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116096538254241278547788773 21768100922670239727710395)
    ·
      refine ⟨32652151384005359591565593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21768100922670239727710395 32652151384005359591565593)
      ·
        refine ⟨24489113538004019693674195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32652151384005359591565593 24489113538004019693674195)
        ·
          refine ⟨36733670307006029540511293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489113538004019693674195 36733670307006029540511293)
          ·
            refine ⟨13775126365127261077691735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36733670307006029540511293 13775126365127261077691735)
            ·
              refine ⟨20662689547690891616537603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775126365127261077691735 20662689547690891616537603)
              ·
                refine ⟨30994034321536337424806405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20662689547690891616537603 30994034321536337424806405)
                ·
                  refine ⟨5811381435288063267151201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30994034321536337424806405 5811381435288063267151201)
                  ·
                    refine ⟨4358536076466047450363401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5811381435288063267151201 4358536076466047450363401)
                    ·
                      refine ⟨3268902057349535587772551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358536076466047450363401 3268902057349535587772551)
                      ·
                        rfl

theorem cell23_6366164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6366164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366164 prefixEnd_6366164 := by exact prefixLift 6366164
  have htrace : WordTrace (prefixWord ++ tailWord_6366164) baseStart_6366164 baseEnd_6366164 := by
    simpa [prefixWord, tailWord_6366164, baseEnd_6366164] using wordTrace_append hprefix tailTrace_6366164
  have hstable : (prefixWord ++ tailWord_6366164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366164).length < 2 ^ (prefixWord ++ tailWord_6366164).sum := by decide
  have hdescent : baseEnd_6366164 < baseStart_6366164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366170 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_6366170 : Nat := 118140960795 + 6366170 * 2 ^ 59
def prefixEnd_6366170 : Nat := 4983230072969 + 3 ^ 40 * 6366170 * 2
def baseEnd_6366170 : Nat := 363211682025940284921947

theorem tailTrace_6366170 : CollatzResearch.WordTrace tailWord_6366170 prefixEnd_6366170 363211682025940284921947 := by
  unfold tailWord_6366170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58048323836615205030073991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154795530230973880080197309 58048323836615205030073991)
  ·
    refine ⟨87072485754922807545110987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58048323836615205030073991 87072485754922807545110987)
    ·
      refine ⟨130608728632384211317666481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87072485754922807545110987 130608728632384211317666481)
      ·
        refine ⟨97956546474288158488249861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130608728632384211317666481 97956546474288158488249861)
        ·
          refine ⟨18366852463929029716546849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97956546474288158488249861 18366852463929029716546849)
          ·
            refine ⟨13775139347946772287410137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18366852463929029716546849 13775139347946772287410137)
            ·
              refine ⟨10331354510960079215557603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13775139347946772287410137 10331354510960079215557603)
              ·
                refine ⟨15497031766440118823336405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331354510960079215557603 15497031766440118823336405)
                ·
                  refine ⟨363211682025940284921947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15497031766440118823336405 363211682025940284921947)
                  ·
                    rfl

theorem cell23_6366170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_6366170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366170 prefixEnd_6366170 := by exact prefixLift 6366170
  have htrace : WordTrace (prefixWord ++ tailWord_6366170) baseStart_6366170 baseEnd_6366170 := by
    simpa [prefixWord, tailWord_6366170, baseEnd_6366170] using wordTrace_append hprefix tailTrace_6366170
  have hstable : (prefixWord ++ tailWord_6366170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366170).length < 2 ^ (prefixWord ++ tailWord_6366170).sum := by decide
  have hdescent : baseEnd_6366170 < baseStart_6366170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366181 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6366181 : Nat := 118140960795 + 6366181 * 2 ^ 59
def prefixEnd_6366181 : Nat := 4983230072969 + 3 ^ 40 * 6366181 * 2
def baseEnd_6366181 : Nat := 3268910786520662021259973

theorem tailTrace_6366181 : CollatzResearch.WordTrace tailWord_6366181 prefixEnd_6366181 3268910786520662021259973 := by
  unfold tailWord_6366181
  simp only [CollatzResearch.WordTrace]
  refine ⟨232193696549420968998946397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154795797699613979332630931 232193696549420968998946397)
  ·
    refine ⟨87072636206032863374604899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232193696549420968998946397 87072636206032863374604899)
    ·
      refine ⟨130608954309049295061907349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87072636206032863374604899 130608954309049295061907349)
      ·
        refine ⟨6122294733236685706026907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130608954309049295061907349 6122294733236685706026907)
        ·
          refine ⟨9183442099855028559040361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122294733236685706026907 9183442099855028559040361)
          ·
            refine ⟨6887581574891271419280271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9183442099855028559040361 6887581574891271419280271)
            ·
              refine ⟨10331372362336907128920407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887581574891271419280271 10331372362336907128920407)
              ·
                refine ⟨15497058543505360693380611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331372362336907128920407 15497058543505360693380611)
                ·
                  refine ⟨23245587815258041040070917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15497058543505360693380611 23245587815258041040070917)
                  ·
                    refine ⟨4358547715360882695013297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23245587815258041040070917 4358547715360882695013297)
                    ·
                      refine ⟨3268910786520662021259973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358547715360882695013297 3268910786520662021259973)
                      ·
                        rfl

theorem cell23_6366181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6366181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366181 prefixEnd_6366181 := by exact prefixLift 6366181
  have htrace : WordTrace (prefixWord ++ tailWord_6366181) baseStart_6366181 baseEnd_6366181 := by
    simpa [prefixWord, tailWord_6366181, baseEnd_6366181] using wordTrace_append hprefix tailTrace_6366181
  have hstable : (prefixWord ++ tailWord_6366181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366181).length < 2 ^ (prefixWord ++ tailWord_6366181).sum := by decide
  have hdescent : baseEnd_6366181 < baseStart_6366181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366220 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6366220 : Nat := 118140960795 + 6366220 * 2 ^ 59
def prefixEnd_6366220 : Nat := 4983230072969 + 3 ^ 40 * 6366220 * 2
def baseEnd_6366220 : Nat := 3268930812266187368672293

theorem tailTrace_6366220 : CollatzResearch.WordTrace tailWord_6366220 prefixEnd_6366220 3268930812266187368672293 := by
  unfold tailWord_6366220
  simp only [CollatzResearch.WordTrace]
  refine ⟨116097559498139839329808057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154796745997519785773077409 116097559498139839329808057)
  ·
    refine ⟨87073169623604879497356043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116097559498139839329808057 87073169623604879497356043)
    ·
      refine ⟨130609754435407319246034065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87073169623604879497356043 130609754435407319246034065)
      ·
        refine ⟨97957315826555489434525549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130609754435407319246034065 97957315826555489434525549)
        ·
          refine ⟨36733993434958308537947081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97957315826555489434525549 36733993434958308537947081)
          ·
            refine ⟨27550495076218731403460311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36733993434958308537947081 27550495076218731403460311)
            ·
              refine ⟨41325742614328097105190467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27550495076218731403460311 41325742614328097105190467)
              ·
                refine ⟨61988613921492145657785701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41325742614328097105190467 61988613921492145657785701)
                ·
                  refine ⟨11622865110279777310834819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61988613921492145657785701 11622865110279777310834819)
                  ·
                    refine ⟨17434297665419665966252229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11622865110279777310834819 17434297665419665966252229)
                    ·
                      refine ⟨3268930812266187368672293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17434297665419665966252229 3268930812266187368672293)
                      ·
                        rfl

theorem cell23_6366220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6366220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366220 prefixEnd_6366220 := by exact prefixLift 6366220
  have htrace : WordTrace (prefixWord ++ tailWord_6366220) baseStart_6366220 baseEnd_6366220 := by
    simpa [prefixWord, tailWord_6366220, baseEnd_6366220] using wordTrace_append hprefix tailTrace_6366220
  have hstable : (prefixWord ++ tailWord_6366220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366220).length < 2 ^ (prefixWord ++ tailWord_6366220).sum := by decide
  have hdescent : baseEnd_6366220 < baseStart_6366220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366233 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_6366233 : Nat := 118140960795 + 6366233 * 2 ^ 59
def prefixEnd_6366233 : Nat := 4983230072969 + 3 ^ 40 * 6366233 * 2
def baseEnd_6366233 : Nat := 3268937487514695817809733

theorem tailTrace_6366233 : CollatzResearch.WordTrace tailWord_6366233 prefixEnd_6366233 3268937487514695817809733 := by
  unfold tailWord_6366233
  simp only [CollatzResearch.WordTrace]
  refine ⟨232195593145232581879839353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154797062096821721253226235 232195593145232581879839353)
  ·
    refine ⟨174146694858924436409879515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232195593145232581879839353 174146694858924436409879515)
    ·
      refine ⟨261220042288386654614819273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174146694858924436409879515 261220042288386654614819273)
      ·
        refine ⟨195915031716289990961114455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261220042288386654614819273 195915031716289990961114455)
        ·
          refine ⟨293872547574434986441671683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195915031716289990961114455 293872547574434986441671683)
          ·
            refine ⟨440808821361652479662507525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293872547574434986441671683 440808821361652479662507525)
            ·
              refine ⟨82651654005309839936720161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440808821361652479662507525 82651654005309839936720161)
              ·
                refine ⟨61988740503982379952540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82651654005309839936720161 61988740503982379952540121)
                ·
                  refine ⟨46491555377986784964405091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61988740503982379952540121 46491555377986784964405091)
                  ·
                    refine ⟨69737333066980177446607637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46491555377986784964405091 69737333066980177446607637)
                    ·
                      refine ⟨3268937487514695817809733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69737333066980177446607637 3268937487514695817809733)
                      ·
                        rfl

theorem cell23_6366233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_6366233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366233 prefixEnd_6366233 := by exact prefixLift 6366233
  have htrace : WordTrace (prefixWord ++ tailWord_6366233) baseStart_6366233 baseEnd_6366233 := by
    simpa [prefixWord, tailWord_6366233, baseEnd_6366233] using wordTrace_append hprefix tailTrace_6366233
  have hstable : (prefixWord ++ tailWord_6366233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366233).length < 2 ^ (prefixWord ++ tailWord_6366233).sum := by decide
  have hdescent : baseEnd_6366233 < baseStart_6366233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366257 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_6366257 : Nat := 118140960795 + 6366257 * 2 ^ 59
def prefixEnd_6366257 : Nat := 4983230072969 + 3 ^ 40 * 6366257 * 2
def baseEnd_6366257 : Nat := 3268949811050403723909623

theorem tailTrace_6366257 : CollatzResearch.WordTrace tailWord_6366257 prefixEnd_6366257 3268949811050403723909623 := by
  unfold tailWord_6366257
  simp only [CollatzResearch.WordTrace]
  refine ⟨232196468497145633978713025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154797645664763755985808683 232196468497145633978713025)
  ·
    refine ⟨174147351372859225484034769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232196468497145633978713025 174147351372859225484034769)
    ·
      refine ⟨130610513529644419113026077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174147351372859225484034769 130610513529644419113026077)
      ·
        refine ⟨48978942573616657167384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130610513529644419113026077 48978942573616657167384779)
        ·
          refine ⟨73468413860424985751077169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48978942573616657167384779 73468413860424985751077169)
          ·
            refine ⟨55101310395318739313307877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73468413860424985751077169 55101310395318739313307877)
            ·
              refine ⟨10331495699122263621245227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55101310395318739313307877 10331495699122263621245227)
              ·
                refine ⟨15497243548683395431867841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331495699122263621245227 15497243548683395431867841)
                ·
                  refine ⟨11622932661512546573900881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15497243548683395431867841 11622932661512546573900881)
                  ·
                    refine ⟨8717199496134409930425661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11622932661512546573900881 8717199496134409930425661)
                    ·
                      refine ⟨3268949811050403723909623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717199496134409930425661 3268949811050403723909623)
                      ·
                        rfl

theorem cell23_6366257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_6366257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366257 prefixEnd_6366257 := by exact prefixLift 6366257
  have htrace : WordTrace (prefixWord ++ tailWord_6366257) baseStart_6366257 baseEnd_6366257 := by
    simpa [prefixWord, tailWord_6366257, baseEnd_6366257] using wordTrace_append hprefix tailTrace_6366257
  have hstable : (prefixWord ++ tailWord_6366257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366257).length < 2 ^ (prefixWord ++ tailWord_6366257).sum := by decide
  have hdescent : baseEnd_6366257 < baseStart_6366257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_6366263 : Nat := 118140960795 + 6366263 * 2 ^ 59
def prefixEnd_6366263 : Nat := 4983230072969 + 3 ^ 40 * 6366263 * 2
def baseEnd_6366263 : Nat := 3268952891934330700434595

theorem tailTrace_6366263 : CollatzResearch.WordTrace tailWord_6366263 prefixEnd_6366263 3268952891934330700434595 := by
  unfold tailWord_6366263
  simp only [CollatzResearch.WordTrace]
  refine ⟨232196687335123897003431443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154797791556749264668954295 232196687335123897003431443)
  ·
    refine ⟨348295031002685845505147165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232196687335123897003431443 348295031002685845505147165)
    ·
      refine ⟨130610636626007192064430187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348295031002685845505147165 130610636626007192064430187)
      ·
        refine ⟨195915954939010788096645281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130610636626007192064430187 195915954939010788096645281)
        ·
          refine ⟨146936966204258091072483961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195915954939010788096645281 146936966204258091072483961)
          ·
            refine ⟨110202724653193568304362971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146936966204258091072483961 110202724653193568304362971)
            ·
              refine ⟨165304086979790352456544457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110202724653193568304362971 165304086979790352456544457)
              ·
                refine ⟨123978065234842764342408343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165304086979790352456544457 123978065234842764342408343)
                ·
                  refine ⟨185967097852264146513612515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123978065234842764342408343 185967097852264146513612515)
                  ·
                    refine ⟨278950646778396219770418773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185967097852264146513612515 278950646778396219770418773)
                    ·
                      refine ⟨3268952891934330700434595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278950646778396219770418773 3268952891934330700434595)
                      ·
                        rfl

theorem cell23_6366263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_6366263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366263 prefixEnd_6366263 := by exact prefixLift 6366263
  have htrace : WordTrace (prefixWord ++ tailWord_6366263) baseStart_6366263 baseEnd_6366263 := by
    simpa [prefixWord, tailWord_6366263, baseEnd_6366263] using wordTrace_append hprefix tailTrace_6366263
  have hstable : (prefixWord ++ tailWord_6366263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366263).length < 2 ^ (prefixWord ++ tailWord_6366263).sum := by decide
  have hdescent : baseEnd_6366263 < baseStart_6366263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366283 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_6366283 : Nat := 118140960795 + 6366283 * 2 ^ 59
def prefixEnd_6366283 : Nat := 4983230072969 + 3 ^ 40 * 6366283 * 2
def baseEnd_6366283 : Nat := 3268963161547420622184503

theorem tailTrace_6366283 : CollatzResearch.WordTrace tailWord_6366283 prefixEnd_6366283 3268963161547420622184503 := by
  unfold tailWord_6366283
  simp only [CollatzResearch.WordTrace]
  refine ⟨232197416795051440419159503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154798277863367626946106335 232197416795051440419159503)
  ·
    refine ⟨348296125192577160628739255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232197416795051440419159503 348296125192577160628739255)
    ·
      refine ⟨522444187788865740943108883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348296125192577160628739255 522444187788865740943108883)
      ·
        refine ⟨783666281683298611414663325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522444187788865740943108883 783666281683298611414663325)
        ·
          refine ⟨293874855631236979280498747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783666281683298611414663325 293874855631236979280498747)
          ·
            refine ⟨440812283446855468920748121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293874855631236979280498747 440812283446855468920748121)
            ·
              refine ⟨330609212585141601690561091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440812283446855468920748121 330609212585141601690561091)
              ·
                refine ⟨495913818877712402535841637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330609212585141601690561091 495913818877712402535841637)
                ·
                  refine ⟨92983841039571075475470307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495913818877712402535841637 92983841039571075475470307)
                  ·
                    refine ⟨139475761559356613213205461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92983841039571075475470307 139475761559356613213205461)
                    ·
                      refine ⟨3268963161547420622184503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139475761559356613213205461 3268963161547420622184503)
                      ·
                        rfl

theorem cell23_6366283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_6366283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366283 prefixEnd_6366283 := by exact prefixLift 6366283
  have htrace : WordTrace (prefixWord ++ tailWord_6366283) baseStart_6366283 baseEnd_6366283 := by
    simpa [prefixWord, tailWord_6366283, baseEnd_6366283] using wordTrace_append hprefix tailTrace_6366283
  have hstable : (prefixWord ++ tailWord_6366283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366283).length < 2 ^ (prefixWord ++ tailWord_6366283).sum := by decide
  have hdescent : baseEnd_6366283 < baseStart_6366283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366300 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6366300 : Nat := 118140960795 + 6366300 * 2 ^ 59
def prefixEnd_6366300 : Nat := 4983230072969 + 3 ^ 40 * 6366300 * 2
def baseEnd_6366300 : Nat := 3268971890718547055671925

theorem tailTrace_6366300 : CollatzResearch.WordTrace tailWord_6366300 prefixEnd_6366300 3268971890718547055671925 := by
  unfold tailWord_6366300
  simp only [CollatzResearch.WordTrace]
  refine ⟨116099018417994926161264177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154798691223993234881685569 116099018417994926161264177)
  ·
    refine ⟨87074263813496194620948133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116099018417994926161264177 87074263813496194620948133)
    ·
      refine ⟨16326424465030536491427775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87074263813496194620948133 16326424465030536491427775)
      ·
        refine ⟨24489636697545804737141663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326424465030536491427775 24489636697545804737141663)
        ·
          refine ⟨36734455046318707105712495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489636697545804737141663 36734455046318707105712495)
          ·
            refine ⟨55101682569478060658568743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36734455046318707105712495 55101682569478060658568743)
            ·
              refine ⟨82652523854217090987853115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55101682569478060658568743 82652523854217090987853115)
              ·
                refine ⟨123978785781325636481779673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82652523854217090987853115 123978785781325636481779673)
                ·
                  refine ⟨92984089335994227361334755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123978785781325636481779673 92984089335994227361334755)
                  ·
                    refine ⟨139476134003991341042002133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92984089335994227361334755 139476134003991341042002133)
                    ·
                      refine ⟨3268971890718547055671925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139476134003991341042002133 3268971890718547055671925)
                      ·
                        rfl

theorem cell23_6366300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6366300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366300 prefixEnd_6366300 := by exact prefixLift 6366300
  have htrace : WordTrace (prefixWord ++ tailWord_6366300) baseStart_6366300 baseEnd_6366300 := by
    simpa [prefixWord, tailWord_6366300, baseEnd_6366300] using wordTrace_append hprefix tailTrace_6366300
  have hstable : (prefixWord ++ tailWord_6366300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366300).length < 2 ^ (prefixWord ++ tailWord_6366300).sum := by decide
  have hdescent : baseEnd_6366300 < baseStart_6366300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366314 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6366314 : Nat := 118140960795 + 6366314 * 2 ^ 59
def prefixEnd_6366314 : Nat := 4983230072969 + 3 ^ 40 * 6366314 * 2
def baseEnd_6366314 : Nat := 3268979079447710000896861

theorem tailTrace_6366314 : CollatzResearch.WordTrace tailWord_6366314 prefixEnd_6366314 3268979079447710000896861 := by
  unfold tailWord_6366314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58049636864484783178384499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154799031638626088475691997 58049636864484783178384499)
  ·
    refine ⟨87074455296727174767576749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58049636864484783178384499 87074455296727174767576749)
    ·
      refine ⟨32652920736272690537841281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87074455296727174767576749 32652920736272690537841281)
      ·
        refine ⟨24489690552204517903380961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32652920736272690537841281 24489690552204517903380961)
        ·
          refine ⟨18367267914153388427535721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24489690552204517903380961 18367267914153388427535721)
          ·
            refine ⟨13775450935615041320651791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18367267914153388427535721 13775450935615041320651791)
            ·
              refine ⟨20663176403422561980977687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775450935615041320651791 20663176403422561980977687)
              ·
                refine ⟨30994764605133842971466531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20663176403422561980977687 30994764605133842971466531)
                ·
                  refine ⟨46492146907700764457199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30994764605133842971466531 46492146907700764457199797)
                  ·
                    refine ⟨4358638772596946667862481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46492146907700764457199797 4358638772596946667862481)
                    ·
                      refine ⟨3268979079447710000896861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358638772596946667862481 3268979079447710000896861)
                      ·
                        rfl

theorem cell23_6366314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6366314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366314 prefixEnd_6366314 := by exact prefixLift 6366314
  have htrace : WordTrace (prefixWord ++ tailWord_6366314) baseStart_6366314 baseEnd_6366314 := by
    simpa [prefixWord, tailWord_6366314, baseEnd_6366314] using wordTrace_append hprefix tailTrace_6366314
  have hstable : (prefixWord ++ tailWord_6366314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366314).length < 2 ^ (prefixWord ++ tailWord_6366314).sum := by decide
  have hdescent : baseEnd_6366314 < baseStart_6366314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366320 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_6366320 : Nat := 118140960795 + 6366320 * 2 ^ 59
def prefixEnd_6366320 : Nat := 4983230072969 + 3 ^ 40 * 6366320 * 2
def baseEnd_6366320 : Nat := 1089660720110545659140611

theorem tailTrace_6366320 : CollatzResearch.WordTrace tailWord_6366320 prefixEnd_6366320 1089660720110545659140611 := by
  unfold tailWord_6366320
  simp only [CollatzResearch.WordTrace]
  refine ⟨116099383147958697869128207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154799177530611597158837609 116099383147958697869128207)
  ·
    refine ⟨174149074721938046803692311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116099383147958697869128207 174149074721938046803692311)
    ·
      refine ⟨261223612082907070205538467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174149074721938046803692311 261223612082907070205538467)
      ·
        refine ⟨391835418124360605308307701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261223612082907070205538467 391835418124360605308307701)
        ·
          refine ⟨36734570449158806747653847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391835418124360605308307701 36734570449158806747653847)
          ·
            refine ⟨55101855673738210121480771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36734570449158806747653847 55101855673738210121480771)
            ·
              refine ⟨82652783510607315182221157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55101855673738210121480771 82652783510607315182221157)
              ·
                refine ⟨15497396908238871596666467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82652783510607315182221157 15497396908238871596666467)
                ·
                  refine ⟨23246095362358307394999701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15497396908238871596666467 23246095362358307394999701)
                  ·
                    refine ⟨1089660720110545659140611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23246095362358307394999701 1089660720110545659140611)
                    ·
                      rfl

theorem cell23_6366320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_6366320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366320 prefixEnd_6366320 := by exact prefixLift 6366320
  have htrace : WordTrace (prefixWord ++ tailWord_6366320) baseStart_6366320 baseEnd_6366320 := by
    simpa [prefixWord, tailWord_6366320, baseEnd_6366320] using wordTrace_append hprefix tailTrace_6366320
  have hstable : (prefixWord ++ tailWord_6366320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366320).length < 2 ^ (prefixWord ++ tailWord_6366320).sum := by decide
  have hdescent : baseEnd_6366320 < baseStart_6366320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366327 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_6366327 : Nat := 118140960795 + 6366327 * 2 ^ 59
def prefixEnd_6366327 : Nat := 4983230072969 + 3 ^ 40 * 6366327 * 2
def baseEnd_6366327 : Nat := 3268985754696218450034301

theorem tailTrace_6366327 : CollatzResearch.WordTrace tailWord_6366327 prefixEnd_6366327 3268985754696218450034301 := by
  unfold tailWord_6366327
  simp only [CollatzResearch.WordTrace]
  refine ⟨232199021606892035933761235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154799347737928023955840823 232199021606892035933761235)
  ·
    refine ⟨348298532410338053900641853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232199021606892035933761235 348298532410338053900641853)
    ·
      refine ⟨130611949653876770212740695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348298532410338053900641853 130611949653876770212740695)
      ·
        refine ⟨195917924480815155319111043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130611949653876770212740695 195917924480815155319111043)
        ·
          refine ⟨293876886721222732978666565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195917924480815155319111043 293876886721222732978666565)
          ·
            refine ⟨55101916260229262433499981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293876886721222732978666565 55101916260229262433499981)
            ·
              refine ⟨20663218597585973412562493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55101916260229262433499981 20663218597585973412562493)
              ·
                refine ⟨7748706974094740029710935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20663218597585973412562493 7748706974094740029710935)
                ·
                  refine ⟨11623060461142110044566403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748706974094740029710935 11623060461142110044566403)
                  ·
                    refine ⟨17434590691713165066849605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11623060461142110044566403 17434590691713165066849605)
                    ·
                      refine ⟨3268985754696218450034301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17434590691713165066849605 3268985754696218450034301)
                      ·
                        rfl

theorem cell23_6366327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_6366327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366327 prefixEnd_6366327 := by exact prefixLift 6366327
  have htrace : WordTrace (prefixWord ++ tailWord_6366327) baseStart_6366327 baseEnd_6366327 := by
    simpa [prefixWord, tailWord_6366327, baseEnd_6366327] using wordTrace_append hprefix tailTrace_6366327
  have hstable : (prefixWord ++ tailWord_6366327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366327).length < 2 ^ (prefixWord ++ tailWord_6366327).sum := by decide
  have hdescent : baseEnd_6366327 < baseStart_6366327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366354 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_6366354 : Nat := 118140960795 + 6366354 * 2 ^ 59
def prefixEnd_6366354 : Nat := 4983230072969 + 3 ^ 40 * 6366354 * 2
def baseEnd_6366354 : Nat := 1089666539557963281465559

theorem tailTrace_6366354 : CollatzResearch.WordTrace tailWord_6366354 prefixEnd_6366354 1089666539557963281465559 := by
  unfold tailWord_6366354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58050001594448554886248529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154800004251862813029996077 58050001594448554886248529)
  ·
    refine ⟨43537501195836416164686397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58050001594448554886248529 43537501195836416164686397)
    ·
      refine ⟨16326562948438656061757399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43537501195836416164686397 16326562948438656061757399)
      ·
        refine ⟨24489844422657984092636099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326562948438656061757399 24489844422657984092636099)
        ·
          refine ⟨36734766633986976138954149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489844422657984092636099 36734766633986976138954149)
          ·
            refine ⟨6887768743872558026053903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36734766633986976138954149 6887768743872558026053903)
            ·
              refine ⟨10331653115808837039080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887768743872558026053903 10331653115808837039080855)
              ·
                refine ⟨15497479673713255558621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331653115808837039080855 15497479673713255558621283)
                ·
                  refine ⟨23246219510569883337931925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15497479673713255558621283 23246219510569883337931925)
                  ·
                    refine ⟨1089666539557963281465559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23246219510569883337931925 1089666539557963281465559)
                    ·
                      rfl

theorem cell23_6366354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_6366354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366354 prefixEnd_6366354 := by exact prefixLift 6366354
  have htrace : WordTrace (prefixWord ++ tailWord_6366354) baseStart_6366354 baseEnd_6366354 := by
    simpa [prefixWord, tailWord_6366354, baseEnd_6366354] using wordTrace_append hprefix tailTrace_6366354
  have hstable : (prefixWord ++ tailWord_6366354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366354).length < 2 ^ (prefixWord ++ tailWord_6366354).sum := by decide
  have hdescent : baseEnd_6366354 < baseStart_6366354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366364 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6366364 : Nat := 118140960795 + 6366364 * 2 ^ 59
def prefixEnd_6366364 : Nat := 4983230072969 + 3 ^ 40 * 6366364 * 2
def baseEnd_6366364 : Nat := 3269004753480434805271631

theorem tailTrace_6366364 : CollatzResearch.WordTrace tailWord_6366364 prefixEnd_6366364 3269004753480434805271631 := by
  unfold tailWord_6366364
  simp only [CollatzResearch.WordTrace]
  refine ⟨116100185553878995626429073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154800247405171994168572097 116100185553878995626429073)
  ·
    refine ⟨87075139165409246719821805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116100185553878995626429073 87075139165409246719821805)
    ·
      refine ⟨32653177187028467519933177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87075139165409246719821805 32653177187028467519933177)
      ·
        refine ⟨24489882890271350639949883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32653177187028467519933177 24489882890271350639949883)
        ·
          refine ⟨36734824335407025959924825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489882890271350639949883 36734824335407025959924825)
          ·
            refine ⟨27551118251555269469943619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36734824335407025959924825 27551118251555269469943619)
            ·
              refine ⟨41326677377332904204915429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27551118251555269469943619 41326677377332904204915429)
              ·
                refine ⟨7748752008249919538421643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41326677377332904204915429 7748752008249919538421643)
                ·
                  refine ⟨11623128012374879307632465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748752008249919538421643 11623128012374879307632465)
                  ·
                    refine ⟨8717346009281159480724349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11623128012374879307632465 8717346009281159480724349)
                    ·
                      refine ⟨3269004753480434805271631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717346009281159480724349 3269004753480434805271631)
                      ·
                        rfl

theorem cell23_6366364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6366364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366364 prefixEnd_6366364 := by exact prefixLift 6366364
  have htrace : WordTrace (prefixWord ++ tailWord_6366364) baseStart_6366364 baseEnd_6366364 := by
    simpa [prefixWord, tailWord_6366364, baseEnd_6366364] using wordTrace_append hprefix tailTrace_6366364
  have hstable : (prefixWord ++ tailWord_6366364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366364).length < 2 ^ (prefixWord ++ tailWord_6366364).sum := by decide
  have hdescent : baseEnd_6366364 < baseStart_6366364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366367 : List Nat := [1, 1, 2, 6, 2, 1, 1, 9]
def baseStart_6366367 : Nat := 118140960795 + 6366367 * 2 ^ 59
def prefixEnd_6366367 : Nat := 4983230072969 + 3 ^ 40 * 6366367 * 2
def baseEnd_6366367 : Nat := 121074307182311047908671

theorem tailTrace_6366367 : CollatzResearch.WordTrace tailWord_6366367 prefixEnd_6366367 121074307182311047908671 := by
  unfold tailWord_6366367
  simp only [CollatzResearch.WordTrace]
  refine ⟨232200480526747122765217355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154800320351164748510144903 232200480526747122765217355)
  ·
    refine ⟨348300720790120684147826033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232200480526747122765217355 348300720790120684147826033)
    ·
      refine ⟨261225540592590513110869525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348300720790120684147826033 261225540592590513110869525)
      ·
        refine ⟨12244947215277680302072009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 261225540592590513110869525 12244947215277680302072009)
        ·
          refine ⟨9183710411458260226554007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12244947215277680302072009 9183710411458260226554007)
          ·
            refine ⟨13775565617187390339831011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183710411458260226554007 13775565617187390339831011)
            ·
              refine ⟨20663348425781085509746517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775565617187390339831011 20663348425781085509746517)
              ·
                refine ⟨121074307182311047908671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20663348425781085509746517 121074307182311047908671)
                ·
                  rfl

theorem cell23_6366367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 9].length) (baseStart_6366367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366367 prefixEnd_6366367 := by exact prefixLift 6366367
  have htrace : WordTrace (prefixWord ++ tailWord_6366367) baseStart_6366367 baseEnd_6366367 := by
    simpa [prefixWord, tailWord_6366367, baseEnd_6366367] using wordTrace_append hprefix tailTrace_6366367
  have hstable : (prefixWord ++ tailWord_6366367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366367).length < 2 ^ (prefixWord ++ tailWord_6366367).sum := by decide
  have hdescent : baseEnd_6366367 < baseStart_6366367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366394 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_6366394 : Nat := 118140960795 + 6366394 * 2 ^ 59
def prefixEnd_6366394 : Nat := 4983230072969 + 3 ^ 40 * 6366394 * 2
def baseEnd_6366394 : Nat := 3269020157900069687896493

theorem tailTrace_6366394 : CollatzResearch.WordTrace tailWord_6366394 prefixEnd_6366394 3269020157900069687896493 := by
  unfold tailWord_6366394
  simp only [CollatzResearch.WordTrace]
  refine ⟨58050366324412326594112559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154800976865099537584300157 58050366324412326594112559)
  ·
    refine ⟨87075549486618489891168839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58050366324412326594112559 87075549486618489891168839)
    ·
      refine ⟨130613324229927734836753259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87075549486618489891168839 130613324229927734836753259)
      ·
        refine ⟨195919986344891602255129889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130613324229927734836753259 195919986344891602255129889)
        ·
          refine ⟨146939989758668701691347417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195919986344891602255129889 146939989758668701691347417)
          ·
            refine ⟨110204992319001526268510563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146939989758668701691347417 110204992319001526268510563)
            ·
              refine ⟨165307488478502289402765845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110204992319001526268510563 165307488478502289402765845)
              ·
                refine ⟨7748788522429794815754649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165307488478502289402765845 7748788522429794815754649)
                ·
                  refine ⟨5811591391822346111815987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7748788522429794815754649 5811591391822346111815987)
                  ·
                    refine ⟨8717387087733519167723981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5811591391822346111815987 8717387087733519167723981)
                    ·
                      refine ⟨3269020157900069687896493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717387087733519167723981 3269020157900069687896493)
                      ·
                        rfl

theorem cell23_6366394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_6366394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366394 prefixEnd_6366394 := by exact prefixLift 6366394
  have htrace : WordTrace (prefixWord ++ tailWord_6366394) baseStart_6366394 baseEnd_6366394 := by
    simpa [prefixWord, tailWord_6366394, baseEnd_6366394] using wordTrace_append hprefix tailTrace_6366394
  have hstable : (prefixWord ++ tailWord_6366394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366394).length < 2 ^ (prefixWord ++ tailWord_6366394).sum := by decide
  have hdescent : baseEnd_6366394 < baseStart_6366394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366421 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6366421 : Nat := 118140960795 + 6366421 * 2 ^ 59
def prefixEnd_6366421 : Nat := 4983230072969 + 3 ^ 40 * 6366421 * 2
def baseEnd_6366421 : Nat := 3269034021877741082258869

theorem tailTrace_6366421 : CollatzResearch.WordTrace tailWord_6366421 prefixEnd_6366421 3269034021877741082258869 := by
  unfold tailWord_6366421
  simp only [CollatzResearch.WordTrace]
  refine ⟨232202450068551489987683117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154801633379034326658455411 232202450068551489987683117)
  ·
    refine ⟨87075918775706808745381169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232202450068551489987683117 87075918775706808745381169)
    ·
      refine ⟨65306939081780106559035877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87075918775706808745381169 65306939081780106559035877)
      ·
        refine ⟨12245051077833769979819227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65306939081780106559035877 12245051077833769979819227)
        ·
          refine ⟨18367576616750654969728841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12245051077833769979819227 18367576616750654969728841)
          ·
            refine ⟨13775682462562991227296631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18367576616750654969728841 13775682462562991227296631)
            ·
              refine ⟨20663523693844486840944947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775682462562991227296631 20663523693844486840944947)
              ·
                refine ⟨30995285540766730261417421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20663523693844486840944947 30995285540766730261417421)
                ·
                  refine ⟨11623232077787523848031533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30995285540766730261417421 11623232077787523848031533)
                  ·
                    refine ⟨4358712029170321443011825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11623232077787523848031533 4358712029170321443011825)
                    ·
                      refine ⟨3269034021877741082258869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358712029170321443011825 3269034021877741082258869)
                      ·
                        rfl

theorem cell23_6366421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6366421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366421 prefixEnd_6366421 := by exact prefixLift 6366421
  have htrace : WordTrace (prefixWord ++ tailWord_6366421) baseStart_6366421 baseEnd_6366421 := by
    simpa [prefixWord, tailWord_6366421, baseEnd_6366421] using wordTrace_append hprefix tailTrace_6366421
  have hstable : (prefixWord ++ tailWord_6366421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366421).length < 2 ^ (prefixWord ++ tailWord_6366421).sum := by decide
  have hdescent : baseEnd_6366421 < baseStart_6366421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366451 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 2, 2, 2]
def baseStart_6366451 : Nat := 118140960795 + 6366451 * 2 ^ 59
def prefixEnd_6366451 : Nat := 4983230072969 + 3 ^ 40 * 6366451 * 2
def baseEnd_6366451 : Nat := 3269049426297375964883731

theorem tailTrace_6366451 : CollatzResearch.WordTrace tailWord_6366451 prefixEnd_6366451 3269049426297375964883731 := by
  unfold tailWord_6366451
  simp only [CollatzResearch.WordTrace]
  refine ⟨232203544258442805111275207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154802362838961870074183471 232203544258442805111275207)
  ·
    refine ⟨348305316387664207666912811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232203544258442805111275207 348305316387664207666912811)
    ·
      refine ⟨522457974581496311500369217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348305316387664207666912811 522457974581496311500369217)
      ·
        refine ⟨391843480936122233625276913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522457974581496311500369217 391843480936122233625276913)
        ·
          refine ⟨293882610702091675218957685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391843480936122233625276913 293882610702091675218957685)
          ·
            refine ⟨27551494753321094551777283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293882610702091675218957685 27551494753321094551777283)
            ·
              refine ⟨41327242129981641827665925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27551494753321094551777283 41327242129981641827665925)
              ·
                refine ⟨7748857899371557842687361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41327242129981641827665925 7748857899371557842687361)
                ·
                  refine ⟨5811643424528668382015521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7748857899371557842687361 5811643424528668382015521)
                  ·
                    refine ⟨4358732568396501286511641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5811643424528668382015521 4358732568396501286511641)
                    ·
                      refine ⟨3269049426297375964883731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358732568396501286511641 3269049426297375964883731)
                      ·
                        rfl

theorem cell23_6366451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2, 2].length) (baseStart_6366451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366451 prefixEnd_6366451 := by exact prefixLift 6366451
  have htrace : WordTrace (prefixWord ++ tailWord_6366451) baseStart_6366451 baseEnd_6366451 := by
    simpa [prefixWord, tailWord_6366451, baseEnd_6366451] using wordTrace_append hprefix tailTrace_6366451
  have hstable : (prefixWord ++ tailWord_6366451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366451).length < 2 ^ (prefixWord ++ tailWord_6366451).sum := by decide
  have hdescent : baseEnd_6366451 < baseStart_6366451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366467 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3]
def baseStart_6366467 : Nat := 118140960795 + 6366467 * 2 ^ 59
def prefixEnd_6366467 : Nat := 4983230072969 + 3 ^ 40 * 6366467 * 2
def baseEnd_6366467 : Nat := 3269057641987847902283657

theorem tailTrace_6366467 : CollatzResearch.WordTrace tailWord_6366467 prefixEnd_6366467 3269057641987847902283657 := by
  unfold tailWord_6366467
  simp only [CollatzResearch.WordTrace]
  refine ⟨232204127826384839843857655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154802751884256559895905103 232204127826384839843857655)
  ·
    refine ⟨348306191739577259765786483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232204127826384839843857655 348306191739577259765786483)
    ·
      refine ⟨522459287609365889648679725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348306191739577259765786483 522459287609365889648679725)
      ·
        refine ⟨195922232853512208618254897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522459287609365889648679725 195922232853512208618254897)
        ·
          refine ⟨146941674640134156463691173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195922232853512208618254897 146941674640134156463691173)
          ·
            refine ⟨27551563995025154336942095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146941674640134156463691173 27551563995025154336942095)
            ·
              refine ⟨41327345992537731505413143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27551563995025154336942095 41327345992537731505413143)
              ·
                refine ⟨61991018988806597258119715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41327345992537731505413143 61991018988806597258119715)
                ·
                  refine ⟨92986528483209895887179573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61991018988806597258119715 92986528483209895887179573)
                  ·
                    refine ⟨8717487045300927739423085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92986528483209895887179573 8717487045300927739423085)
                    ·
                      refine ⟨3269057641987847902283657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717487045300927739423085 3269057641987847902283657)
                      ·
                        rfl

theorem cell23_6366467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_6366467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366467 prefixEnd_6366467 := by exact prefixLift 6366467
  have htrace : WordTrace (prefixWord ++ tailWord_6366467) baseStart_6366467 baseEnd_6366467 := by
    simpa [prefixWord, tailWord_6366467, baseEnd_6366467] using wordTrace_append hprefix tailTrace_6366467
  have hstable : (prefixWord ++ tailWord_6366467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366467).length < 2 ^ (prefixWord ++ tailWord_6366467).sum := by decide
  have hdescent : baseEnd_6366467 < baseStart_6366467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366468 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6366468 : Nat := 118140960795 + 6366468 * 2 ^ 59
def prefixEnd_6366468 : Nat := 4983230072969 + 3 ^ 40 * 6366468 * 2
def baseEnd_6366468 : Nat := 3269058155468502398371153

theorem tailTrace_6366468 : CollatzResearch.WordTrace tailWord_6366468 prefixEnd_6366468 3269058155468502398371153 := by
  unfold tailWord_6366468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116102082149690608507322029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154802776199587478009762705 116102082149690608507322029)
  ·
    refine ⟨43538280806133978190245761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116102082149690608507322029 43538280806133978190245761)
    ·
      refine ⟨32653710604600483642684321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43538280806133978190245761 32653710604600483642684321)
      ·
        refine ⟨24490282953450362732013241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32653710604600483642684321 24490282953450362732013241)
        ·
          refine ⟨18367712215087772049009931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24490282953450362732013241 18367712215087772049009931)
          ·
            refine ⟨27551568322631658073514897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18367712215087772049009931 27551568322631658073514897)
            ·
              refine ⟨20663676241973743555136173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27551568322631658073514897 20663676241973743555136173)
              ·
                refine ⟨7748878590740153833176065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20663676241973743555136173 7748878590740153833176065)
                ·
                  refine ⟨5811658943055115374882049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7748878590740153833176065 5811658943055115374882049)
                  ·
                    refine ⟨4358744207291336531161537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5811658943055115374882049 4358744207291336531161537)
                    ·
                      refine ⟨3269058155468502398371153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358744207291336531161537 3269058155468502398371153)
                      ·
                        rfl

theorem cell23_6366468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6366468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366468 prefixEnd_6366468 := by exact prefixLift 6366468
  have htrace : WordTrace (prefixWord ++ tailWord_6366468) baseStart_6366468 baseEnd_6366468 := by
    simpa [prefixWord, tailWord_6366468, baseEnd_6366468] using wordTrace_append hprefix tailTrace_6366468
  have hstable : (prefixWord ++ tailWord_6366468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366468).length < 2 ^ (prefixWord ++ tailWord_6366468).sum := by decide
  have hdescent : baseEnd_6366468 < baseStart_6366468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366487 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 7]
def baseStart_6366487 : Nat := 118140960795 + 6366487 * 2 ^ 59
def prefixEnd_6366487 : Nat := 4983230072969 + 3 ^ 40 * 6366487 * 2
def baseEnd_6366487 : Nat := 1089689303866979274677855

theorem tailTrace_6366487 : CollatzResearch.WordTrace tailWord_6366487 prefixEnd_6366487 1089689303866979274677855 := by
  unfold tailWord_6366487
  simp only [CollatzResearch.WordTrace]
  refine ⟨232204857286312383259585715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154803238190874922173057143 232204857286312383259585715)
  ·
    refine ⟨348307285929468574889378573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232204857286312383259585715 348307285929468574889378573)
    ·
      refine ⟨130615232223550715583516965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348307285929468574889378573 130615232223550715583516965)
      ·
        refine ⟨24490356041915759171909431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130615232223550715583516965 24490356041915759171909431)
        ·
          refine ⟨36735534062873638757864147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24490356041915759171909431 36735534062873638757864147)
          ·
            refine ⟨55103301094310458136796221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36735534062873638757864147 55103301094310458136796221)
            ·
              refine ⟨20663737910366421801298583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55103301094310458136796221 20663737910366421801298583)
              ·
                refine ⟨30995606865549632701947875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20663737910366421801298583 30995606865549632701947875)
                ·
                  refine ⟨46493410298324449052921813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30995606865549632701947875 46493410298324449052921813)
                  ·
                    refine ⟨1089689303866979274677855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46493410298324449052921813 1089689303866979274677855)
                    ·
                      rfl

theorem cell23_6366487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_6366487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366487 prefixEnd_6366487 := by exact prefixLift 6366487
  have htrace : WordTrace (prefixWord ++ tailWord_6366487) baseStart_6366487 baseEnd_6366487 := by
    simpa [prefixWord, tailWord_6366487, baseEnd_6366487] using wordTrace_append hprefix tailTrace_6366487
  have hstable : (prefixWord ++ tailWord_6366487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366487).length < 2 ^ (prefixWord ++ tailWord_6366487).sum := by decide
  have hdescent : baseEnd_6366487 < baseStart_6366487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366544 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_6366544 : Nat := 118140960795 + 6366544 * 2 ^ 59
def prefixEnd_6366544 : Nat := 4983230072969 + 3 ^ 40 * 6366544 * 2
def baseEnd_6366544 : Nat := 3269097179998244101020803

theorem tailTrace_6366544 : CollatzResearch.WordTrace tailWord_6366544 prefixEnd_6366544 3269097179998244101020803 := by
  unfold tailWord_6366544
  simp only [CollatzResearch.WordTrace]
  refine ⟨116103468123552940997205343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154804624164737254662940457 116103468123552940997205343)
  ·
    refine ⟨174155202185329411495808015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116103468123552940997205343 174155202185329411495808015)
    ·
      refine ⟨261232803277994117243712023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174155202185329411495808015 261232803277994117243712023)
      ·
        refine ⟨391849204916991175865568035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261232803277994117243712023 391849204916991175865568035)
        ·
          refine ⟨587773807375486763798352053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391849204916991175865568035 587773807375486763798352053)
          ·
            refine ⟨55103794441451884106095505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 587773807375486763798352053 55103794441451884106095505)
            ·
              refine ⟨41327845831088913079571629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55103794441451884106095505 41327845831088913079571629)
              ·
                refine ⟨15497942186658342404839361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41327845831088913079571629 15497942186658342404839361)
                ·
                  refine ⟨11623456639993756803629521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15497942186658342404839361 11623456639993756803629521)
                  ·
                    refine ⟨8717592479995317602722141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11623456639993756803629521 8717592479995317602722141)
                    ·
                      refine ⟨3269097179998244101020803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717592479995317602722141 3269097179998244101020803)
                      ·
                        rfl

theorem cell23_6366544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_6366544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366544 prefixEnd_6366544 := by exact prefixLift 6366544
  have htrace : WordTrace (prefixWord ++ tailWord_6366544) baseStart_6366544 baseEnd_6366544 := by
    simpa [prefixWord, tailWord_6366544, baseEnd_6366544] using wordTrace_append hprefix tailTrace_6366544
  have hstable : (prefixWord ++ tailWord_6366544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366544).length < 2 ^ (prefixWord ++ tailWord_6366544).sum := by decide
  have hdescent : baseEnd_6366544 < baseStart_6366544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366568 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_6366568 : Nat := 118140960795 + 6366568 * 2 ^ 59
def prefixEnd_6366568 : Nat := 4983230072969 + 3 ^ 40 * 6366568 * 2
def baseEnd_6366568 : Nat := 1089703167844650669040231

theorem tailTrace_6366568 : CollatzResearch.WordTrace tailWord_6366568 prefixEnd_6366568 1089703167844650669040231 := by
  unfold tailWord_6366568
  simp only [CollatzResearch.WordTrace]
  refine ⟨116103905799509467046642179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154805207732679289395522905 116103905799509467046642179)
  ·
    refine ⟨174155858699264200569963269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116103905799509467046642179 174155858699264200569963269)
    ·
      refine ⟨32654223506112037606868113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174155858699264200569963269 32654223506112037606868113)
      ·
        refine ⟨24490667629584028205151085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32654223506112037606868113 24490667629584028205151085)
        ·
          refine ⟨9184000361094010576931657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24490667629584028205151085 9184000361094010576931657)
          ·
            refine ⟨6888000270820507932698743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9184000361094010576931657 6888000270820507932698743)
            ·
              refine ⟨10332000406230761899048115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888000270820507932698743 10332000406230761899048115)
              ·
                refine ⟨15498000609346142848572173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10332000406230761899048115 15498000609346142848572173)
                ·
                  refine ⟨5811750228504803568214565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15498000609346142848572173 5811750228504803568214565)
                  ·
                    refine ⟨1089703167844650669040231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5811750228504803568214565 1089703167844650669040231)
                    ·
                      rfl

theorem cell23_6366568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_6366568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366568 prefixEnd_6366568 := by exact prefixLift 6366568
  have htrace : WordTrace (prefixWord ++ tailWord_6366568) baseStart_6366568 baseEnd_6366568 := by
    simpa [prefixWord, tailWord_6366568, baseEnd_6366568] using wordTrace_append hprefix tailTrace_6366568
  have hstable : (prefixWord ++ tailWord_6366568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366568).length < 2 ^ (prefixWord ++ tailWord_6366568).sum := by decide
  have hdescent : baseEnd_6366568 < baseStart_6366568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366581 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 6]
def baseStart_6366581 : Nat := 118140960795 + 6366581 * 2 ^ 59
def prefixEnd_6366581 : Nat := 4983230072969 + 3 ^ 40 * 6366581 * 2
def baseEnd_6366581 : Nat := 363235130975828939584237

theorem tailTrace_6366581 : CollatzResearch.WordTrace tailWord_6366581 prefixEnd_6366581 363235130975828939584237 := by
  unfold tailWord_6366581
  simp only [CollatzResearch.WordTrace]
  refine ⟨232208285747971837313507597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154805523831981224875671731 232208285747971837313507597)
  ·
    refine ⟨87078107155489438992565349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232208285747971837313507597 87078107155489438992565349)
    ·
      refine ⟨16327145091654269811106003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87078107155489438992565349 16327145091654269811106003)
      ·
        refine ⟨24490717637481404716659005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16327145091654269811106003 24490717637481404716659005)
        ·
          refine ⟨9184019114055526768747127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24490717637481404716659005 9184019114055526768747127)
          ·
            refine ⟨13776028671083290153120691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184019114055526768747127 13776028671083290153120691)
            ·
              refine ⟨20664043006624935229681037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13776028671083290153120691 20664043006624935229681037)
              ·
                refine ⟨7749016127484350711130389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20664043006624935229681037 7749016127484350711130389)
                ·
                  refine ⟨363235130975828939584237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7749016127484350711130389 363235130975828939584237)
                  ·
                    rfl

theorem cell23_6366581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_6366581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366581 prefixEnd_6366581 := by exact prefixLift 6366581
  have htrace : WordTrace (prefixWord ++ tailWord_6366581) baseStart_6366581 baseEnd_6366581 := by
    simpa [prefixWord, tailWord_6366581, baseEnd_6366581] using wordTrace_append hprefix tailTrace_6366581
  have hstable : (prefixWord ++ tailWord_6366581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366581).length < 2 ^ (prefixWord ++ tailWord_6366581).sum := by decide
  have hdescent : baseEnd_6366581 < baseStart_6366581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366641 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_6366641 : Nat := 118140960795 + 6366641 * 2 ^ 59
def prefixEnd_6366641 : Nat := 4983230072969 + 3 ^ 40 * 6366641 * 2
def baseEnd_6366641 : Nat := 1089715662540576740502619

theorem tailTrace_6366641 : CollatzResearch.WordTrace tailWord_6366641 prefixEnd_6366641 1089715662540576740502619 := by
  unfold tailWord_6366641
  simp only [CollatzResearch.WordTrace]
  refine ⟨232210474127754467560691777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154806982751836311707127851 232210474127754467560691777)
  ·
    refine ⟨174157855595815850670518833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232210474127754467560691777 174157855595815850670518833)
    ·
      refine ⟨130618391696861888002889125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174157855595815850670518833 130618391696861888002889125)
      ·
        refine ⟨24490948443161604000541711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130618391696861888002889125 24490948443161604000541711)
        ·
          refine ⟨36736422664742406000812567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24490948443161604000541711 36736422664742406000812567)
          ·
            refine ⟨55104633997113609001218851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36736422664742406000812567 55104633997113609001218851)
            ·
              refine ⟨82656950995670413501828277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55104633997113609001218851 82656950995670413501828277)
              ·
                refine ⟨7749089155844101265796401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82656950995670413501828277 7749089155844101265796401)
                ·
                  refine ⟨5811816866883075949347301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749089155844101265796401 5811816866883075949347301)
                  ·
                    refine ⟨1089715662540576740502619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5811816866883075949347301 1089715662540576740502619)
                    ·
                      rfl

theorem cell23_6366641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_6366641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366641 prefixEnd_6366641 := by exact prefixLift 6366641
  have htrace : WordTrace (prefixWord ++ tailWord_6366641) baseStart_6366641 baseEnd_6366641 := by
    simpa [prefixWord, tailWord_6366641, baseEnd_6366641] using wordTrace_append hprefix tailTrace_6366641
  have hstable : (prefixWord ++ tailWord_6366641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366641).length < 2 ^ (prefixWord ++ tailWord_6366641).sum := by decide
  have hdescent : baseEnd_6366641 < baseStart_6366641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366652 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6366652 : Nat := 118140960795 + 6366652 * 2 ^ 59
def prefixEnd_6366652 : Nat := 4983230072969 + 3 ^ 40 * 6366652 * 2
def baseEnd_6366652 : Nat := 3269152635908929678470307

theorem tailTrace_6366652 : CollatzResearch.WordTrace tailWord_6366652 prefixEnd_6366652 3269152635908929678470307 := by
  unfold tailWord_6366652
  simp only [CollatzResearch.WordTrace]
  refine ⟨116105437665357308219671105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154807250220476410959561473 116105437665357308219671105)
  ·
    refine ⟨87079078249017981164753329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116105437665357308219671105 87079078249017981164753329)
    ·
      refine ⟨65309308686763485873564997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87079078249017981164753329 65309308686763485873564997)
      ·
        refine ⟨12245495378768153601293437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65309308686763485873564997 12245495378768153601293437)
        ·
          refine ⟨4592060767038057600485039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12245495378768153601293437 4592060767038057600485039)
          ·
            refine ⟨6888091150557086400727559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592060767038057600485039 6888091150557086400727559)
            ·
              refine ⟨10332136725835629601091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888091150557086400727559 10332136725835629601091339)
              ·
                refine ⟨15498205088753444401637009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10332136725835629601091339 15498205088753444401637009)
                ·
                  refine ⟨11623653816565083301227757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15498205088753444401637009 11623653816565083301227757)
                  ·
                    refine ⟨4358870181211906237960409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11623653816565083301227757 4358870181211906237960409)
                    ·
                      refine ⟨3269152635908929678470307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358870181211906237960409 3269152635908929678470307)
                      ·
                        rfl

theorem cell23_6366652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6366652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366652 prefixEnd_6366652 := by exact prefixLift 6366652
  have htrace : WordTrace (prefixWord ++ tailWord_6366652) baseStart_6366652 baseEnd_6366652 := by
    simpa [prefixWord, tailWord_6366652, baseEnd_6366652] using wordTrace_append hprefix tailTrace_6366652
  have hstable : (prefixWord ++ tailWord_6366652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366652).length < 2 ^ (prefixWord ++ tailWord_6366652).sum := by decide
  have hdescent : baseEnd_6366652 < baseStart_6366652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366668 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6366668 : Nat := 118140960795 + 6366668 * 2 ^ 59
def prefixEnd_6366668 : Nat := 4983230072969 + 3 ^ 40 * 6366668 * 2
def baseEnd_6366668 : Nat := 3269160851599401615870233

theorem tailTrace_6366668 : CollatzResearch.WordTrace tailWord_6366668 prefixEnd_6366668 3269160851599401615870233 := by
  unfold tailWord_6366668
  simp only [CollatzResearch.WordTrace]
  refine ⟨116105729449328325585962329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154807639265771100781283105 116105729449328325585962329)
  ·
    refine ⟨87079297086996244189471747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116105729449328325585962329 87079297086996244189471747)
    ·
      refine ⟨130618945630494366284207621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87079297086996244189471747 130618945630494366284207621)
      ·
        refine ⟨24491052305717693678288929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130618945630494366284207621 24491052305717693678288929)
        ·
          refine ⟨18368289229288270258716697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491052305717693678288929 18368289229288270258716697)
          ·
            refine ⟨13776216921966202694037523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18368289229288270258716697 13776216921966202694037523)
            ·
              refine ⟨20664325382949304041056285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13776216921966202694037523 20664325382949304041056285)
              ·
                refine ⟨7749122018605989015396107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20664325382949304041056285 7749122018605989015396107)
                ·
                  refine ⟨11623683027908983523094161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749122018605989015396107 11623683027908983523094161)
                  ·
                    refine ⟨8717762270931737642320621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11623683027908983523094161 8717762270931737642320621)
                    ·
                      refine ⟨3269160851599401615870233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8717762270931737642320621 3269160851599401615870233)
                      ·
                        rfl

theorem cell23_6366668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6366668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366668 prefixEnd_6366668 := by exact prefixLift 6366668
  have htrace : WordTrace (prefixWord ++ tailWord_6366668) baseStart_6366668 baseEnd_6366668 := by
    simpa [prefixWord, tailWord_6366668, baseEnd_6366668] using wordTrace_append hprefix tailTrace_6366668
  have hstable : (prefixWord ++ tailWord_6366668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366668).length < 2 ^ (prefixWord ++ tailWord_6366668).sum := by decide
  have hdescent : baseEnd_6366668 < baseStart_6366668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366733 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6366733 : Nat := 118140960795 + 6366733 * 2 ^ 59
def prefixEnd_6366733 : Nat := 4983230072969 + 3 ^ 40 * 6366733 * 2
def baseEnd_6366733 : Nat := 3269194227841943861557435

theorem tailTrace_6366733 : CollatzResearch.WordTrace tailWord_6366733 prefixEnd_6366733 3269194227841943861557435 := by
  unfold tailWord_6366733
  simp only [CollatzResearch.WordTrace]
  refine ⟨232213829643421167273040853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154809219762280778182027235 232213829643421167273040853)
  ·
    refine ⟨5442511632267683607961895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 232213829643421167273040853 5442511632267683607961895)
    ·
      refine ⟨8163767448401525411942843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5442511632267683607961895 8163767448401525411942843)
      ·
        refine ⟨12245651172602288117914265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163767448401525411942843 12245651172602288117914265)
        ·
          refine ⟨9184238379451716088435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12245651172602288117914265 9184238379451716088435699)
          ·
            refine ⟨13776357569177574132653549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184238379451716088435699 13776357569177574132653549)
            ·
              refine ⟨5166134088441590299745081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13776357569177574132653549 5166134088441590299745081)
              ·
                refine ⟨3874600566331192724808811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5166134088441590299745081 3874600566331192724808811)
                ·
                  refine ⟨5811900849496789087213217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874600566331192724808811 5811900849496789087213217)
                  ·
                    refine ⟨4358925637122591815409913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5811900849496789087213217 4358925637122591815409913)
                    ·
                      refine ⟨3269194227841943861557435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4358925637122591815409913 3269194227841943861557435)
                      ·
                        rfl

theorem cell23_6366733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6366733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366733 prefixEnd_6366733 := by exact prefixLift 6366733
  have htrace : WordTrace (prefixWord ++ tailWord_6366733) baseStart_6366733 baseEnd_6366733 := by
    simpa [prefixWord, tailWord_6366733, baseEnd_6366733] using wordTrace_append hprefix tailTrace_6366733
  have hstable : (prefixWord ++ tailWord_6366733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366733).length < 2 ^ (prefixWord ++ tailWord_6366733).sum := by decide
  have hdescent : baseEnd_6366733 < baseStart_6366733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366855 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 1, 4]
def baseStart_6366855 : Nat := 118140960795 + 6366855 * 2 ^ 59
def prefixEnd_6366855 : Nat := 4983230072969 + 3 ^ 40 * 6366855 * 2
def baseEnd_6366855 : Nat := 1089752290827264128077291

theorem tailTrace_6366855 : CollatzResearch.WordTrace tailWord_6366855 prefixEnd_6366855 1089752290827264128077291 := by
  unfold tailWord_6366855
  simp only [CollatzResearch.WordTrace]
  refine ⟨232218279348979182108982019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154812186232652788072654679 232218279348979182108982019)
  ·
    refine ⟨348327419023468773163473029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232218279348979182108982019 348327419023468773163473029)
    ·
      refine ⟨65311391066900394968151193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348327419023468773163473029 65311391066900394968151193)
      ·
        refine ⟨48983543300175296226113395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65311391066900394968151193 48983543300175296226113395)
        ·
          refine ⟨73475314950262944339170093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48983543300175296226113395 73475314950262944339170093)
          ·
            refine ⟨27553243106348604127188785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73475314950262944339170093 27553243106348604127188785)
            ·
              refine ⟨20664932329761453095391589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27553243106348604127188785 20664932329761453095391589)
              ·
                refine ⟨3874674811830272455385923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20664932329761453095391589 3874674811830272455385923)
                ·
                  refine ⟨5812012217745408683078885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874674811830272455385923 5812012217745408683078885)
                  ·
                    refine ⟨1089752290827264128077291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812012217745408683078885 1089752290827264128077291)
                    ·
                      rfl

theorem cell23_6366855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_6366855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366855 prefixEnd_6366855 := by exact prefixLift 6366855
  have htrace : WordTrace (prefixWord ++ tailWord_6366855) baseStart_6366855 baseEnd_6366855 := by
    simpa [prefixWord, tailWord_6366855, baseEnd_6366855] using wordTrace_append hprefix tailTrace_6366855
  have hstable : (prefixWord ++ tailWord_6366855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366855).length < 2 ^ (prefixWord ++ tailWord_6366855).sum := by decide
  have hdescent : baseEnd_6366855 < baseStart_6366855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366898 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_6366898 : Nat := 118140960795 + 6366898 * 2 ^ 59
def prefixEnd_6366898 : Nat := 4983230072969 + 3 ^ 40 * 6366898 * 2
def baseEnd_6366898 : Nat := 1089759650716645238664725

theorem tailTrace_6366898 : CollatzResearch.WordTrace tailWord_6366898 prefixEnd_6366898 1089759650716645238664725 := by
  unfold tailWord_6366898
  simp only [CollatzResearch.WordTrace]
  refine ⟨58054961921955850113199337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154813231791882266968531565 58054961921955850113199337)
  ·
    refine ⟨43541221441466887584899503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58054961921955850113199337 43541221441466887584899503)
    ·
      refine ⟨65311832162200331377349255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43541221441466887584899503 65311832162200331377349255)
      ·
        refine ⟨97967748243300497066023883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65311832162200331377349255 97967748243300497066023883)
        ·
          refine ⟨146951622364950745599035825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97967748243300497066023883 146951622364950745599035825)
          ·
            refine ⟨110213716773713059199276869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146951622364950745599035825 110213716773713059199276869)
            ·
              refine ⟨20665071895071198599864413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110213716773713059199276869 20665071895071198599864413)
              ·
                refine ⟨7749401960651699474949155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20665071895071198599864413 7749401960651699474949155)
                ·
                  refine ⟨11624102940977549212423733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749401960651699474949155 11624102940977549212423733)
                  ·
                    refine ⟨1089759650716645238664725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11624102940977549212423733 1089759650716645238664725)
                    ·
                      rfl

theorem cell23_6366898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_6366898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366898 prefixEnd_6366898 := by exact prefixLift 6366898
  have htrace : WordTrace (prefixWord ++ tailWord_6366898) baseStart_6366898 baseEnd_6366898 := by
    simpa [prefixWord, tailWord_6366898, baseEnd_6366898] using wordTrace_append hprefix tailTrace_6366898
  have hstable : (prefixWord ++ tailWord_6366898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366898).length < 2 ^ (prefixWord ++ tailWord_6366898).sum := by decide
  have hdescent : baseEnd_6366898 < baseStart_6366898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366932 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_6366932 : Nat := 118140960795 + 6366932 * 2 ^ 59
def prefixEnd_6366932 : Nat := 4983230072969 + 3 ^ 40 * 6366932 * 2
def baseEnd_6366932 : Nat := 1089765470164062860989673

theorem tailTrace_6366932 : CollatzResearch.WordTrace tailWord_6366932 prefixEnd_6366932 1089765470164062860989673 := by
  unfold tailWord_6366932
  simp only [CollatzResearch.WordTrace]
  refine ⟨116110543884850112129767525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154814058513133482839690033 116110543884850112129767525)
  ·
    refine ⟨21770726978409396024331411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116110543884850112129767525 21770726978409396024331411)
    ·
      refine ⟨32656090467614094036497117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21770726978409396024331411 32656090467614094036497117)
      ·
        refine ⟨12246033925355285263686419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32656090467614094036497117 12246033925355285263686419)
        ·
          refine ⟨18369050888032927895529629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246033925355285263686419 18369050888032927895529629)
          ·
            refine ⟨6888394083012347960823611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18369050888032927895529629 6888394083012347960823611)
            ·
              refine ⟨10332591124518521941235417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888394083012347960823611 10332591124518521941235417)
              ·
                refine ⟨7749443343388891455926563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10332591124518521941235417 7749443343388891455926563)
                ·
                  refine ⟨11624165015083337183889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749443343388891455926563 11624165015083337183889845)
                  ·
                    refine ⟨1089765470164062860989673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11624165015083337183889845 1089765470164062860989673)
                    ·
                      rfl

theorem cell23_6366932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_6366932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366932 prefixEnd_6366932 := by exact prefixLift 6366932
  have htrace : WordTrace (prefixWord ++ tailWord_6366932) baseStart_6366932 baseEnd_6366932 := by
    simpa [prefixWord, tailWord_6366932, baseEnd_6366932] using wordTrace_append hprefix tailTrace_6366932
  have hstable : (prefixWord ++ tailWord_6366932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366932).length < 2 ^ (prefixWord ++ tailWord_6366932).sum := by decide
  have hdescent : baseEnd_6366932 < baseStart_6366932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366935 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_6366935 : Nat := 118140960795 + 6366935 * 2 ^ 59
def prefixEnd_6366935 : Nat := 4983230072969 + 3 ^ 40 * 6366935 * 2
def baseEnd_6366935 : Nat := 3269297950934152071231505

theorem tailTrace_6366935 : CollatzResearch.WordTrace tailWord_6366935 prefixEnd_6366935 3269297950934152071231505 := by
  unfold tailWord_6366935
  simp only [CollatzResearch.WordTrace]
  refine ⟨232221197188689355771894259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154814131459126237181262839 232221197188689355771894259)
  ·
    refine ⟨348331795783034033657841389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232221197188689355771894259 348331795783034033657841389)
    ·
      refine ⟨130624423418637762621690521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348331795783034033657841389 130624423418637762621690521)
      ·
        refine ⟨97968317563978321966267891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130624423418637762621690521 97968317563978321966267891)
        ·
          refine ⟨146952476345967482949401837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97968317563978321966267891 146952476345967482949401837)
          ·
            refine ⟨55107178629737806106025689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146952476345967482949401837 55107178629737806106025689)
            ·
              refine ⟨41330383972303354579519267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55107178629737806106025689 41330383972303354579519267)
              ·
                refine ⟨61995575958455031869278901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41330383972303354579519267 61995575958455031869278901)
                ·
                  refine ⟨5812085246105159237744897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61995575958455031869278901 5812085246105159237744897)
                  ·
                    refine ⟨4359063934578869428308673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812085246105159237744897 4359063934578869428308673)
                    ·
                      refine ⟨3269297950934152071231505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359063934578869428308673 3269297950934152071231505)
                      ·
                        rfl

theorem cell23_6366935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_6366935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366935 prefixEnd_6366935 := by exact prefixLift 6366935
  have htrace : WordTrace (prefixWord ++ tailWord_6366935) baseStart_6366935 baseEnd_6366935 := by
    simpa [prefixWord, tailWord_6366935, baseEnd_6366935] using wordTrace_append hprefix tailTrace_6366935
  have hstable : (prefixWord ++ tailWord_6366935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366935).length < 2 ^ (prefixWord ++ tailWord_6366935).sum := by decide
  have hdescent : baseEnd_6366935 < baseStart_6366935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366948 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_6366948 : Nat := 118140960795 + 6366948 * 2 ^ 59
def prefixEnd_6366948 : Nat := 4983230072969 + 3 ^ 40 * 6366948 * 2
def baseEnd_6366948 : Nat := 3269304626182660520368945

theorem tailTrace_6366948 : CollatzResearch.WordTrace tailWord_6366948 prefixEnd_6366948 3269304626182660520368945 := by
  unfold tailWord_6366948
  simp only [CollatzResearch.WordTrace]
  refine ⟨116110835668821129496058749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154814447558428172661411665 116110835668821129496058749)
  ·
    refine ⟨43541563375807923561022031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116110835668821129496058749 43541563375807923561022031)
    ·
      refine ⟨65312345063711885341533047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43541563375807923561022031 65312345063711885341533047)
      ·
        refine ⟨97968517595567828012299571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65312345063711885341533047 97968517595567828012299571)
        ·
          refine ⟨146952776393351742018449357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97968517595567828012299571 146952776393351742018449357)
          ·
            refine ⟨55107291147506903256918509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146952776393351742018449357 55107291147506903256918509)
            ·
              refine ⟨20665234180315088721344441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55107291147506903256918509 20665234180315088721344441)
              ·
                refine ⟨15498925635236316541008331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20665234180315088721344441 15498925635236316541008331)
                ·
                  refine ⟨23248388452854474811512497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15498925635236316541008331 23248388452854474811512497)
                  ·
                    refine ⟨17436291339640856108634373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23248388452854474811512497 17436291339640856108634373)
                    ·
                      refine ⟨3269304626182660520368945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17436291339640856108634373 3269304626182660520368945)
                      ·
                        rfl

theorem cell23_6366948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_6366948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366948 prefixEnd_6366948 := by exact prefixLift 6366948
  have htrace : WordTrace (prefixWord ++ tailWord_6366948) baseStart_6366948 baseEnd_6366948 := by
    simpa [prefixWord, tailWord_6366948, baseEnd_6366948] using wordTrace_append hprefix tailTrace_6366948
  have hstable : (prefixWord ++ tailWord_6366948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366948).length < 2 ^ (prefixWord ++ tailWord_6366948).sum := by decide
  have hdescent : baseEnd_6366948 < baseStart_6366948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366952 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6366952 : Nat := 118140960795 + 6366952 * 2 ^ 59
def prefixEnd_6366952 : Nat := 4983230072969 + 3 ^ 40 * 6366952 * 2
def baseEnd_6366952 : Nat := 3269306680105278504718927

theorem tailTrace_6366952 : CollatzResearch.WordTrace tailWord_6366952 prefixEnd_6366952 3269306680105278504718927 := by
  unfold tailWord_6366952
  simp only [CollatzResearch.WordTrace]
  refine ⟨116110908614813883837631555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154814544819751845116842073 116110908614813883837631555)
  ·
    refine ⟨174166362922220825756447333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116110908614813883837631555 174166362922220825756447333)
    ·
      refine ⟨32656193047916404829333875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174166362922220825756447333 32656193047916404829333875)
      ·
        refine ⟨48984289571874607244000813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32656193047916404829333875 48984289571874607244000813)
        ·
          refine ⟨18369108589452977716500305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48984289571874607244000813 18369108589452977716500305)
          ·
            refine ⟨13776831442089733287375229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18369108589452977716500305 13776831442089733287375229)
            ·
              refine ⟨5166311790783649982765711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13776831442089733287375229 5166311790783649982765711)
              ·
                refine ⟨7749467686175474974148567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166311790783649982765711 7749467686175474974148567)
                ·
                  refine ⟨11624201529263212461222851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749467686175474974148567 11624201529263212461222851)
                  ·
                    refine ⟨17436302293894818691834277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11624201529263212461222851 17436302293894818691834277)
                    ·
                      refine ⟨3269306680105278504718927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17436302293894818691834277 3269306680105278504718927)
                      ·
                        rfl

theorem cell23_6366952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6366952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366952 prefixEnd_6366952 := by exact prefixLift 6366952
  have htrace : WordTrace (prefixWord ++ tailWord_6366952) baseStart_6366952 baseEnd_6366952 := by
    simpa [prefixWord, tailWord_6366952, baseEnd_6366952] using wordTrace_append hprefix tailTrace_6366952
  have hstable : (prefixWord ++ tailWord_6366952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366952).length < 2 ^ (prefixWord ++ tailWord_6366952).sum := by decide
  have hdescent : baseEnd_6366952 < baseStart_6366952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366981 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_6366981 : Nat := 118140960795 + 6366981 * 2 ^ 59
def prefixEnd_6366981 : Nat := 4983230072969 + 3 ^ 40 * 6366981 * 2
def baseEnd_6366981 : Nat := 3269321571044258891256293

theorem tailTrace_6366981 : CollatzResearch.WordTrace tailWord_6366981 prefixEnd_6366981 3269321571044258891256293 := by
  unfold tailWord_6366981
  simp only [CollatzResearch.WordTrace]
  refine ⟨232222874946522705628068797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154815249964348470418712531 232222874946522705628068797)
  ·
    refine ⟨87083578104946014610525799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232222874946522705628068797 87083578104946014610525799)
    ·
      refine ⟨130625367157419021915788699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87083578104946014610525799 130625367157419021915788699)
      ·
        refine ⟨195938050736128532873683049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130625367157419021915788699 195938050736128532873683049)
        ·
          refine ⟨146953538052096399655262287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195938050736128532873683049 146953538052096399655262287)
          ·
            refine ⟨220430307078144599482893431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146953538052096399655262287 220430307078144599482893431)
            ·
              refine ⟨330645460617216899224340147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220430307078144599482893431 330645460617216899224340147)
              ·
                refine ⟨495968190925825348836510221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330645460617216899224340147 495968190925825348836510221)
                ·
                  refine ⟨185988071597184505813691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495968190925825348836510221 185988071597184505813691333)
                  ·
                    refine ⟨34872763424472094840067125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185988071597184505813691333 34872763424472094840067125)
                    ·
                      refine ⟨3269321571044258891256293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34872763424472094840067125 3269321571044258891256293)
                      ·
                        rfl

theorem cell23_6366981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_6366981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6366981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6366981 prefixEnd_6366981 := by exact prefixLift 6366981
  have htrace : WordTrace (prefixWord ++ tailWord_6366981) baseStart_6366981 baseEnd_6366981 := by
    simpa [prefixWord, tailWord_6366981, baseEnd_6366981] using wordTrace_append hprefix tailTrace_6366981
  have hstable : (prefixWord ++ tailWord_6366981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366981).length < 2 ^ (prefixWord ++ tailWord_6366981).sum := by decide
  have hdescent : baseEnd_6366981 < baseStart_6366981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367006 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6367006 : Nat := 118140960795 + 6367006 * 2 ^ 59
def prefixEnd_6367006 : Nat := 4983230072969 + 3 ^ 40 * 6367006 * 2
def baseEnd_6367006 : Nat := 3269334408060621293443679

theorem tailTrace_6367006 : CollatzResearch.WordTrace tailWord_6367006 prefixEnd_6367006 3269334408060621293443679 := by
  unfold tailWord_6367006
  simp only [CollatzResearch.WordTrace]
  refine ⟨29027973346429016862216109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154815857847621423265152581 29027973346429016862216109)
  ·
    refine ⟨10885490004910881323331041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29027973346429016862216109 10885490004910881323331041)
    ·
      refine ⟨8164117503683160992498281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10885490004910881323331041 8164117503683160992498281)
      ·
        refine ⟨6123088127762370744373711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8164117503683160992498281 6123088127762370744373711)
        ·
          refine ⟨9184632191643556116560567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123088127762370744373711 9184632191643556116560567)
          ·
            refine ⟨13776948287465334174840851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184632191643556116560567 13776948287465334174840851)
            ·
              refine ⟨20665422431198001262261277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13776948287465334174840851 20665422431198001262261277)
              ·
                refine ⟨7749533411699250473347979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20665422431198001262261277 7749533411699250473347979)
                ·
                  refine ⟨11624300117548875710021969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749533411699250473347979 11624300117548875710021969)
                  ·
                    refine ⟨8718225088161656782516477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11624300117548875710021969 8718225088161656782516477)
                    ·
                      refine ⟨3269334408060621293443679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8718225088161656782516477 3269334408060621293443679)
                      ·
                        rfl

theorem cell23_6367006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6367006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367006 prefixEnd_6367006 := by exact prefixLift 6367006
  have htrace : WordTrace (prefixWord ++ tailWord_6367006) baseStart_6367006 baseEnd_6367006 := by
    simpa [prefixWord, tailWord_6367006, baseEnd_6367006] using wordTrace_append hprefix tailTrace_6367006
  have hstable : (prefixWord ++ tailWord_6367006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367006).length < 2 ^ (prefixWord ++ tailWord_6367006).sum := by decide
  have hdescent : baseEnd_6367006 < baseStart_6367006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367046 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6367046 : Nat := 118140960795 + 6367046 * 2 ^ 59
def prefixEnd_6367046 : Nat := 4983230072969 + 3 ^ 40 * 6367046 * 2
def baseEnd_6367046 : Nat := 3269354947286801136943495

theorem tailTrace_6367046 : CollatzResearch.WordTrace tailWord_6367046 prefixEnd_6367046 3269354947286801136943495 := by
  unfold tailWord_6367046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257038927852725679037031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154816830460858147819456661 7257038927852725679037031)
  ·
    refine ⟨10885558391779088518555547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257038927852725679037031 10885558391779088518555547)
    ·
      refine ⟨16328337587668632777833321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885558391779088518555547 16328337587668632777833321)
      ·
        refine ⟨12246253190751474583374991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16328337587668632777833321 12246253190751474583374991)
        ·
          refine ⟨18369379786127211875062487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246253190751474583374991 18369379786127211875062487)
          ·
            refine ⟨27554069679190817812593731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18369379786127211875062487 27554069679190817812593731)
            ·
              refine ⟨41331104518786226718890597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27554069679190817812593731 41331104518786226718890597)
              ·
                refine ⟨7749582097272417509791987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41331104518786226718890597 7749582097272417509791987)
                ·
                  refine ⟨11624373145908626264687981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749582097272417509791987 11624373145908626264687981)
                  ·
                    refine ⟨4359139929715734849257993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11624373145908626264687981 4359139929715734849257993)
                    ·
                      refine ⟨3269354947286801136943495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359139929715734849257993 3269354947286801136943495)
                      ·
                        rfl

theorem cell23_6367046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6367046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367046 prefixEnd_6367046 := by exact prefixLift 6367046
  have htrace : WordTrace (prefixWord ++ tailWord_6367046) baseStart_6367046 baseEnd_6367046 := by
    simpa [prefixWord, tailWord_6367046, baseEnd_6367046] using wordTrace_append hprefix tailTrace_6367046
  have hstable : (prefixWord ++ tailWord_6367046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367046).length < 2 ^ (prefixWord ++ tailWord_6367046).sum := by decide
  have hdescent : baseEnd_6367046 < baseStart_6367046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367048 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 7]
def baseStart_6367048 : Nat := 118140960795 + 6367048 * 2 ^ 59
def prefixEnd_6367048 : Nat := 4983230072969 + 3 ^ 40 * 6367048 * 2
def baseEnd_6367048 : Nat := 363261774916456681013165

theorem tailTrace_6367048 : CollatzResearch.WordTrace tailWord_6367048 prefixEnd_6367048 363261774916456681013165 := by
  unfold tailWord_6367048
  simp only [CollatzResearch.WordTrace]
  refine ⟨116112659318639988035378899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154816879091519984047171865 116112659318639988035378899)
  ·
    refine ⟨174168988977959982053068349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116112659318639988035378899 174168988977959982053068349)
    ·
      refine ⟨65313370866734993269900631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174168988977959982053068349 65313370866734993269900631)
      ·
        refine ⟨97970056300102489904850947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65313370866734993269900631 97970056300102489904850947)
        ·
          refine ⟨146955084450153734857276421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97970056300102489904850947 146955084450153734857276421)
          ·
            refine ⟨27554078334403825285739329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146955084450153734857276421 27554078334403825285739329)
            ·
              refine ⟨20665558750802868964304497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27554078334403825285739329 20665558750802868964304497)
              ·
                refine ⟨15499169063102151723228373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20665558750802868964304497 15499169063102151723228373)
                ·
                  refine ⟨363261774916456681013165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15499169063102151723228373 363261774916456681013165)
                  ·
                    rfl

theorem cell23_6367048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_6367048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367048 prefixEnd_6367048 := by exact prefixLift 6367048
  have htrace : WordTrace (prefixWord ++ tailWord_6367048) baseStart_6367048 baseEnd_6367048 := by
    simpa [prefixWord, tailWord_6367048, baseEnd_6367048] using wordTrace_append hprefix tailTrace_6367048
  have hstable : (prefixWord ++ tailWord_6367048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367048).length < 2 ^ (prefixWord ++ tailWord_6367048).sum := by decide
  have hdescent : baseEnd_6367048 < baseStart_6367048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367098 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_6367098 : Nat := 118140960795 + 6367098 * 2 ^ 59
def prefixEnd_6367098 : Nat := 4983230072969 + 3 ^ 40 * 6367098 * 2
def baseEnd_6367098 : Nat := 3269381648280834933493255

theorem tailTrace_6367098 : CollatzResearch.WordTrace tailWord_6367098 prefixEnd_6367098 3269381648280834933493255 := by
  unfold tailWord_6367098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58056785571774708652519487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154818094858065889740051965 58056785571774708652519487)
  ·
    refine ⟨87085178357662062978779231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58056785571774708652519487 87085178357662062978779231)
    ·
      refine ⟨130627767536493094468168847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87085178357662062978779231 130627767536493094468168847)
      ·
        refine ⟨195941651304739641702253271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130627767536493094468168847 195941651304739641702253271)
        ·
          refine ⟨293912476957109462553379907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195941651304739641702253271 293912476957109462553379907)
          ·
            refine ⟨440868715435664193830069861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293912476957109462553379907 440868715435664193830069861)
            ·
              refine ⟨82662884144187036343138099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440868715435664193830069861 82662884144187036343138099)
              ·
                refine ⟨123994326216280554514707149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82662884144187036343138099 123994326216280554514707149)
                ·
                  refine ⟨46497872331105207943015181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123994326216280554514707149 46497872331105207943015181)
                  ·
                    refine ⟨17436702124164452978630693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46497872331105207943015181 17436702124164452978630693)
                    ·
                      refine ⟨3269381648280834933493255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17436702124164452978630693 3269381648280834933493255)
                      ·
                        rfl

theorem cell23_6367098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_6367098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367098 prefixEnd_6367098 := by exact prefixLift 6367098
  have htrace : WordTrace (prefixWord ++ tailWord_6367098) baseStart_6367098 baseEnd_6367098 := by
    simpa [prefixWord, tailWord_6367098, baseEnd_6367098] using wordTrace_append hprefix tailTrace_6367098
  have hstable : (prefixWord ++ tailWord_6367098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367098).length < 2 ^ (prefixWord ++ tailWord_6367098).sum := by decide
  have hdescent : baseEnd_6367098 < baseStart_6367098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367108 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_6367108 : Nat := 118140960795 + 6367108 * 2 ^ 59
def prefixEnd_6367108 : Nat := 4983230072969 + 3 ^ 40 * 6367108 * 2
def baseEnd_6367108 : Nat := 1089795594362459964789403

theorem tailTrace_6367108 : CollatzResearch.WordTrace tailWord_6367108 prefixEnd_6367108 1089795594362459964789403 := by
  unfold tailWord_6367108
  simp only [CollatzResearch.WordTrace]
  refine ⟨116113753508531303158970989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154818338011375070878627985 116113753508531303158970989)
  ·
    refine ⟨43542657565699238684614121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116113753508531303158970989 43542657565699238684614121)
    ·
      refine ⟨32656993174274429013460591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43542657565699238684614121 32656993174274429013460591)
      ·
        refine ⟨48985489761411643520190887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32656993174274429013460591 48985489761411643520190887)
        ·
          refine ⟨73478234642117465280286331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48985489761411643520190887 73478234642117465280286331)
          ·
            refine ⟨110217351963176197920429497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73478234642117465280286331 110217351963176197920429497)
            ·
              refine ⟨82663013972382148440322123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110217351963176197920429497 82663013972382148440322123)
              ·
                refine ⟨123994520958573222660483185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82663013972382148440322123 123994520958573222660483185)
                ·
                  refine ⟨92995890718929916995362389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123994520958573222660483185 92995890718929916995362389)
                  ·
                    refine ⟨1089795594362459964789403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92995890718929916995362389 1089795594362459964789403)
                    ·
                      rfl

theorem cell23_6367108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_6367108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367108 prefixEnd_6367108 := by exact prefixLift 6367108
  have htrace : WordTrace (prefixWord ++ tailWord_6367108) baseStart_6367108 baseEnd_6367108 := by
    simpa [prefixWord, tailWord_6367108, baseEnd_6367108] using wordTrace_append hprefix tailTrace_6367108
  have hstable : (prefixWord ++ tailWord_6367108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367108).length < 2 ^ (prefixWord ++ tailWord_6367108).sum := by decide
  have hdescent : baseEnd_6367108 < baseStart_6367108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367112 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_6367112 : Nat := 118140960795 + 6367112 * 2 ^ 59
def prefixEnd_6367112 : Nat := 4983230072969 + 3 ^ 40 * 6367112 * 2
def baseEnd_6367112 : Nat := 1089796279003332626239397

theorem tailTrace_6367112 : CollatzResearch.WordTrace tailWord_6367112 prefixEnd_6367112 1089796279003332626239397 := by
  unfold tailWord_6367112
  simp only [CollatzResearch.WordTrace]
  refine ⟨116113826454524057500543795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154818435272698743334058393 116113826454524057500543795)
  ·
    refine ⟨174170739681786086250815693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116113826454524057500543795 174170739681786086250815693)
    ·
      refine ⟨65314027380669782344055885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174170739681786086250815693 65314027380669782344055885)
      ·
        refine ⟨24492760267751168379020957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65314027380669782344055885 24492760267751168379020957)
        ·
          refine ⟨9184785100406688142132859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24492760267751168379020957 9184785100406688142132859)
          ·
            refine ⟨13777177650610032213199289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184785100406688142132859 13777177650610032213199289)
            ·
              refine ⟨10332883237957524159899467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13777177650610032213199289 10332883237957524159899467)
              ·
                refine ⟨15499324856936286239849201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10332883237957524159899467 15499324856936286239849201)
                ·
                  refine ⟨11624493642702214679886901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15499324856936286239849201 11624493642702214679886901)
                  ·
                    refine ⟨1089796279003332626239397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11624493642702214679886901 1089796279003332626239397)
                    ·
                      rfl

theorem cell23_6367112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_6367112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367112 prefixEnd_6367112 := by exact prefixLift 6367112
  have htrace : WordTrace (prefixWord ++ tailWord_6367112) baseStart_6367112 baseEnd_6367112 := by
    simpa [prefixWord, tailWord_6367112, baseEnd_6367112] using wordTrace_append hprefix tailTrace_6367112
  have hstable : (prefixWord ++ tailWord_6367112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367112).length < 2 ^ (prefixWord ++ tailWord_6367112).sum := by decide
  have hdescent : baseEnd_6367112 < baseStart_6367112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 4, 2]
def baseStart_6367115 : Nat := 118140960795 + 6367115 * 2 ^ 59
def prefixEnd_6367115 : Nat := 4983230072969 + 3 ^ 40 * 6367115 * 2
def baseEnd_6367115 : Nat := 3269390377451961366980677

theorem tailTrace_6367115 : CollatzResearch.WordTrace tailWord_6367115 prefixEnd_6367115 3269390377451961366980677 := by
  unfold tailWord_6367115
  simp only [CollatzResearch.WordTrace]
  refine ⟨232227762328037246513446799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154818508218691497675631199 232227762328037246513446799)
  ·
    refine ⟨348341643492055869770170199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232227762328037246513446799 348341643492055869770170199)
    ·
      refine ⟨522512465238083804655255299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348341643492055869770170199 522512465238083804655255299)
      ·
        refine ⟨783768697857125706982882949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522512465238083804655255299 783768697857125706982882949)
        ·
          refine ⟨146956630848211070059290553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 783768697857125706982882949 146956630848211070059290553)
          ·
            refine ⟨110217473136158302544467915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146956630848211070059290553 110217473136158302544467915)
            ·
              refine ⟨165326209704237453816701873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110217473136158302544467915 165326209704237453816701873)
              ·
                refine ⟨123994657278178090362526405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165326209704237453816701873 123994657278178090362526405)
                ·
                  refine ⟨23248998239658391942973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123994657278178090362526405 23248998239658391942973701)
                  ·
                    refine ⟨4359187169935948489307569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23248998239658391942973701 4359187169935948489307569)
                    ·
                      refine ⟨3269390377451961366980677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359187169935948489307569 3269390377451961366980677)
                      ·
                        rfl

theorem cell23_6367115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4, 2].length) (baseStart_6367115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367115 prefixEnd_6367115 := by exact prefixLift 6367115
  have htrace : WordTrace (prefixWord ++ tailWord_6367115) baseStart_6367115 baseEnd_6367115 := by
    simpa [prefixWord, tailWord_6367115, baseEnd_6367115] using wordTrace_append hprefix tailTrace_6367115
  have hstable : (prefixWord ++ tailWord_6367115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367115).length < 2 ^ (prefixWord ++ tailWord_6367115).sum := by decide
  have hdescent : baseEnd_6367115 < baseStart_6367115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367132 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6367132 : Nat := 118140960795 + 6367132 * 2 ^ 59
def prefixEnd_6367132 : Nat := 4983230072969 + 3 ^ 40 * 6367132 * 2
def baseEnd_6367132 : Nat := 3269399106623087800468099

theorem tailTrace_6367132 : CollatzResearch.WordTrace tailWord_6367132 prefixEnd_6367132 3269399106623087800468099 := by
  unfold tailWord_6367132
  simp only [CollatzResearch.WordTrace]
  refine ⟨116114191184487829208407825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154818921579317105611210433 116114191184487829208407825)
  ·
    refine ⟨87085643388365871906305869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116114191184487829208407825 87085643388365871906305869)
    ·
      refine ⟨32657116270637201964864701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87085643388365871906305869 32657116270637201964864701)
      ·
        refine ⟨12246418601488950736824263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32657116270637201964864701 12246418601488950736824263)
        ·
          refine ⟨18369627902233426105236395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246418601488950736824263 18369627902233426105236395)
          ·
            refine ⟨27554441853350139157854593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18369627902233426105236395 27554441853350139157854593)
            ·
              refine ⟨20665831390012604368390945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27554441853350139157854593 20665831390012604368390945)
              ·
                refine ⟨15499373542509453276293209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20665831390012604368390945 15499373542509453276293209)
                ·
                  refine ⟨11624530156882089957219907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15499373542509453276293209 11624530156882089957219907)
                  ·
                    refine ⟨17436795235323134935829861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11624530156882089957219907 17436795235323134935829861)
                    ·
                      refine ⟨3269399106623087800468099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17436795235323134935829861 3269399106623087800468099)
                      ·
                        rfl

theorem cell23_6367132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6367132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367132 prefixEnd_6367132 := by exact prefixLift 6367132
  have htrace : WordTrace (prefixWord ++ tailWord_6367132) baseStart_6367132 baseEnd_6367132 := by
    simpa [prefixWord, tailWord_6367132, baseEnd_6367132] using wordTrace_append hprefix tailTrace_6367132
  have hstable : (prefixWord ++ tailWord_6367132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367132).length < 2 ^ (prefixWord ++ tailWord_6367132).sum := by decide
  have hdescent : baseEnd_6367132 < baseStart_6367132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367182 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_6367182 : Nat := 118140960795 + 6367182 * 2 ^ 59
def prefixEnd_6367182 : Nat := 4983230072969 + 3 ^ 40 * 6367182 * 2
def baseEnd_6367182 : Nat := 3269424780655812604842869

theorem tailTrace_6367182 : CollatzResearch.WordTrace tailWord_6367182 prefixEnd_6367182 3269424780655812604842869 := by
  unfold tailWord_6367182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028775752349314619516975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154820137345863011304090533 29028775752349314619516975)
  ·
    refine ⟨43543163628523971929275463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29028775752349314619516975 43543163628523971929275463)
    ·
      refine ⟨65314745442785957893913195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43543163628523971929275463 65314745442785957893913195)
      ·
        refine ⟨97972118164178936840869793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65314745442785957893913195 97972118164178936840869793)
        ·
          refine ⟨73479088623134202630652345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97972118164178936840869793 73479088623134202630652345)
          ·
            refine ⟨55109316467350651972989259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73479088623134202630652345 55109316467350651972989259)
            ·
              refine ⟨82663974701025977959483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55109316467350651972989259 82663974701025977959483889)
              ·
                refine ⟨61997981025769483469612917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82663974701025977959483889 61997981025769483469612917)
                ·
                  refine ⟨5812310721165889075276211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61997981025769483469612917 5812310721165889075276211)
                  ·
                    refine ⟨8718466081748833612914317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5812310721165889075276211 8718466081748833612914317)
                    ·
                      refine ⟨3269424780655812604842869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8718466081748833612914317 3269424780655812604842869)
                      ·
                        rfl

theorem cell23_6367182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_6367182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367182 prefixEnd_6367182 := by exact prefixLift 6367182
  have htrace : WordTrace (prefixWord ++ tailWord_6367182) baseStart_6367182 baseEnd_6367182 := by
    simpa [prefixWord, tailWord_6367182, baseEnd_6367182] using wordTrace_append hprefix tailTrace_6367182
  have hstable : (prefixWord ++ tailWord_6367182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367182).length < 2 ^ (prefixWord ++ tailWord_6367182).sum := by decide
  have hdescent : baseEnd_6367182 < baseStart_6367182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367192 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_6367192 : Nat := 118140960795 + 6367192 * 2 ^ 59
def prefixEnd_6367192 : Nat := 4983230072969 + 3 ^ 40 * 6367192 * 2
def baseEnd_6367192 : Nat := 3269429915462357565717823

theorem tailTrace_6367192 : CollatzResearch.WordTrace tailWord_6367192 prefixEnd_6367192 3269429915462357565717823 := by
  unfold tailWord_6367192
  simp only [CollatzResearch.WordTrace]
  refine ⟨116115285374379144331999915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154820380499172192442666553 116115285374379144331999915)
  ·
    refine ⟨174172928061568716497999873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116115285374379144331999915 174172928061568716497999873)
    ·
      refine ⟨130629696046176537373499905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174172928061568716497999873 130629696046176537373499905)
      ·
        refine ⟨97972272034632403030124929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130629696046176537373499905 97972272034632403030124929)
        ·
          refine ⟨73479204025974302272593697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97972272034632403030124929 73479204025974302272593697)
          ·
            refine ⟨55109403019480726704445273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73479204025974302272593697 55109403019480726704445273)
            ·
              refine ⟨41332052264610545028333955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55109403019480726704445273 41332052264610545028333955)
              ·
                refine ⟨61998078396915817542500933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41332052264610545028333955 61998078396915817542500933)
                ·
                  refine ⟨11624639699421715789218925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61998078396915817542500933 11624639699421715789218925)
                  ·
                    refine ⟨4359239887283143420957097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11624639699421715789218925 4359239887283143420957097)
                    ·
                      refine ⟨3269429915462357565717823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359239887283143420957097 3269429915462357565717823)
                      ·
                        rfl

theorem cell23_6367192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_6367192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367192 prefixEnd_6367192 := by exact prefixLift 6367192
  have htrace : WordTrace (prefixWord ++ tailWord_6367192) baseStart_6367192 baseEnd_6367192 := by
    simpa [prefixWord, tailWord_6367192, baseEnd_6367192] using wordTrace_append hprefix tailTrace_6367192
  have hstable : (prefixWord ++ tailWord_6367192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367192).length < 2 ^ (prefixWord ++ tailWord_6367192).sum := by decide
  have hdescent : baseEnd_6367192 < baseStart_6367192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367199 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_6367199 : Nat := 118140960795 + 6367199 * 2 ^ 59
def prefixEnd_6367199 : Nat := 4983230072969 + 3 ^ 40 * 6367199 * 2
def baseEnd_6367199 : Nat := 3269433509826939038330291

theorem tailTrace_6367199 : CollatzResearch.WordTrace tailWord_6367199 prefixEnd_6367199 3269433509826939038330291 := by
  unfold tailWord_6367199
  simp only [CollatzResearch.WordTrace]
  refine ⟨232230826059732928859504651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154820550706488619239669767 232230826059732928859504651)
  ·
    refine ⟨348346239089599393289256977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232230826059732928859504651 348346239089599393289256977)
    ·
      refine ⟨261259679317199544966942733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348346239089599393289256977 261259679317199544966942733)
      ·
        refine ⟨97972379743949829362603525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261259679317199544966942733 97972379743949829362603525)
        ·
          refine ⟨18369821201990593005488161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97972379743949829362603525 18369821201990593005488161)
          ·
            refine ⟨13777365901492944754116121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18369821201990593005488161 13777365901492944754116121)
            ·
              refine ⟨10333024426119708565587091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13777365901492944754116121 10333024426119708565587091)
              ·
                refine ⟨15499536639179562848380637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333024426119708565587091 15499536639179562848380637)
                ·
                  refine ⟨5812326239692336068142739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15499536639179562848380637 5812326239692336068142739)
                  ·
                    refine ⟨8718489359538504102214109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5812326239692336068142739 8718489359538504102214109)
                    ·
                      refine ⟨3269433509826939038330291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8718489359538504102214109 3269433509826939038330291)
                      ·
                        rfl

theorem cell23_6367199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_6367199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367199 prefixEnd_6367199 := by exact prefixLift 6367199
  have htrace : WordTrace (prefixWord ++ tailWord_6367199) baseStart_6367199 baseEnd_6367199 := by
    simpa [prefixWord, tailWord_6367199, baseEnd_6367199] using wordTrace_append hprefix tailTrace_6367199
  have hstable : (prefixWord ++ tailWord_6367199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367199).length < 2 ^ (prefixWord ++ tailWord_6367199).sum := by decide
  have hdescent : baseEnd_6367199 < baseStart_6367199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367235 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_6367235 : Nat := 118140960795 + 6367235 * 2 ^ 59
def prefixEnd_6367235 : Nat := 4983230072969 + 3 ^ 40 * 6367235 * 2
def baseEnd_6367235 : Nat := 3269451995130500897480125

theorem tailTrace_6367235 : CollatzResearch.WordTrace tailWord_6367235 prefixEnd_6367235 3269451995130500897480125 := by
  unfold tailWord_6367235
  simp only [CollatzResearch.WordTrace]
  refine ⟨232232139087602507007815159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154821426058401671338543439 232232139087602507007815159)
  ·
    refine ⟨348348208631403760511722739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232232139087602507007815159 348348208631403760511722739)
    ·
      refine ⟨522522312947105640767584109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348348208631403760511722739 522522312947105640767584109)
      ·
        refine ⟨195945867355164615287844041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522522312947105640767584109 195945867355164615287844041)
        ·
          refine ⟨146959400516373461465883031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195945867355164615287844041 146959400516373461465883031)
          ·
            refine ⟨220439100774560192198824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146959400516373461465883031 220439100774560192198824547)
            ·
              refine ⟨330658651161840288298236821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220439100774560192198824547 330658651161840288298236821)
              ·
                refine ⟨15499624273211263513979851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 330658651161840288298236821 15499624273211263513979851)
                ·
                  refine ⟨23249436409816895270969777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15499624273211263513979851 23249436409816895270969777)
                  ·
                    refine ⟨17437077307362671453227333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23249436409816895270969777 17437077307362671453227333)
                    ·
                      refine ⟨3269451995130500897480125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17437077307362671453227333 3269451995130500897480125)
                      ·
                        rfl

theorem cell23_6367235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_6367235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367235 prefixEnd_6367235 := by exact prefixLift 6367235
  have htrace : WordTrace (prefixWord ++ tailWord_6367235) baseStart_6367235 baseEnd_6367235 := by
    simpa [prefixWord, tailWord_6367235, baseEnd_6367235] using wordTrace_append hprefix tailTrace_6367235
  have hstable : (prefixWord ++ tailWord_6367235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367235).length < 2 ^ (prefixWord ++ tailWord_6367235).sum := by decide
  have hdescent : baseEnd_6367235 < baseStart_6367235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367285 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6367285 : Nat := 118140960795 + 6367285 * 2 ^ 59
def prefixEnd_6367285 : Nat := 4983230072969 + 3 ^ 40 * 6367285 * 2
def baseEnd_6367285 : Nat := 3269477669163225701854895

theorem tailTrace_6367285 : CollatzResearch.WordTrace tailWord_6367285 prefixEnd_6367285 3269477669163225701854895 := by
  unfold tailWord_6367285
  simp only [CollatzResearch.WordTrace]
  refine ⟨232233962737421365547135309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154822641824947577031423539 232233962737421365547135309)
  ·
    refine ⟨87087736026533012080175741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232233962737421365547135309 87087736026533012080175741)
    ·
      refine ⟨32657901009949879530065903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87087736026533012080175741 32657901009949879530065903)
      ·
        refine ⟨48986851514924819295098855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32657901009949879530065903 48986851514924819295098855)
        ·
          refine ⟨73480277272387228942648283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48986851514924819295098855 73480277272387228942648283)
          ·
            refine ⟨110220415908580843413972425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73480277272387228942648283 110220415908580843413972425)
            ·
              refine ⟨82665311931435632560479319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110220415908580843413972425 82665311931435632560479319)
              ·
                refine ⟨123997967897153448840718979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82665311931435632560479319 123997967897153448840718979)
                ·
                  refine ⟨185996951845730173261078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123997967897153448840718979 185996951845730173261078469)
                  ·
                    refine ⟨34874428471074407486452213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185996951845730173261078469 34874428471074407486452213)
                    ·
                      refine ⟨3269477669163225701854895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34874428471074407486452213 3269477669163225701854895)
                      ·
                        rfl

theorem cell23_6367285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6367285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367285 prefixEnd_6367285 := by exact prefixLift 6367285
  have htrace : WordTrace (prefixWord ++ tailWord_6367285) baseStart_6367285 baseEnd_6367285 := by
    simpa [prefixWord, tailWord_6367285, baseEnd_6367285] using wordTrace_append hprefix tailTrace_6367285
  have hstable : (prefixWord ++ tailWord_6367285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367285).length < 2 ^ (prefixWord ++ tailWord_6367285).sum := by decide
  have hdescent : baseEnd_6367285 < baseStart_6367285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367289 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6367289 : Nat := 118140960795 + 6367289 * 2 ^ 59
def prefixEnd_6367289 : Nat := 4983230072969 + 3 ^ 40 * 6367289 * 2
def baseEnd_6367289 : Nat := 3269479723085843686204877

theorem tailTrace_6367289 : CollatzResearch.WordTrace tailWord_6367289 prefixEnd_6367289 3269479723085843686204877 := by
  unfold tailWord_6367289
  simp only [CollatzResearch.WordTrace]
  refine ⟨232234108629406874230280921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154822739086271249486853947 232234108629406874230280921)
  ·
    refine ⟨174175581472055155672710691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232234108629406874230280921 174175581472055155672710691)
    ·
      refine ⟨261263372208082733509066037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174175581472055155672710691 261263372208082733509066037)
      ·
        refine ⟨24493441144507756266474941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261263372208082733509066037 24493441144507756266474941)
        ·
          refine ⟨9185040429190408599928103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24493441144507756266474941 9185040429190408599928103)
          ·
            refine ⟨13777560643785612899892155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9185040429190408599928103 13777560643785612899892155)
            ·
              refine ⟨20666340965678419349838233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13777560643785612899892155 20666340965678419349838233)
              ·
                refine ⟨15499755724258814512378675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20666340965678419349838233 15499755724258814512378675)
                ·
                  refine ⟨23249633586388221768568013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15499755724258814512378675 23249633586388221768568013)
                  ·
                    refine ⟨8718612594895583163213005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23249633586388221768568013 8718612594895583163213005)
                    ·
                      refine ⟨3269479723085843686204877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8718612594895583163213005 3269479723085843686204877)
                      ·
                        rfl

theorem cell23_6367289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6367289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367289 prefixEnd_6367289 := by exact prefixLift 6367289
  have htrace : WordTrace (prefixWord ++ tailWord_6367289) baseStart_6367289 baseEnd_6367289 := by
    simpa [prefixWord, tailWord_6367289, baseEnd_6367289] using wordTrace_append hprefix tailTrace_6367289
  have hstable : (prefixWord ++ tailWord_6367289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367289).length < 2 ^ (prefixWord ++ tailWord_6367289).sum := by decide
  have hdescent : baseEnd_6367289 < baseStart_6367289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367305 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_6367305 : Nat := 118140960795 + 6367305 * 2 ^ 59
def prefixEnd_6367305 : Nat := 4983230072969 + 3 ^ 40 * 6367305 * 2
def baseEnd_6367305 : Nat := 1089829312925438541201601

theorem tailTrace_6367305 : CollatzResearch.WordTrace tailWord_6367305 prefixEnd_6367305 1089829312925438541201601 := by
  unfold tailWord_6367305
  simp only [CollatzResearch.WordTrace]
  refine ⟨232234692197348908962863369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154823128131565939308575579 232234692197348908962863369)
  ·
    refine ⟨174176019148011681722147527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232234692197348908962863369 174176019148011681722147527)
    ·
      refine ⟨261264028722017522583221291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174176019148011681722147527 261264028722017522583221291)
      ·
        refine ⟨391896043083026283874831937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261264028722017522583221291 391896043083026283874831937)
        ·
          refine ⟨293922032312269712906123953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391896043083026283874831937 293922032312269712906123953)
          ·
            refine ⟨220441524234202284679592965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293922032312269712906123953 220441524234202284679592965)
            ·
              refine ⟨41332785793912928377423681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220441524234202284679592965 41332785793912928377423681)
              ·
                refine ⟨30999589345434696283067761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41332785793912928377423681 30999589345434696283067761)
                ·
                  refine ⟨23249692009076022212300821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30999589345434696283067761 23249692009076022212300821)
                  ·
                    refine ⟨1089829312925438541201601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23249692009076022212300821 1089829312925438541201601)
                    ·
                      rfl

theorem cell23_6367305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_6367305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367305 prefixEnd_6367305 := by exact prefixLift 6367305
  have htrace : WordTrace (prefixWord ++ tailWord_6367305) baseStart_6367305 baseEnd_6367305 := by
    simpa [prefixWord, tailWord_6367305, baseEnd_6367305] using wordTrace_append hprefix tailTrace_6367305
  have hstable : (prefixWord ++ tailWord_6367305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367305).length < 2 ^ (prefixWord ++ tailWord_6367305).sum := by decide
  have hdescent : baseEnd_6367305 < baseStart_6367305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367329 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_6367329 : Nat := 118140960795 + 6367329 * 2 ^ 59
def prefixEnd_6367329 : Nat := 4983230072969 + 3 ^ 40 * 6367329 * 2
def baseEnd_6367329 : Nat := 3269500262312023529704693

theorem tailTrace_6367329 : CollatzResearch.WordTrace tailWord_6367329 prefixEnd_6367329 3269500262312023529704693 := by
  unfold tailWord_6367329
  simp only [CollatzResearch.WordTrace]
  refine ⟨232235567549261961061737041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154823711699507974041158027 232235567549261961061737041)
  ·
    refine ⟨174176675661946470796302781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232235567549261961061737041 174176675661946470796302781)
    ·
      refine ⟨65316253373229926548613543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174176675661946470796302781 65316253373229926548613543)
      ·
        refine ⟨97974380059844889822920315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65316253373229926548613543 97974380059844889822920315)
        ·
          refine ⟨146961570089767334734380473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97974380059844889822920315 146961570089767334734380473)
          ·
            refine ⟨110221177567325501050785355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146961570089767334734380473 110221177567325501050785355)
            ·
              refine ⟨165331766350988251576178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110221177567325501050785355 165331766350988251576178033)
              ·
                refine ⟨123998824763241188682133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165331766350988251576178033 123998824763241188682133525)
                ·
                  refine ⟨5812444910776930719475009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123998824763241188682133525 5812444910776930719475009)
                  ·
                    refine ⟨4359333683082698039606257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812444910776930719475009 4359333683082698039606257)
                    ·
                      refine ⟨3269500262312023529704693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359333683082698039606257 3269500262312023529704693)
                      ·
                        rfl

theorem cell23_6367329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_6367329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367329 prefixEnd_6367329 := by exact prefixLift 6367329
  have htrace : WordTrace (prefixWord ++ tailWord_6367329) baseStart_6367329 baseEnd_6367329 := by
    simpa [prefixWord, tailWord_6367329, baseEnd_6367329] using wordTrace_append hprefix tailTrace_6367329
  have hstable : (prefixWord ++ tailWord_6367329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367329).length < 2 ^ (prefixWord ++ tailWord_6367329).sum := by decide
  have hdescent : baseEnd_6367329 < baseStart_6367329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367342 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6367342 : Nat := 118140960795 + 6367342 * 2 ^ 59
def prefixEnd_6367342 : Nat := 4983230072969 + 3 ^ 40 * 6367342 * 2
def baseEnd_6367342 : Nat := 3269506937560531978842133

theorem tailTrace_6367342 : CollatzResearch.WordTrace tailWord_6367342 prefixEnd_6367342 3269506937560531978842133 := by
  unfold tailWord_6367342
  simp only [CollatzResearch.WordTrace]
  refine ⟨29029505212276858035245035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154824027798809909521306853 29029505212276858035245035)
  ·
    refine ⟨43544257818415287052867553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29029505212276858035245035 43544257818415287052867553)
    ·
      refine ⟨32658193363811465289650665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43544257818415287052867553 32658193363811465289650665)
      ·
        refine ⟨24493645022858598967237999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32658193363811465289650665 24493645022858598967237999)
        ·
          refine ⟨36740467534287898450856999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24493645022858598967237999 36740467534287898450856999)
          ·
            refine ⟨55110701301431847676285499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36740467534287898450856999 55110701301431847676285499)
            ·
              refine ⟨82666051952147771514428249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55110701301431847676285499 82666051952147771514428249)
              ·
                refine ⟨61999538964110828635821187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82666051952147771514428249 61999538964110828635821187)
                ·
                  refine ⟨92999308446166242953731781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61999538964110828635821187 92999308446166242953731781)
                  ·
                    refine ⟨17437370333656170553824709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92999308446166242953731781 17437370333656170553824709)
                    ·
                      refine ⟨3269506937560531978842133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17437370333656170553824709 3269506937560531978842133)
                      ·
                        rfl

theorem cell23_6367342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6367342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367342 prefixEnd_6367342 := by exact prefixLift 6367342
  have htrace : WordTrace (prefixWord ++ tailWord_6367342) baseStart_6367342 baseEnd_6367342 := by
    simpa [prefixWord, tailWord_6367342, baseEnd_6367342] using wordTrace_append hprefix tailTrace_6367342
  have hstable : (prefixWord ++ tailWord_6367342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367342).length < 2 ^ (prefixWord ++ tailWord_6367342).sum := by decide
  have hdescent : baseEnd_6367342 < baseStart_6367342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367350 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6367350 : Nat := 118140960795 + 6367350 * 2 ^ 59
def prefixEnd_6367350 : Nat := 4983230072969 + 3 ^ 40 * 6367350 * 2
def baseEnd_6367350 : Nat := 3269511045405767947542097

theorem tailTrace_6367350 : CollatzResearch.WordTrace tailWord_6367350 prefixEnd_6367350 3269511045405767947542097 := by
  unfold tailWord_6367350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14514770842636617603015719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154824222321457254432167669 14514770842636617603015719)
  ·
    refine ⟨21772156263954926404523579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14514770842636617603015719 21772156263954926404523579)
    ·
      refine ⟨32658234395932389606785369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21772156263954926404523579 32658234395932389606785369)
      ·
        refine ⟨24493675796949292205089027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32658234395932389606785369 24493675796949292205089027)
        ·
          refine ⟨36740513695423938307633541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24493675796949292205089027 36740513695423938307633541)
          ·
            refine ⟨6888846317891988432681289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36740513695423938307633541 6888846317891988432681289)
            ·
              refine ⟨5166634738418991324510967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888846317891988432681289 5166634738418991324510967)
              ·
                refine ⟨7749952107628486986766451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166634738418991324510967 7749952107628486986766451)
                ·
                  refine ⟨11624928161442730480149677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749952107628486986766451 11624928161442730480149677)
                  ·
                    refine ⟨4359348060541023930056129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11624928161442730480149677 4359348060541023930056129)
                    ·
                      refine ⟨3269511045405767947542097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359348060541023930056129 3269511045405767947542097)
                      ·
                        rfl

theorem cell23_6367350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6367350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367350 prefixEnd_6367350 := by exact prefixLift 6367350
  have htrace : WordTrace (prefixWord ++ tailWord_6367350) baseStart_6367350 baseEnd_6367350 := by
    simpa [prefixWord, tailWord_6367350, baseEnd_6367350] using wordTrace_append hprefix tailTrace_6367350
  have hstable : (prefixWord ++ tailWord_6367350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367350).length < 2 ^ (prefixWord ++ tailWord_6367350).sum := by decide
  have hdescent : baseEnd_6367350 < baseStart_6367350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367363 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 2, 2, 2]
def baseStart_6367363 : Nat := 118140960795 + 6367363 * 2 ^ 59
def prefixEnd_6367363 : Nat := 4983230072969 + 3 ^ 40 * 6367363 * 2
def baseEnd_6367363 : Nat := 3269517720654276396679537

theorem tailTrace_6367363 : CollatzResearch.WordTrace tailWord_6367363 prefixEnd_6367363 3269517720654276396679537 := by
  unfold tailWord_6367363
  simp only [CollatzResearch.WordTrace]
  refine ⟨232236807631138784868474743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154824538420759189912316495 232236807631138784868474743)
  ·
    refine ⟨348355211446708177302712115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232236807631138784868474743 348355211446708177302712115)
    ·
      refine ⟨522532817170062265954068173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348355211446708177302712115 522532817170062265954068173)
      ·
        refine ⟨195949806438773349732775565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522532817170062265954068173 195949806438773349732775565)
        ·
          refine ⟨73481177414540006149790837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195949806438773349732775565 73481177414540006149790837)
          ·
            refine ⟨6888860382613125576542891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73481177414540006149790837 6888860382613125576542891)
            ·
              refine ⟨10333290573919688364814337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888860382613125576542891 10333290573919688364814337)
              ·
                refine ⟨7749967930439766273610753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333290573919688364814337 7749967930439766273610753)
                ·
                  refine ⟨5812475947829824705208065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749967930439766273610753 5812475947829824705208065)
                  ·
                    refine ⟨4359356960872368528906049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812475947829824705208065 4359356960872368528906049)
                    ·
                      refine ⟨3269517720654276396679537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359356960872368528906049 3269517720654276396679537)
                      ·
                        rfl

theorem cell23_6367363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_6367363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367363 prefixEnd_6367363 := by exact prefixLift 6367363
  have htrace : WordTrace (prefixWord ++ tailWord_6367363) baseStart_6367363 baseEnd_6367363 := by
    simpa [prefixWord, tailWord_6367363, baseEnd_6367363] using wordTrace_append hprefix tailTrace_6367363
  have hstable : (prefixWord ++ tailWord_6367363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367363).length < 2 ^ (prefixWord ++ tailWord_6367363).sum := by decide
  have hdescent : baseEnd_6367363 < baseStart_6367363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367380 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6367380 : Nat := 118140960795 + 6367380 * 2 ^ 59
def prefixEnd_6367380 : Nat := 4983230072969 + 3 ^ 40 * 6367380 * 2
def baseEnd_6367380 : Nat := 3269526449825402830166959

theorem tailTrace_6367380 : CollatzResearch.WordTrace tailWord_6367380 prefixEnd_6367380 3269526449825402830166959 := by
  unfold tailWord_6367380
  simp only [CollatzResearch.WordTrace]
  refine ⟨116118713836038598385921797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154824951781384797847895729 116118713836038598385921797)
  ·
    refine ⟨21772258844257237197360337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116118713836038598385921797 21772258844257237197360337)
    ·
      refine ⟨16329194133192927898020253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21772258844257237197360337 16329194133192927898020253)
      ·
        refine ⟨6123447799947347961757595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16329194133192927898020253 6123447799947347961757595)
        ·
          refine ⟨9185171699921021942636393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123447799947347961757595 9185171699921021942636393)
          ·
            refine ⟨6888878774940766456977295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185171699921021942636393 6888878774940766456977295)
            ·
              refine ⟨10333318162411149685465943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888878774940766456977295 10333318162411149685465943)
              ·
                refine ⟨15499977243616724528198915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333318162411149685465943 15499977243616724528198915)
                ·
                  refine ⟨23249965865425086792298373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15499977243616724528198915 23249965865425086792298373)
                  ·
                    refine ⟨4359368599767203773555945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23249965865425086792298373 4359368599767203773555945)
                    ·
                      refine ⟨3269526449825402830166959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359368599767203773555945 3269526449825402830166959)
                      ·
                        rfl

theorem cell23_6367380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6367380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367380 prefixEnd_6367380 := by exact prefixLift 6367380
  have htrace : WordTrace (prefixWord ++ tailWord_6367380) baseStart_6367380 baseEnd_6367380 := by
    simpa [prefixWord, tailWord_6367380, baseEnd_6367380] using wordTrace_append hprefix tailTrace_6367380
  have hstable : (prefixWord ++ tailWord_6367380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367380).length < 2 ^ (prefixWord ++ tailWord_6367380).sum := by decide
  have hdescent : baseEnd_6367380 < baseStart_6367380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367426 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6367426 : Nat := 118140960795 + 6367426 * 2 ^ 59
def prefixEnd_6367426 : Nat := 4983230072969 + 3 ^ 40 * 6367426 * 2
def baseEnd_6367426 : Nat := 3269550069935509650191747

theorem tailTrace_6367426 : CollatzResearch.WordTrace tailWord_6367426 prefixEnd_6367426 3269550069935509650191747 := by
  unfold tailWord_6367426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58059776357477636657004533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154826070286607031085345421 58059776357477636657004533)
  ·
    refine ⟨5443104033513528436594175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58059776357477636657004533 5443104033513528436594175)
    ·
      refine ⟨8164656050270292654891263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443104033513528436594175 8164656050270292654891263)
      ·
        refine ⟨12246984075405438982336895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8164656050270292654891263 12246984075405438982336895)
        ·
          refine ⟨18370476113108158473505343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246984075405438982336895 18370476113108158473505343)
          ·
            refine ⟨27555714169662237710258015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18370476113108158473505343 27555714169662237710258015)
            ·
              refine ⟨41333571254493356565387023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27555714169662237710258015 41333571254493356565387023)
              ·
                refine ⟨62000356881740034848080535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41333571254493356565387023 62000356881740034848080535)
                ·
                  refine ⟨93000535322610052272120803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62000356881740034848080535 93000535322610052272120803)
                  ·
                    refine ⟨139500802983915078408181205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93000535322610052272120803 139500802983915078408181205)
                    ·
                      refine ⟨3269550069935509650191747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139500802983915078408181205 3269550069935509650191747)
                      ·
                        rfl

theorem cell23_6367426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6367426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367426 prefixEnd_6367426 := by exact prefixLift 6367426
  have htrace : WordTrace (prefixWord ++ tailWord_6367426) baseStart_6367426 baseEnd_6367426 := by
    simpa [prefixWord, tailWord_6367426, baseEnd_6367426] using wordTrace_append hprefix tailTrace_6367426
  have hstable : (prefixWord ++ tailWord_6367426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367426).length < 2 ^ (prefixWord ++ tailWord_6367426).sum := by decide
  have hdescent : baseEnd_6367426 < baseStart_6367426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367429 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_6367429 : Nat := 118140960795 + 6367429 * 2 ^ 59
def prefixEnd_6367429 : Nat := 4983230072969 + 3 ^ 40 * 6367429 * 2
def baseEnd_6367429 : Nat := 1089850536792491046151411

theorem tailTrace_6367429 : CollatzResearch.WordTrace tailWord_6367429 prefixEnd_6367429 1089850536792491046151411 := by
  unfold tailWord_6367429
  simp only [CollatzResearch.WordTrace]
  refine ⟨232239214848899678140377341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154826143232599785426918227 232239214848899678140377341)
  ·
    refine ⟨87089705568337379302641503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232239214848899678140377341 87089705568337379302641503)
    ·
      refine ⟨130634558352506068953962255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87089705568337379302641503 130634558352506068953962255)
      ·
        refine ⟨195951837528759103430943383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130634558352506068953962255 195951837528759103430943383)
        ·
          refine ⟨293927756293138655146415075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195951837528759103430943383 293927756293138655146415075)
          ·
            refine ⟨440891634439707982719622613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293927756293138655146415075 440891634439707982719622613)
            ·
              refine ⟨10333397682180655844991155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440891634439707982719622613 10333397682180655844991155)
              ·
                refine ⟨15500096523270983767486733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333397682180655844991155 15500096523270983767486733)
                ·
                  refine ⟨5812536196226618912807525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15500096523270983767486733 5812536196226618912807525)
                  ·
                    refine ⟨1089850536792491046151411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812536196226618912807525 1089850536792491046151411)
                    ·
                      rfl

theorem cell23_6367429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_6367429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367429 prefixEnd_6367429 := by exact prefixLift 6367429
  have htrace : WordTrace (prefixWord ++ tailWord_6367429) baseStart_6367429 baseEnd_6367429 := by
    simpa [prefixWord, tailWord_6367429, baseEnd_6367429] using wordTrace_append hprefix tailTrace_6367429
  have hstable : (prefixWord ++ tailWord_6367429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367429).length < 2 ^ (prefixWord ++ tailWord_6367429).sum := by decide
  have hdescent : baseEnd_6367429 < baseStart_6367429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367509 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6367509 : Nat := 118140960795 + 6367509 * 2 ^ 59
def prefixEnd_6367509 : Nat := 4983230072969 + 3 ^ 40 * 6367509 * 2
def baseEnd_6367509 : Nat := 3269592688829832825453865

theorem tailTrace_6367509 : CollatzResearch.WordTrace tailWord_6367509 prefixEnd_6367509 3269592688829832825453865 := by
  unfold tailWord_6367509
  simp only [CollatzResearch.WordTrace]
  refine ⟨232242132688609851803289581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154828088459073234535526387 232242132688609851803289581)
  ·
    refine ⟨87090799758228694426233593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232242132688609851803289581 87090799758228694426233593)
    ·
      refine ⟨65318099818671520819675195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87090799758228694426233593 65318099818671520819675195)
      ·
        refine ⟨97977149728007281229512793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65318099818671520819675195 97977149728007281229512793)
        ·
          refine ⟨73482862296005460922134595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97977149728007281229512793 73482862296005460922134595)
          ·
            refine ⟨110224293444008191383201893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73482862296005460922134595 110224293444008191383201893)
            ·
              refine ⟨20667055020751535884350355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110224293444008191383201893 20667055020751535884350355)
              ·
                refine ⟨31000582531127303826525533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20667055020751535884350355 31000582531127303826525533)
                ·
                  refine ⟨11625218449172738934947075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31000582531127303826525533 11625218449172738934947075)
                  ·
                    refine ⟨17437827673759108402420613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11625218449172738934947075 17437827673759108402420613)
                    ·
                      refine ⟨3269592688829832825453865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17437827673759108402420613 3269592688829832825453865)
                      ·
                        rfl

theorem cell23_6367509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6367509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367509 prefixEnd_6367509 := by exact prefixLift 6367509
  have htrace : WordTrace (prefixWord ++ tailWord_6367509) baseStart_6367509 baseEnd_6367509 := by
    simpa [prefixWord, tailWord_6367509, baseEnd_6367509] using wordTrace_append hprefix tailTrace_6367509
  have hstable : (prefixWord ++ tailWord_6367509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367509).length < 2 ^ (prefixWord ++ tailWord_6367509).sum := by decide
  have hdescent : baseEnd_6367509 < baseStart_6367509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367519 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 6]
def baseStart_6367519 : Nat := 118140960795 + 6367519 * 2 ^ 59
def prefixEnd_6367519 : Nat := 4983230072969 + 3 ^ 40 * 6367519 * 2
def baseEnd_6367519 : Nat := 1089865941212125928776273

theorem tailTrace_6367519 : CollatzResearch.WordTrace tailWord_6367519 prefixEnd_6367519 1089865941212125928776273 := by
  unfold tailWord_6367519
  simp only [CollatzResearch.WordTrace]
  refine ⟨232242497418573623511153611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154828331612382415674102407 232242497418573623511153611)
  ·
    refine ⟨348363746127860435266730417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232242497418573623511153611 348363746127860435266730417)
    ·
      refine ⟨261272809595895326450047813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348363746127860435266730417 261272809595895326450047813)
      ·
        refine ⟨48988651799230373709383965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261272809595895326450047813 48988651799230373709383965)
        ·
          refine ⟨18370744424711390141018987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48988651799230373709383965 18370744424711390141018987)
          ·
            refine ⟨27556116637067085211528481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18370744424711390141018987 27556116637067085211528481)
            ·
              refine ⟨20667087477800313908646361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27556116637067085211528481 20667087477800313908646361)
              ·
                refine ⟨15500315608350235431484771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20667087477800313908646361 15500315608350235431484771)
                ·
                  refine ⟨23250473412525353147227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15500315608350235431484771 23250473412525353147227157)
                  ·
                    refine ⟨1089865941212125928776273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23250473412525353147227157 1089865941212125928776273)
                    ·
                      rfl

theorem cell23_6367519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_6367519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367519 prefixEnd_6367519 := by exact prefixLift 6367519
  have htrace : WordTrace (prefixWord ++ tailWord_6367519) baseStart_6367519 baseEnd_6367519 := by
    simpa [prefixWord, tailWord_6367519, baseEnd_6367519] using wordTrace_append hprefix tailTrace_6367519
  have hstable : (prefixWord ++ tailWord_6367519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367519).length < 2 ^ (prefixWord ++ tailWord_6367519).sum := by decide
  have hdescent : baseEnd_6367519 < baseStart_6367519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367520 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6367520 : Nat := 118140960795 + 6367520 * 2 ^ 59
def prefixEnd_6367520 : Nat := 4983230072969 + 3 ^ 40 * 6367520 * 2
def baseEnd_6367520 : Nat := 3269598337117032282416315

theorem tailTrace_6367520 : CollatzResearch.WordTrace tailWord_6367520 prefixEnd_6367520 3269598337117032282416315 := by
  unfold tailWord_6367520
  simp only [CollatzResearch.WordTrace]
  refine ⟨116121266945785000340970007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154828355927713333787960009 116121266945785000340970007)
  ·
    refine ⟨174181900418677500511455011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116121266945785000340970007 174181900418677500511455011)
    ·
      refine ⟨261272850628016250767182517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174181900418677500511455011 261272850628016250767182517)
      ·
        refine ⟨24494329746376523509423361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261272850628016250767182517 24494329746376523509423361)
        ·
          refine ⟨18370747309782392632067521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24494329746376523509423361 18370747309782392632067521)
          ·
            refine ⟨13778060482336794474050641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18370747309782392632067521 13778060482336794474050641)
            ·
              refine ⟨10333545361752595855537981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13778060482336794474050641 10333545361752595855537981)
              ·
                refine ⟨3875079510657223445826743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10333545361752595855537981 3875079510657223445826743)
                ·
                  refine ⟨5812619265985835168740115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875079510657223445826743 5812619265985835168740115)
                  ·
                    refine ⟨8718928898978752753110173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5812619265985835168740115 8718928898978752753110173)
                    ·
                      refine ⟨3269598337117032282416315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8718928898978752753110173 3269598337117032282416315)
                      ·
                        rfl

theorem cell23_6367520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6367520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367520 prefixEnd_6367520 := by exact prefixLift 6367520
  have htrace : WordTrace (prefixWord ++ tailWord_6367520) baseStart_6367520 baseEnd_6367520 := by
    simpa [prefixWord, tailWord_6367520, baseEnd_6367520] using wordTrace_append hprefix tailTrace_6367520
  have hstable : (prefixWord ++ tailWord_6367520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367520).length < 2 ^ (prefixWord ++ tailWord_6367520).sum := by decide
  have hdescent : baseEnd_6367520 < baseStart_6367520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367527 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 6]
def baseStart_6367527 : Nat := 118140960795 + 6367527 * 2 ^ 59
def prefixEnd_6367527 : Nat := 4983230072969 + 3 ^ 40 * 6367527 * 2
def baseEnd_6367527 : Nat := 363289103497957083892087

theorem tailTrace_6367527 : CollatzResearch.WordTrace tailWord_6367527 prefixEnd_6367527 363289103497957083892087 := by
  unfold tailWord_6367527
  simp only [CollatzResearch.WordTrace]
  refine ⟨232242789202544640877444835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154828526135029760584963223 232242789202544640877444835)
  ·
    refine ⟨348364183803816961316167253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232242789202544640877444835 348364183803816961316167253)
    ·
      refine ⟨4082392778950980015423835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 348364183803816961316167253 4082392778950980015423835)
      ·
        refine ⟨6123589168426470023135753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082392778950980015423835 6123589168426470023135753)
        ·
          refine ⟨4592691876319852517351815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6123589168426470023135753 4592691876319852517351815)
          ·
            refine ⟨6889037814479778776027723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592691876319852517351815 6889037814479778776027723)
            ·
              refine ⟨10333556721719668164041585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889037814479778776027723 10333556721719668164041585)
              ·
                refine ⟨7750167541289751123031189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333556721719668164041585 7750167541289751123031189)
                ·
                  refine ⟨363289103497957083892087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7750167541289751123031189 363289103497957083892087)
                  ·
                    rfl

theorem cell23_6367527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 6].length) (baseStart_6367527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367527 prefixEnd_6367527 := by exact prefixLift 6367527
  have htrace : WordTrace (prefixWord ++ tailWord_6367527) baseStart_6367527 baseEnd_6367527 := by
    simpa [prefixWord, tailWord_6367527, baseEnd_6367527] using wordTrace_append hprefix tailTrace_6367527
  have hstable : (prefixWord ++ tailWord_6367527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367527).length < 2 ^ (prefixWord ++ tailWord_6367527).sum := by decide
  have hdescent : baseEnd_6367527 < baseStart_6367527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_6367552 : Nat := 118140960795 + 6367552 * 2 ^ 59
def prefixEnd_6367552 : Nat := 4983230072969 + 3 ^ 40 * 6367552 * 2
def baseEnd_6367552 : Nat := 3269614768497976157216167

theorem tailTrace_6367552 : CollatzResearch.WordTrace tailWord_6367552 prefixEnd_6367552 3269614768497976157216167 := by
  unfold tailWord_6367552
  simp only [CollatzResearch.WordTrace]
  refine ⟨116121850513727035073552455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154829134018302713431403273 116121850513727035073552455)
  ·
    refine ⟨174182775770590552610328683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116121850513727035073552455 174182775770590552610328683)
    ·
      refine ⟨261274163655885828915493025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174182775770590552610328683 261274163655885828915493025)
      ·
        refine ⟨195955622741914371686619769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261274163655885828915493025 195955622741914371686619769)
        ·
          refine ⟨146966717056435778764964827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195955622741914371686619769 146966717056435778764964827)
          ·
            refine ⟨220450075584653668147447241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146966717056435778764964827 220450075584653668147447241)
            ·
              refine ⟨165337556688490251110585431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220450075584653668147447241 165337556688490251110585431)
              ·
                refine ⟨248006335032735376665878147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165337556688490251110585431 248006335032735376665878147)
                ·
                  refine ⟨372009502549103064998817221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248006335032735376665878147 372009502549103064998817221)
                  ·
                    refine ⟨69751781727956824687278229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372009502549103064998817221 69751781727956824687278229)
                    ·
                      refine ⟨3269614768497976157216167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69751781727956824687278229 3269614768497976157216167)
                      ·
                        rfl

theorem cell23_6367552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_6367552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367552 prefixEnd_6367552 := by exact prefixLift 6367552
  have htrace : WordTrace (prefixWord ++ tailWord_6367552) baseStart_6367552 baseEnd_6367552 := by
    simpa [prefixWord, tailWord_6367552, baseEnd_6367552] using wordTrace_append hprefix tailTrace_6367552
  have hstable : (prefixWord ++ tailWord_6367552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367552).length < 2 ^ (prefixWord ++ tailWord_6367552).sum := by decide
  have hdescent : baseEnd_6367552 < baseStart_6367552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367553 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6367553 : Nat := 118140960795 + 6367553 * 2 ^ 59
def prefixEnd_6367553 : Nat := 4983230072969 + 3 ^ 40 * 6367553 * 2
def baseEnd_6367553 : Nat := 1089871760659543551101221

theorem tailTrace_6367553 : CollatzResearch.WordTrace tailWord_6367553 prefixEnd_6367553 1089871760659543551101221 := by
  unfold tailWord_6367553
  simp only [CollatzResearch.WordTrace]
  refine ⟨232243737500450447317891313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154829158333633631545260875 232243737500450447317891313)
  ·
    refine ⟨174182803125337835488418485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232243737500450447317891313 174182803125337835488418485)
    ·
      refine ⟨16329637793000422077039233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174182803125337835488418485 16329637793000422077039233)
      ·
        refine ⟨12247228344750316557779425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16329637793000422077039233 12247228344750316557779425)
        ·
          refine ⟨9185421258562737418334569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12247228344750316557779425 9185421258562737418334569)
          ·
            refine ⟨6889065943922053063750927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185421258562737418334569 6889065943922053063750927)
            ·
              refine ⟨10333598915883079595626391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889065943922053063750927 10333598915883079595626391)
              ·
                refine ⟨15500398373824619393439587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333598915883079595626391 15500398373824619393439587)
                ·
                  refine ⟨23250597560736929090159381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15500398373824619393439587 23250597560736929090159381)
                  ·
                    refine ⟨1089871760659543551101221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23250597560736929090159381 1089871760659543551101221)
                    ·
                      rfl

theorem cell23_6367553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6367553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367553 prefixEnd_6367553 := by exact prefixLift 6367553
  have htrace : WordTrace (prefixWord ++ tailWord_6367553) baseStart_6367553 baseEnd_6367553 := by
    simpa [prefixWord, tailWord_6367553, baseEnd_6367553] using wordTrace_append hprefix tailTrace_6367553
  have hstable : (prefixWord ++ tailWord_6367553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367553).length < 2 ^ (prefixWord ++ tailWord_6367553).sum := by decide
  have hdescent : baseEnd_6367553 < baseStart_6367553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367594 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6367594 : Nat := 118140960795 + 6367594 * 2 ^ 59
def prefixEnd_6367594 : Nat := 4983230072969 + 3 ^ 40 * 6367594 * 2
def baseEnd_6367594 : Nat := 3269636334685464992890975

theorem tailTrace_6367594 : CollatzResearch.WordTrace tailWord_6367594 prefixEnd_6367594 3269636334685464992890975 := by
  unfold tailWord_6367594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58061308223325477830033459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154830155262201274213422557 58061308223325477830033459)
  ·
    refine ⟨87091962334988216745050189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58061308223325477830033459 87091962334988216745050189)
    ·
      refine ⟨32659485875620581279393821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87091962334988216745050189 32659485875620581279393821)
      ·
        refine ⟨12247307203357717979772683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32659485875620581279393821 12247307203357717979772683)
        ·
          refine ⟨18370960805036576969659025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12247307203357717979772683 18370960805036576969659025)
          ·
            refine ⟨13778220603777432727244269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18370960805036576969659025 13778220603777432727244269)
            ·
              refine ⟨5166832726416537272716601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13778220603777432727244269 5166832726416537272716601)
              ·
                refine ⟨3875124544812402954537451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5166832726416537272716601 3875124544812402954537451)
                ·
                  refine ⟨5812686817218604431806177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875124544812402954537451 5812686817218604431806177)
                  ·
                    refine ⟨4359515112913953323854633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812686817218604431806177 4359515112913953323854633)
                    ·
                      refine ⟨3269636334685464992890975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359515112913953323854633 3269636334685464992890975)
                      ·
                        rfl

theorem cell23_6367594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6367594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367594 prefixEnd_6367594 := by exact prefixLift 6367594
  have htrace : WordTrace (prefixWord ++ tailWord_6367594) baseStart_6367594 baseEnd_6367594 := by
    simpa [prefixWord, tailWord_6367594, baseEnd_6367594] using wordTrace_append hprefix tailTrace_6367594
  have hstable : (prefixWord ++ tailWord_6367594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367594).length < 2 ^ (prefixWord ++ tailWord_6367594).sum := by decide
  have hdescent : baseEnd_6367594 < baseStart_6367594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367666 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_6367666 : Nat := 118140960795 + 6367666 * 2 ^ 59
def prefixEnd_6367666 : Nat := 4983230072969 + 3 ^ 40 * 6367666 * 2
def baseEnd_6367666 : Nat := 3269673305292588711190643

theorem tailTrace_6367666 : CollatzResearch.WordTrace tailWord_6367666 prefixEnd_6367666 3269673305292588711190643 := by
  unfold tailWord_6367666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58061964737260266904188713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154831905966027378411169901 58061964737260266904188713)
  ·
    refine ⟨43546473552945200178141535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58061964737260266904188713 43546473552945200178141535)
    ·
      refine ⟨65319710329417800267212303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43546473552945200178141535 65319710329417800267212303)
      ·
        refine ⟨97979565494126700400818455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65319710329417800267212303 97979565494126700400818455)
        ·
          refine ⟨146969348241190050601227683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97979565494126700400818455 146969348241190050601227683)
          ·
            refine ⟨220454022361785075901841525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146969348241190050601227683 220454022361785075901841525)
            ·
              refine ⟨20667564596417350865797643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220454022361785075901841525 20667564596417350865797643)
              ·
                refine ⟨31001346894626026298696465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20667564596417350865797643 31001346894626026298696465)
                ·
                  refine ⟨23251010170969519724022349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31001346894626026298696465 23251010170969519724022349)
                  ·
                    refine ⟨8719128814113569896508381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23251010170969519724022349 8719128814113569896508381)
                    ·
                      refine ⟨3269673305292588711190643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719128814113569896508381 3269673305292588711190643)
                      ·
                        rfl

theorem cell23_6367666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_6367666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367666 prefixEnd_6367666 := by exact prefixLift 6367666
  have htrace : WordTrace (prefixWord ++ tailWord_6367666) baseStart_6367666 baseEnd_6367666 := by
    simpa [prefixWord, tailWord_6367666, baseEnd_6367666] using wordTrace_append hprefix tailTrace_6367666
  have hstable : (prefixWord ++ tailWord_6367666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367666).length < 2 ^ (prefixWord ++ tailWord_6367666).sum := by decide
  have hdescent : baseEnd_6367666 < baseStart_6367666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367706 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_6367706 : Nat := 118140960795 + 6367706 * 2 ^ 59
def prefixEnd_6367706 : Nat := 4983230072969 + 3 ^ 40 * 6367706 * 2
def baseEnd_6367706 : Nat := 3269693844518768554690459

theorem tailTrace_6367706 : CollatzResearch.WordTrace tailWord_6367706 prefixEnd_6367706 3269693844518768554690459 := by
  unfold tailWord_6367706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58062329467224038612052743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154832878579264102965473981 58062329467224038612052743)
  ·
    refine ⟨87093494200836057918079115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58062329467224038612052743 87093494200836057918079115)
    ·
      refine ⟨130640241301254086877118673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87093494200836057918079115 130640241301254086877118673)
      ·
        refine ⟨97980180975940565157839005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130640241301254086877118673 97980180975940565157839005)
        ·
          refine ⟨36742567865977711934189627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97980180975940565157839005 36742567865977711934189627)
          ·
            refine ⟨55113851798966567901284441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36742567865977711934189627 55113851798966567901284441)
            ·
              refine ⟨41335388849224925925963331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55113851798966567901284441 41335388849224925925963331)
              ·
                refine ⟨62003083273837388888944997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41335388849224925925963331 62003083273837388888944997)
                ·
                  refine ⟨11625578113844510416677187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62003083273837388888944997 11625578113844510416677187)
                  ·
                    refine ⟨17438367170766765625015781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11625578113844510416677187 17438367170766765625015781)
                    ·
                      refine ⟨3269693844518768554690459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17438367170766765625015781 3269693844518768554690459)
                      ·
                        rfl

theorem cell23_6367706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_6367706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367706 prefixEnd_6367706 := by exact prefixLift 6367706
  have htrace : WordTrace (prefixWord ++ tailWord_6367706) baseStart_6367706 baseEnd_6367706 := by
    simpa [prefixWord, tailWord_6367706, baseEnd_6367706] using wordTrace_append hprefix tailTrace_6367706
  have hstable : (prefixWord ++ tailWord_6367706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367706).length < 2 ^ (prefixWord ++ tailWord_6367706).sum := by decide
  have hdescent : baseEnd_6367706 < baseStart_6367706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367757 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6367757 : Nat := 118140960795 + 6367757 * 2 ^ 59
def prefixEnd_6367757 : Nat := 4983230072969 + 3 ^ 40 * 6367757 * 2
def baseEnd_6367757 : Nat := 3269720032032147855152725

theorem tailTrace_6367757 : CollatzResearch.WordTrace tailWord_6367757 prefixEnd_6367757 3269720032032147855152725 := by
  unfold tailWord_6367757
  simp only [CollatzResearch.WordTrace]
  refine ⟨232251177991711390158317525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154834118661140926772211683 232251177991711390158317525)
  ·
    refine ⟨5443386984180735706835567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 232251177991711390158317525 5443386984180735706835567)
    ·
      refine ⟨8165080476271103560253351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443386984180735706835567 8165080476271103560253351)
      ·
        refine ⟨12247620714406655340380027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8165080476271103560253351 12247620714406655340380027)
        ·
          refine ⟨18371431071609983010570041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12247620714406655340380027 18371431071609983010570041)
          ·
            refine ⟨13778573303707487257927531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18371431071609983010570041 13778573303707487257927531)
            ·
              refine ⟨20667859955561230886891297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13778573303707487257927531 20667859955561230886891297)
              ·
                refine ⟨15500894966670923165168473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20667859955561230886891297 15500894966670923165168473)
                ·
                  refine ⟨11625671225003192373876355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15500894966670923165168473 11625671225003192373876355)
                  ·
                    refine ⟨17438506837504788560814533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11625671225003192373876355 17438506837504788560814533)
                    ·
                      refine ⟨3269720032032147855152725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17438506837504788560814533 3269720032032147855152725)
                      ·
                        rfl

theorem cell23_6367757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6367757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367757 prefixEnd_6367757 := by exact prefixLift 6367757
  have htrace : WordTrace (prefixWord ++ tailWord_6367757) baseStart_6367757 baseEnd_6367757 := by
    simpa [prefixWord, tailWord_6367757, baseEnd_6367757] using wordTrace_append hprefix tailTrace_6367757
  have hstable : (prefixWord ++ tailWord_6367757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367757).length < 2 ^ (prefixWord ++ tailWord_6367757).sum := by decide
  have hdescent : baseEnd_6367757 < baseStart_6367757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367767 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 3, 4]
def baseStart_6367767 : Nat := 118140960795 + 6367767 * 2 ^ 59
def prefixEnd_6367767 : Nat := 4983230072969 + 3 ^ 40 * 6367767 * 2
def baseEnd_6367767 : Nat := 1089908388946230938675893

theorem tailTrace_6367767 : CollatzResearch.WordTrace tailWord_6367767 prefixEnd_6367767 1089908388946230938675893 := by
  unfold tailWord_6367767
  simp only [CollatzResearch.WordTrace]
  refine ⟨232251542721675161866181555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154834361814450107910787703 232251542721675161866181555)
  ·
    refine ⟨348377314082512742799272333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232251542721675161866181555 348377314082512742799272333)
    ·
      refine ⟨130641492780942278549727125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348377314082512742799272333 130641492780942278549727125)
      ·
        refine ⟨6123819974106669307018459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130641492780942278549727125 6123819974106669307018459)
        ·
          refine ⟨9185729961160003960527689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123819974106669307018459 9185729961160003960527689)
          ·
            refine ⟨6889297470870002970395767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185729961160003960527689 6889297470870002970395767)
            ·
              refine ⟨10333946206305004455593651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889297470870002970395767 10333946206305004455593651)
              ·
                refine ⟨15500919309457506683390477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333946206305004455593651 15500919309457506683390477)
                ·
                  refine ⟨5812844741046565006271429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15500919309457506683390477 5812844741046565006271429)
                  ·
                    refine ⟨1089908388946230938675893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812844741046565006271429 1089908388946230938675893)
                    ·
                      rfl

theorem cell23_6367767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_6367767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367767 prefixEnd_6367767 := by exact prefixLift 6367767
  have htrace : WordTrace (prefixWord ++ tailWord_6367767) baseStart_6367767 baseEnd_6367767 := by
    simpa [prefixWord, tailWord_6367767, baseEnd_6367767] using wordTrace_append hprefix tailTrace_6367767
  have hstable : (prefixWord ++ tailWord_6367767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367767).length < 2 ^ (prefixWord ++ tailWord_6367767).sum := by decide
  have hdescent : baseEnd_6367767 < baseStart_6367767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367780 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 6]
def baseStart_6367780 : Nat := 118140960795 + 6367780 * 2 ^ 59
def prefixEnd_6367780 : Nat := 4983230072969 + 3 ^ 40 * 6367780 * 2
def baseEnd_6367780 : Nat := 363303538009689029462791

theorem tailTrace_6367780 : CollatzResearch.WordTrace tailWord_6367780 prefixEnd_6367780 363303538009689029462791 := by
  unfold tailWord_6367780
  simp only [CollatzResearch.WordTrace]
  refine ⟨116126008435314032543202397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154834677913752043390936529 116126008435314032543202397)
  ·
    refine ⟨43547253163242762203700899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116126008435314032543202397 43547253163242762203700899)
    ·
      refine ⟨65320879744864143305551349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43547253163242762203700899 65320879744864143305551349)
      ·
        refine ⟨6123832476081013434895439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65320879744864143305551349 6123832476081013434895439)
        ·
          refine ⟨9185748714121520152343159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123832476081013434895439 9185748714121520152343159)
          ·
            refine ⟨13778623071182280228514739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9185748714121520152343159 13778623071182280228514739)
            ·
              refine ⟨20667934606773420342772109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13778623071182280228514739 20667934606773420342772109)
              ·
                refine ⟨7750475477540032628539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20667934606773420342772109 7750475477540032628539541)
                ·
                  refine ⟨363303538009689029462791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7750475477540032628539541 363303538009689029462791)
                  ·
                    rfl

theorem cell23_6367780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_6367780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367780 prefixEnd_6367780 := by exact prefixLift 6367780
  have htrace : WordTrace (prefixWord ++ tailWord_6367780) baseStart_6367780 baseEnd_6367780 := by
    simpa [prefixWord, tailWord_6367780, baseEnd_6367780] using wordTrace_append hprefix tailTrace_6367780
  have hstable : (prefixWord ++ tailWord_6367780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367780).length < 2 ^ (prefixWord ++ tailWord_6367780).sum := by decide
  have hdescent : baseEnd_6367780 < baseStart_6367780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367793 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_6367793 : Nat := 118140960795 + 6367793 * 2 ^ 59
def prefixEnd_6367793 : Nat := 4983230072969 + 3 ^ 40 * 6367793 * 2
def baseEnd_6367793 : Nat := 1089912839111903238100853

theorem tailTrace_6367793 : CollatzResearch.WordTrace tailWord_6367793 prefixEnd_6367793 1089912839111903238100853 := by
  unfold tailWord_6367793
  simp only [CollatzResearch.WordTrace]
  refine ⟨232252491019580968306628033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154834994013053978871085355 232252491019580968306628033)
  ·
    refine ⟨174189368264685726229971025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232252491019580968306628033 174189368264685726229971025)
    ·
      refine ⟨130642026198514294672478269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174189368264685726229971025 130642026198514294672478269)
      ·
        refine ⟨48990759824442860502179351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130642026198514294672478269 48990759824442860502179351)
        ·
          refine ⟨73486139736664290753269027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48990759824442860502179351 73486139736664290753269027)
          ·
            refine ⟨110229209604996436129903541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73486139736664290753269027 110229209604996436129903541)
            ·
              refine ⟨10333988400468415887178457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110229209604996436129903541 10333988400468415887178457)
              ·
                refine ⟨7750491300351311915383843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333988400468415887178457 7750491300351311915383843)
                ·
                  refine ⟨11625736950526967873075765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7750491300351311915383843 11625736950526967873075765)
                  ·
                    refine ⟨1089912839111903238100853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11625736950526967873075765 1089912839111903238100853)
                    ·
                      rfl

theorem cell23_6367793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_6367793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367793 prefixEnd_6367793 := by exact prefixLift 6367793
  have htrace : WordTrace (prefixWord ++ tailWord_6367793) baseStart_6367793 baseEnd_6367793 := by
    simpa [prefixWord, tailWord_6367793, baseEnd_6367793] using wordTrace_append hprefix tailTrace_6367793
  have hstable : (prefixWord ++ tailWord_6367793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367793).length < 2 ^ (prefixWord ++ tailWord_6367793).sum := by decide
  have hdescent : baseEnd_6367793 < baseStart_6367793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367800 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_6367800 : Nat := 118140960795 + 6367800 * 2 ^ 59
def prefixEnd_6367800 : Nat := 4983230072969 + 3 ^ 40 * 6367800 * 2
def baseEnd_6367800 : Nat := 3269742111700291186915027

theorem tailTrace_6367800 : CollatzResearch.WordTrace tailWord_6367800 prefixEnd_6367800 3269742111700291186915027 := by
  unfold tailWord_6367800
  simp only [CollatzResearch.WordTrace]
  refine ⟨116126373165277804251066427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154835164220370405668088569 116126373165277804251066427)
  ·
    refine ⟨174189559747916706376599641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116126373165277804251066427 174189559747916706376599641)
    ·
      refine ⟨130642169810937529782449731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174189559747916706376599641 130642169810937529782449731)
      ·
        refine ⟨195963254716406294673674597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130642169810937529782449731 195963254716406294673674597)
        ·
          refine ⟨36743110259326180251313987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195963254716406294673674597 36743110259326180251313987)
          ·
            refine ⟨55114665388989270376970981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36743110259326180251313987 55114665388989270376970981)
            ·
              refine ⟨10333999760435488195682059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55114665388989270376970981 10333999760435488195682059)
              ·
                refine ⟨15500999640653232293523089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333999760435488195682059 15500999640653232293523089)
                ·
                  refine ⟨11625749730489924220142317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15500999640653232293523089 11625749730489924220142317)
                  ·
                    refine ⟨4359656148933721582553369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11625749730489924220142317 4359656148933721582553369)
                    ·
                      refine ⟨3269742111700291186915027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359656148933721582553369 3269742111700291186915027)
                      ·
                        rfl

theorem cell23_6367800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_6367800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367800 prefixEnd_6367800 := by exact prefixLift 6367800
  have htrace : WordTrace (prefixWord ++ tailWord_6367800) baseStart_6367800 baseEnd_6367800 := by
    simpa [prefixWord, tailWord_6367800, baseEnd_6367800] using wordTrace_append hprefix tailTrace_6367800
  have hstable : (prefixWord ++ tailWord_6367800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367800).length < 2 ^ (prefixWord ++ tailWord_6367800).sum := by decide
  have hdescent : baseEnd_6367800 < baseStart_6367800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367823 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 2, 4]
def baseStart_6367823 : Nat := 118140960795 + 6367823 * 2 ^ 59
def prefixEnd_6367823 : Nat := 4983230072969 + 3 ^ 40 * 6367823 * 2
def baseEnd_6367823 : Nat := 1089917973918448198975807

theorem tailTrace_6367823 : CollatzResearch.WordTrace tailWord_6367823 prefixEnd_6367823 1089917973918448198975807 := by
  unfold tailWord_6367823
  simp only [CollatzResearch.WordTrace]
  refine ⟨232253585209472283430220123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154835723472981522286813415 232253585209472283430220123)
  ·
    refine ⟨348380377814208425145330185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232253585209472283430220123 348380377814208425145330185)
    ·
      refine ⟨261285283360656318858997639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348380377814208425145330185 261285283360656318858997639)
      ·
        refine ⟨391927925040984478288496459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261285283360656318858997639 391927925040984478288496459)
        ·
          refine ⟨587891887561476717432744689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391927925040984478288496459 587891887561476717432744689)
          ·
            refine ⟨440918915671107538074558517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587891887561476717432744689 440918915671107538074558517)
            ·
              refine ⟨41336148344166331694489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 440918915671107538074558517 41336148344166331694489861)
              ·
                refine ⟨7750527814531187192716849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41336148344166331694489861 7750527814531187192716849)
                ·
                  refine ⟨5812895860898390394537637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750527814531187192716849 5812895860898390394537637)
                  ·
                    refine ⟨1089917973918448198975807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812895860898390394537637 1089917973918448198975807)
                    ·
                      rfl

theorem cell23_6367823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_6367823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367823 prefixEnd_6367823 := by exact prefixLift 6367823
  have htrace : WordTrace (prefixWord ++ tailWord_6367823) baseStart_6367823 baseEnd_6367823 := by
    simpa [prefixWord, tailWord_6367823, baseEnd_6367823] using wordTrace_append hprefix tailTrace_6367823
  have hstable : (prefixWord ++ tailWord_6367823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367823).length < 2 ^ (prefixWord ++ tailWord_6367823).sum := by decide
  have hdescent : baseEnd_6367823 < baseStart_6367823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367843 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4]
def baseStart_6367843 : Nat := 118140960795 + 6367843 * 2 ^ 59
def prefixEnd_6367843 : Nat := 4983230072969 + 3 ^ 40 * 6367843 * 2
def baseEnd_6367843 : Nat := 3269764191368434518677329

theorem tailTrace_6367843 : CollatzResearch.WordTrace tailWord_6367843 prefixEnd_6367843 3269764191368434518677329 := by
  unfold tailWord_6367843
  simp only [CollatzResearch.WordTrace]
  refine ⟨232254314669399826845948183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154836209779599884563965455 232254314669399826845948183)
  ·
    refine ⟨348381472004099740268922275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232254314669399826845948183 348381472004099740268922275)
    ·
      refine ⟨522572208006149610403383413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348381472004099740268922275 522572208006149610403383413)
      ·
        refine ⟨48991144500576525975317195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 522572208006149610403383413 48991144500576525975317195)
        ·
          refine ⟨73486716750864788962975793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48991144500576525975317195 73486716750864788962975793)
          ·
            refine ⟨55115037563148591722231845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73486716750864788962975793 55115037563148591722231845)
            ·
              refine ⟨10334069543090360947918471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55115037563148591722231845 10334069543090360947918471)
              ·
                refine ⟨15501104314635541421877707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334069543090360947918471 15501104314635541421877707)
                ·
                  refine ⟨23251656471953312132816561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15501104314635541421877707 23251656471953312132816561)
                  ·
                    refine ⟨17438742353964984099612421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23251656471953312132816561 17438742353964984099612421)
                    ·
                      refine ⟨3269764191368434518677329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17438742353964984099612421 3269764191368434518677329)
                      ·
                        rfl

theorem cell23_6367843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_6367843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367843 prefixEnd_6367843 := by exact prefixLift 6367843
  have htrace : WordTrace (prefixWord ++ tailWord_6367843) baseStart_6367843 baseEnd_6367843 := by
    simpa [prefixWord, tailWord_6367843, baseEnd_6367843] using wordTrace_append hprefix tailTrace_6367843
  have hstable : (prefixWord ++ tailWord_6367843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367843).length < 2 ^ (prefixWord ++ tailWord_6367843).sum := by decide
  have hdescent : baseEnd_6367843 < baseStart_6367843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367850 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6367850 : Nat := 118140960795 + 6367850 * 2 ^ 59
def prefixEnd_6367850 : Nat := 4983230072969 + 3 ^ 40 * 6367850 * 2
def baseEnd_6367850 : Nat := 3269767785733015991289797

theorem tailTrace_6367850 : CollatzResearch.WordTrace tailWord_6367850 prefixEnd_6367850 3269767785733015991289797 := by
  unfold tailWord_6367850
  simp only [CollatzResearch.WordTrace]
  refine ⟨58063642495093616760363251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154836379986916311360968669 58063642495093616760363251)
  ·
    refine ⟨87095463742640425140544877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58063642495093616760363251 87095463742640425140544877)
    ·
      refine ⟨32660798903490159427704329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87095463742640425140544877 32660798903490159427704329)
      ·
        refine ⟨24495599177617619570778247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32660798903490159427704329 24495599177617619570778247)
        ·
          refine ⟨36743398766426429356167371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24495599177617619570778247 36743398766426429356167371)
          ·
            refine ⟨55115098149639644034251057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36743398766426429356167371 55115098149639644034251057)
            ·
              refine ⟨41336323612229733025688293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55115098149639644034251057 41336323612229733025688293)
              ·
                refine ⟨7750560677293074942316555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41336323612229733025688293 7750560677293074942316555)
                ·
                  refine ⟨11625841015939612413474833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7750560677293074942316555 11625841015939612413474833)
                  ·
                    refine ⟨8719380761954709310106125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11625841015939612413474833 8719380761954709310106125)
                    ·
                      refine ⟨3269767785733015991289797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719380761954709310106125 3269767785733015991289797)
                      ·
                        rfl

theorem cell23_6367850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6367850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367850 prefixEnd_6367850 := by exact prefixLift 6367850
  have htrace : WordTrace (prefixWord ++ tailWord_6367850) baseStart_6367850 baseEnd_6367850 := by
    simpa [prefixWord, tailWord_6367850, baseEnd_6367850] using wordTrace_append hprefix tailTrace_6367850
  have hstable : (prefixWord ++ tailWord_6367850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367850).length < 2 ^ (prefixWord ++ tailWord_6367850).sum := by decide
  have hdescent : baseEnd_6367850 < baseStart_6367850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367863 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_6367863 : Nat := 118140960795 + 6367863 * 2 ^ 59
def prefixEnd_6367863 : Nat := 4983230072969 + 3 ^ 40 * 6367863 * 2
def baseEnd_6367863 : Nat := 3269774460981524440427237

theorem tailTrace_6367863 : CollatzResearch.WordTrace tailWord_6367863 prefixEnd_6367863 3269774460981524440427237 := by
  unfold tailWord_6367863
  simp only [CollatzResearch.WordTrace]
  refine ⟨232255044129327370261676243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154836696086218246841117495 232255044129327370261676243)
  ·
    refine ⟨348382566193991055392514365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232255044129327370261676243 348382566193991055392514365)
    ·
      refine ⟨130643462322746645772192887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348382566193991055392514365 130643462322746645772192887)
      ·
        refine ⟨195965193484119968658289331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130643462322746645772192887 195965193484119968658289331)
        ·
          refine ⟨293947790226179952987433997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195965193484119968658289331 293947790226179952987433997)
          ·
            refine ⟨110230421334817482370287749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293947790226179952987433997 110230421334817482370287749)
            ·
              refine ⟨20668204000278277944428953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110230421334817482370287749 20668204000278277944428953)
              ·
                refine ⟨15501153000208708458321715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20668204000278277944428953 15501153000208708458321715)
                ·
                  refine ⟨23251729500313062687482573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15501153000208708458321715 23251729500313062687482573)
                  ·
                    refine ⟨8719398562617398507805965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23251729500313062687482573 8719398562617398507805965)
                    ·
                      refine ⟨3269774460981524440427237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719398562617398507805965 3269774460981524440427237)
                      ·
                        rfl

theorem cell23_6367863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_6367863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367863 prefixEnd_6367863 := by exact prefixLift 6367863
  have htrace : WordTrace (prefixWord ++ tailWord_6367863) baseStart_6367863 baseEnd_6367863 := by
    simpa [prefixWord, tailWord_6367863, baseEnd_6367863] using wordTrace_append hprefix tailTrace_6367863
  have hstable : (prefixWord ++ tailWord_6367863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367863).length < 2 ^ (prefixWord ++ tailWord_6367863).sum := by decide
  have hdescent : baseEnd_6367863 < baseStart_6367863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367897 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 2, 1, 3]
def baseStart_6367897 : Nat := 118140960795 + 6367897 * 2 ^ 59
def prefixEnd_6367897 : Nat := 4983230072969 + 3 ^ 40 * 6367897 * 2
def baseEnd_6367897 : Nat := 3269791919323777307402081

theorem tailTrace_6367897 : CollatzResearch.WordTrace tailWord_6367897 prefixEnd_6367897 3269791919323777307402081 := by
  unfold tailWord_6367897
  simp only [CollatzResearch.WordTrace]
  refine ⟨232256284211204194068413945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154837522807469462712275963 232256284211204194068413945)
  ·
    refine ⟨174192213158403145551310459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232256284211204194068413945 174192213158403145551310459)
    ·
      refine ⟨261288319737604718326965689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174192213158403145551310459 261288319737604718326965689)
      ·
        refine ⟨195966239803203538745224267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261288319737604718326965689 195966239803203538745224267)
        ·
          refine ⟨293949359704805308117836401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195966239803203538745224267 293949359704805308117836401)
          ·
            refine ⟨220462019778603981088377301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293949359704805308117836401 220462019778603981088377301)
            ·
              refine ⟨5167078588561030806758843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220462019778603981088377301 5167078588561030806758843)
              ·
                refine ⟨7750617882841546210138265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167078588561030806758843 7750617882841546210138265)
                ·
                  refine ⟨5812963412131159657603699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750617882841546210138265 5812963412131159657603699)
                  ·
                    refine ⟨8719445118196739486405549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5812963412131159657603699 8719445118196739486405549)
                    ·
                      refine ⟨3269791919323777307402081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719445118196739486405549 3269791919323777307402081)
                      ·
                        rfl

theorem cell23_6367897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_6367897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367897 prefixEnd_6367897 := by exact prefixLift 6367897
  have htrace : WordTrace (prefixWord ++ tailWord_6367897) baseStart_6367897 baseEnd_6367897 := by
    simpa [prefixWord, tailWord_6367897, baseEnd_6367897] using wordTrace_append hprefix tailTrace_6367897
  have hstable : (prefixWord ++ tailWord_6367897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367897).length < 2 ^ (prefixWord ++ tailWord_6367897).sum := by decide
  have hdescent : baseEnd_6367897 < baseStart_6367897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367923 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_6367923 : Nat := 118140960795 + 6367923 * 2 ^ 59
def prefixEnd_6367923 : Nat := 4983230072969 + 3 ^ 40 * 6367923 * 2
def baseEnd_6367923 : Nat := 3269805269820794205676961

theorem tailTrace_6367923 : CollatzResearch.WordTrace tailWord_6367923 prefixEnd_6367923 3269805269820794205676961 := by
  unfold tailWord_6367923
  simp only [CollatzResearch.WordTrace]
  refine ⟨232257232509110000508860423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154838155006073333672573615 232257232509110000508860423)
  ·
    refine ⟨348385848763665000763290635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232257232509110000508860423 348385848763665000763290635)
    ·
      refine ⟨522578773145497501144935953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348385848763665000763290635 522578773145497501144935953)
      ·
        refine ⟨391934079859123125858701965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522578773145497501144935953 391934079859123125858701965)
        ·
          refine ⟨146975279947171172197013237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391934079859123125858701965 146975279947171172197013237)
          ·
            refine ⟨13778932495047297393469991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146975279947171172197013237 13778932495047297393469991)
            ·
              refine ⟨20668398742570946090204987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13778932495047297393469991 20668398742570946090204987)
              ·
                refine ⟨31002598113856419135307481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20668398742570946090204987 31002598113856419135307481)
                ·
                  refine ⟨23251948585392314351480611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31002598113856419135307481 23251948585392314351480611)
                  ·
                    refine ⟨34877922878088471527220917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23251948585392314351480611 34877922878088471527220917)
                    ·
                      refine ⟨3269805269820794205676961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34877922878088471527220917 3269805269820794205676961)
                      ·
                        rfl

theorem cell23_6367923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_6367923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367923 prefixEnd_6367923 := by exact prefixLift 6367923
  have htrace : WordTrace (prefixWord ++ tailWord_6367923) baseStart_6367923 baseEnd_6367923 := by
    simpa [prefixWord, tailWord_6367923, baseEnd_6367923] using wordTrace_append hprefix tailTrace_6367923
  have hstable : (prefixWord ++ tailWord_6367923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367923).length < 2 ^ (prefixWord ++ tailWord_6367923).sum := by decide
  have hdescent : baseEnd_6367923 < baseStart_6367923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367953 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_6367953 : Nat := 118140960795 + 6367953 * 2 ^ 59
def prefixEnd_6367953 : Nat := 4983230072969 + 3 ^ 40 * 6367953 * 2
def baseEnd_6367953 : Nat := 3269820674240429088301823

theorem tailTrace_6367953 : CollatzResearch.WordTrace tailWord_6367953 prefixEnd_6367953 3269820674240429088301823 := by
  unfold tailWord_6367953
  simp only [CollatzResearch.WordTrace]
  refine ⟨232258326699001315632452513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154838884466000877088301675 232258326699001315632452513)
  ·
    refine ⟨174193745024250986724339385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232258326699001315632452513 174193745024250986724339385)
    ·
      refine ⟨130645308768188240043254539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174193745024250986724339385 130645308768188240043254539)
      ·
        refine ⟨195967963152282360064881809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130645308768188240043254539 195967963152282360064881809)
        ·
          refine ⟨146975972364211770048661357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195967963152282360064881809 146975972364211770048661357)
          ·
            refine ⟨55115989636579413768248009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146975972364211770048661357 55115989636579413768248009)
            ·
              refine ⟨41336992227434560326186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55115989636579413768248009 41336992227434560326186007)
              ·
                refine ⟨62005488341151840489279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41336992227434560326186007 62005488341151840489279011)
                ·
                  refine ⟨93008232511727760733918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62005488341151840489279011 93008232511727760733918517)
                  ·
                    refine ⟨8719521797974477568804861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93008232511727760733918517 8719521797974477568804861)
                    ·
                      refine ⟨3269820674240429088301823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719521797974477568804861 3269820674240429088301823)
                      ·
                        rfl

theorem cell23_6367953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_6367953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367953 prefixEnd_6367953 := by exact prefixLift 6367953
  have htrace : WordTrace (prefixWord ++ tailWord_6367953) baseStart_6367953 baseEnd_6367953 := by
    simpa [prefixWord, tailWord_6367953, baseEnd_6367953] using wordTrace_append hprefix tailTrace_6367953
  have hstable : (prefixWord ++ tailWord_6367953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367953).length < 2 ^ (prefixWord ++ tailWord_6367953).sum := by decide
  have hdescent : baseEnd_6367953 < baseStart_6367953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367983 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_6367983 : Nat := 118140960795 + 6367983 * 2 ^ 59
def prefixEnd_6367983 : Nat := 4983230072969 + 3 ^ 40 * 6367983 * 2
def baseEnd_6367983 : Nat := 3269836078660063970926685

theorem tailTrace_6367983 : CollatzResearch.WordTrace tailWord_6367983 prefixEnd_6367983 3269836078660063970926685 := by
  unfold tailWord_6367983
  simp only [CollatzResearch.WordTrace]
  refine ⟨232259420888892630756044603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154839613925928420504029735 232259420888892630756044603)
  ·
    refine ⟨348389131333338946134066905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232259420888892630756044603 348389131333338946134066905)
    ·
      refine ⟨261291848500004209600550179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348389131333338946134066905 261291848500004209600550179)
      ·
        refine ⟨391937772750006314400825269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261291848500004209600550179 391937772750006314400825269)
        ·
          refine ⟨36744166195313091975077369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391937772750006314400825269 36744166195313091975077369)
          ·
            refine ⟨27558124646484818981308027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36744166195313091975077369 27558124646484818981308027)
            ·
              refine ⟨41337186969727228471962041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27558124646484818981308027 41337186969727228471962041)
              ·
                refine ⟨31002890227295421353971531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41337186969727228471962041 31002890227295421353971531)
                ·
                  refine ⟨46504335340943132030957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31002890227295421353971531 46504335340943132030957297)
                  ·
                    refine ⟨34878251505707349023217973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46504335340943132030957297 34878251505707349023217973)
                    ·
                      refine ⟨3269836078660063970926685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34878251505707349023217973 3269836078660063970926685)
                      ·
                        rfl

theorem cell23_6367983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_6367983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367983 prefixEnd_6367983 := by exact prefixLift 6367983
  have htrace : WordTrace (prefixWord ++ tailWord_6367983) baseStart_6367983 baseEnd_6367983 := by
    simpa [prefixWord, tailWord_6367983, baseEnd_6367983] using wordTrace_append hprefix tailTrace_6367983
  have hstable : (prefixWord ++ tailWord_6367983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367983).length < 2 ^ (prefixWord ++ tailWord_6367983).sum := by decide
  have hdescent : baseEnd_6367983 < baseStart_6367983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6367990 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6367990 : Nat := 118140960795 + 6367990 * 2 ^ 59
def prefixEnd_6367990 : Nat := 4983230072969 + 3 ^ 40 * 6367990 * 2
def baseEnd_6367990 : Nat := 1089946557674881814513051

theorem tailTrace_6367990 : CollatzResearch.WordTrace tailWord_6367990 prefixEnd_6367990 1089946557674881814513051 := by
  unfold tailWord_6367990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516229762491704434471839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154839784133244847301032949 14516229762491704434471839)
  ·
    refine ⟨21774344643737556651707759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14516229762491704434471839 21774344643737556651707759)
    ·
      refine ⟨32661516965606334977561639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21774344643737556651707759 32661516965606334977561639)
      ·
        refine ⟨48992275448409502466342459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32661516965606334977561639 48992275448409502466342459)
        ·
          refine ⟨73488413172614253699513689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48992275448409502466342459 73488413172614253699513689)
          ·
            refine ⟨55116309879460690274635267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73488413172614253699513689 55116309879460690274635267)
            ·
              refine ⟨82674464819191035411952901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55116309879460690274635267 82674464819191035411952901)
              ·
                refine ⟨15501462153598319139741169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82674464819191035411952901 15501462153598319139741169)
                ·
                  refine ⟨11626096615198739354805877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15501462153598319139741169 11626096615198739354805877)
                  ·
                    refine ⟨1089946557674881814513051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11626096615198739354805877 1089946557674881814513051)
                    ·
                      rfl

theorem cell23_6367990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6367990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6367990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6367990 prefixEnd_6367990 := by exact prefixLift 6367990
  have htrace : WordTrace (prefixWord ++ tailWord_6367990) baseStart_6367990 baseEnd_6367990 := by
    simpa [prefixWord, tailWord_6367990, baseEnd_6367990] using wordTrace_append hprefix tailTrace_6367990
  have hstable : (prefixWord ++ tailWord_6367990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6367990).length < 2 ^ (prefixWord ++ tailWord_6367990).sum := by decide
  have hdescent : baseEnd_6367990 < baseStart_6367990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6367990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368033 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 8]
def baseStart_6368033 : Nat := 118140960795 + 6368033 * 2 ^ 59
def prefixEnd_6368033 : Nat := 4983230072969 + 3 ^ 40 * 6368033 * 2
def baseEnd_6368033 : Nat := 363317972521420975033495

theorem tailTrace_6368033 : CollatzResearch.WordTrace tailWord_6368033 prefixEnd_6368033 363317972521420975033495 := by
  unfold tailWord_6368033
  simp only [CollatzResearch.WordTrace]
  refine ⟨232261244538711489295364753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154840829692474326196909835 232261244538711489295364753)
  ·
    refine ⟨174195933404033616971523565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232261244538711489295364753 174195933404033616971523565)
    ·
      refine ⟨65323475026512606364321337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174195933404033616971523565 65323475026512606364321337)
      ·
        refine ⟨48992606269884454773241003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65323475026512606364321337 48992606269884454773241003)
        ·
          refine ⟨73488909404826682159861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48992606269884454773241003 73488909404826682159861505)
          ·
            refine ⟨55116682053620011619896129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73488909404826682159861505 55116682053620011619896129)
            ·
              refine ⟨41337511540215008714922097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55116682053620011619896129 41337511540215008714922097)
              ·
                refine ⟨31003133655161256536191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41337511540215008714922097 31003133655161256536191573)
                ·
                  refine ⟨363317972521420975033495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31003133655161256536191573 363317972521420975033495)
                  ·
                    rfl

theorem cell23_6368033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_6368033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368033 prefixEnd_6368033 := by exact prefixLift 6368033
  have htrace : WordTrace (prefixWord ++ tailWord_6368033) baseStart_6368033 baseEnd_6368033 := by
    simpa [prefixWord, tailWord_6368033, baseEnd_6368033] using wordTrace_append hprefix tailTrace_6368033
  have hstable : (prefixWord ++ tailWord_6368033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368033).length < 2 ^ (prefixWord ++ tailWord_6368033).sum := by decide
  have hdescent : baseEnd_6368033 < baseStart_6368033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368080 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_6368080 : Nat := 118140960795 + 6368080 * 2 ^ 59
def prefixEnd_6368080 : Nat := 4983230072969 + 3 ^ 40 * 6368080 * 2
def baseEnd_6368080 : Nat := 1089961962094516697137913

theorem tailTrace_6368080 : CollatzResearch.WordTrace tailWord_6368080 prefixEnd_6368080 1089961962094516697137913 := by
  unfold tailWord_6368080
  simp only [CollatzResearch.WordTrace]
  refine ⟨116131479384770608161162847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154841972513027477548217129 116131479384770608161162847)
  ·
    refine ⟨174197219077155912241744271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116131479384770608161162847 174197219077155912241744271)
    ·
      refine ⟨261295828615733868362616407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174197219077155912241744271 261295828615733868362616407)
      ·
        refine ⟨391943742923600802543924611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261295828615733868362616407 391943742923600802543924611)
        ·
          refine ⟨587915614385401203815886917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391943742923600802543924611 587915614385401203815886917)
          ·
            refine ⟨110234177697262725715478797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 587915614385401203815886917 110234177697262725715478797)
            ·
              refine ⟨41337816636473522143304549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110234177697262725715478797 41337816636473522143304549)
              ·
                refine ⟨7750840619338785401869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41337816636473522143304549 7750840619338785401869603)
                ·
                  refine ⟨11626260929008178102804405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7750840619338785401869603 11626260929008178102804405)
                  ·
                    refine ⟨1089961962094516697137913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11626260929008178102804405 1089961962094516697137913)
                    ·
                      rfl

theorem cell23_6368080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_6368080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368080 prefixEnd_6368080 := by exact prefixLift 6368080
  have htrace : WordTrace (prefixWord ++ tailWord_6368080) baseStart_6368080 baseEnd_6368080 := by
    simpa [prefixWord, tailWord_6368080, baseEnd_6368080] using wordTrace_append hprefix tailTrace_6368080
  have hstable : (prefixWord ++ tailWord_6368080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368080).length < 2 ^ (prefixWord ++ tailWord_6368080).sum := by decide
  have hdescent : baseEnd_6368080 < baseStart_6368080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368083 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_6368083 : Nat := 118140960795 + 6368083 * 2 ^ 59
def prefixEnd_6368083 : Nat := 4983230072969 + 3 ^ 40 * 6368083 * 2
def baseEnd_6368083 : Nat := 3269887426725513579676225

theorem tailTrace_6368083 : CollatzResearch.WordTrace tailWord_6368083 prefixEnd_6368083 3269887426725513579676225 := by
  unfold tailWord_6368083
  simp only [CollatzResearch.WordTrace]
  refine ⟨232263068188530347834684903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154842045459020231889789935 232263068188530347834684903)
  ·
    refine ⟨348394602282795521752027355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232263068188530347834684903 348394602282795521752027355)
    ·
      refine ⟨522591903424193282628041033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348394602282795521752027355 522591903424193282628041033)
      ·
        refine ⟨391943927568144961971030775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522591903424193282628041033 391943927568144961971030775)
        ·
          refine ⟨587915891352217442956546163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391943927568144961971030775 587915891352217442956546163)
          ·
            refine ⟨881873837028326164434819245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587915891352217442956546163 881873837028326164434819245)
            ·
              refine ⟨330702688885622311663057217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881873837028326164434819245 330702688885622311663057217)
              ·
                refine ⟨248027016664216733747292913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330702688885622311663057217 248027016664216733747292913)
                ·
                  refine ⟨186020262498162550310469685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248027016664216733747292913 186020262498162550310469685)
                  ·
                    refine ⟨17439399609202739091606533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186020262498162550310469685 17439399609202739091606533)
                    ·
                      refine ⟨3269887426725513579676225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17439399609202739091606533 3269887426725513579676225)
                      ·
                        rfl

theorem cell23_6368083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_6368083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368083 prefixEnd_6368083 := by exact prefixLift 6368083
  have htrace : WordTrace (prefixWord ++ tailWord_6368083) baseStart_6368083 baseEnd_6368083 := by
    simpa [prefixWord, tailWord_6368083, baseEnd_6368083] using wordTrace_append hprefix tailTrace_6368083
  have hstable : (prefixWord ++ tailWord_6368083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368083).length < 2 ^ (prefixWord ++ tailWord_6368083).sum := by decide
  have hdescent : baseEnd_6368083 < baseStart_6368083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368087 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_6368087 : Nat := 118140960795 + 6368087 * 2 ^ 59
def prefixEnd_6368087 : Nat := 4983230072969 + 3 ^ 40 * 6368087 * 2
def baseEnd_6368087 : Nat := 3269889480648131564026207

theorem tailTrace_6368087 : CollatzResearch.WordTrace tailWord_6368087 prefixEnd_6368087 3269889480648131564026207 := by
  unfold tailWord_6368087
  simp only [CollatzResearch.WordTrace]
  refine ⟨232263214080515856517830515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154842142720343904345220343 232263214080515856517830515)
  ·
    refine ⟨348394821120773784776745773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232263214080515856517830515 348394821120773784776745773)
    ·
      refine ⟨130648057920290169291279665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348394821120773784776745773 130648057920290169291279665)
      ·
        refine ⟨97986043440217626968459749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130648057920290169291279665 97986043440217626968459749)
        ·
          refine ⟨18372383145040805056586203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97986043440217626968459749 18372383145040805056586203)
          ·
            refine ⟨27558574717561207584879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18372383145040805056586203 27558574717561207584879305)
            ·
              refine ⟨20668931038170905688659479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27558574717561207584879305 20668931038170905688659479)
              ·
                refine ⟨31003396557256358532989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20668931038170905688659479 31003396557256358532989219)
                ·
                  refine ⟨46505094835884537799483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31003396557256358532989219 46505094835884537799483829)
                  ·
                    refine ⟨4359852640864175418701609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46505094835884537799483829 4359852640864175418701609)
                    ·
                      refine ⟨3269889480648131564026207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359852640864175418701609 3269889480648131564026207)
                      ·
                        rfl

theorem cell23_6368087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_6368087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368087 prefixEnd_6368087 := by exact prefixLift 6368087
  have htrace : WordTrace (prefixWord ++ tailWord_6368087) baseStart_6368087 baseEnd_6368087 := by
    simpa [prefixWord, tailWord_6368087, baseEnd_6368087] using wordTrace_append hprefix tailTrace_6368087
  have hstable : (prefixWord ++ tailWord_6368087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368087).length < 2 ^ (prefixWord ++ tailWord_6368087).sum := by decide
  have hdescent : baseEnd_6368087 < baseStart_6368087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368104 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6368104 : Nat := 118140960795 + 6368104 * 2 ^ 59
def prefixEnd_6368104 : Nat := 4983230072969 + 3 ^ 40 * 6368104 * 2
def baseEnd_6368104 : Nat := 3269898209819257997513629

theorem tailTrace_6368104 : CollatzResearch.WordTrace tailWord_6368104 prefixEnd_6368104 3269898209819257997513629 := by
  unfold tailWord_6368104
  simp only [CollatzResearch.WordTrace]
  refine ⟨116131917060727134210599683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154842556080969512280799577 116131917060727134210599683)
  ·
    refine ⟨174197875591090701315899525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116131917060727134210599683 174197875591090701315899525)
    ·
      refine ⟨32662101673329506496731161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174197875591090701315899525 32662101673329506496731161)
      ·
        refine ⟨24496576254997129872548371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32662101673329506496731161 24496576254997129872548371)
        ·
          refine ⟨36744864382495694808822557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24496576254997129872548371 36744864382495694808822557)
          ·
            refine ⟨13779324143435885553308459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36744864382495694808822557 13779324143435885553308459)
            ·
              refine ⟨20668986215153828329962689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779324143435885553308459 20668986215153828329962689)
              ·
                refine ⟨15501739661365371247472017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20668986215153828329962689 15501739661365371247472017)
                ·
                  refine ⟨11626304746024028435604013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15501739661365371247472017 11626304746024028435604013)
                  ·
                    refine ⟨4359864279759010663351505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11626304746024028435604013 4359864279759010663351505)
                    ·
                      refine ⟨3269898209819257997513629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359864279759010663351505 3269898209819257997513629)
                      ·
                        rfl

theorem cell23_6368104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6368104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368104 prefixEnd_6368104 := by exact prefixLift 6368104
  have htrace : WordTrace (prefixWord ++ tailWord_6368104) baseStart_6368104 baseEnd_6368104 := by
    simpa [prefixWord, tailWord_6368104, baseEnd_6368104] using wordTrace_append hprefix tailTrace_6368104
  have hstable : (prefixWord ++ tailWord_6368104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368104).length < 2 ^ (prefixWord ++ tailWord_6368104).sum := by decide
  have hdescent : baseEnd_6368104 < baseStart_6368104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368123 : List Nat := [1, 1, 1, 1, 1, 5, 3, 10]
def baseStart_6368123 : Nat := 118140960795 + 6368123 * 2 ^ 59
def prefixEnd_6368123 : Nat := 4983230072969 + 3 ^ 40 * 6368123 * 2
def baseEnd_6368123 : Nat := 121107702442655311969483

theorem tailTrace_6368123 : CollatzResearch.WordTrace tailWord_6368123 prefixEnd_6368123 121107702442655311969483 := by
  unfold tailWord_6368123
  simp only [CollatzResearch.WordTrace]
  refine ⟨232264527108385434666141023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154843018072256956444094015 232264527108385434666141023)
  ·
    refine ⟨348396790662578151999211535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232264527108385434666141023 348396790662578151999211535)
    ·
      refine ⟨522595185993867227998817303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348396790662578151999211535 522595185993867227998817303)
      ·
        refine ⟨783892778990800841998225955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522595185993867227998817303 783892778990800841998225955)
        ·
          refine ⟨1175839168486201262997338933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783892778990800841998225955 1175839168486201262997338933)
          ·
            refine ⟨110234922045581368406000525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1175839168486201262997338933 110234922045581368406000525)
            ·
              refine ⟨41338095767093013152250197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110234922045581368406000525 41338095767093013152250197)
              ·
                refine ⟨121107702442655311969483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41338095767093013152250197 121107702442655311969483)
                ·
                  rfl

theorem cell23_6368123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 10].length) (baseStart_6368123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368123 prefixEnd_6368123 := by exact prefixLift 6368123
  have htrace : WordTrace (prefixWord ++ tailWord_6368123) baseStart_6368123 baseEnd_6368123 := by
    simpa [prefixWord, tailWord_6368123, baseEnd_6368123] using wordTrace_append hprefix tailTrace_6368123
  have hstable : (prefixWord ++ tailWord_6368123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368123).length < 2 ^ (prefixWord ++ tailWord_6368123).sum := by decide
  have hdescent : baseEnd_6368123 < baseStart_6368123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368137 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_6368137 : Nat := 118140960795 + 6368137 * 2 ^ 59
def prefixEnd_6368137 : Nat := 4983230072969 + 3 ^ 40 * 6368137 * 2
def baseEnd_6368137 : Nat := 3269915154680856368400977

theorem tailTrace_6368137 : CollatzResearch.WordTrace tailWord_6368137 prefixEnd_6368137 3269915154680856368400977 := by
  unfold tailWord_6368137
  simp only [CollatzResearch.WordTrace]
  refine ⟨232265037730334715057150665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154843358486889810038100443 232265037730334715057150665)
  ·
    refine ⟨174198778297751036292862999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232265037730334715057150665 174198778297751036292862999)
    ·
      refine ⟨261298167446626554439294499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174198778297751036292862999 261298167446626554439294499)
      ·
        refine ⟨391947251169939831658941749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261298167446626554439294499 391947251169939831658941749)
        ·
          refine ⟨36745054797181859218025789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391947251169939831658941749 36745054797181859218025789)
          ·
            refine ⟨13779395548943197206759671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36745054797181859218025789 13779395548943197206759671)
            ·
              refine ⟨20669093323414795810139507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779395548943197206759671 20669093323414795810139507)
              ·
                refine ⟨31003639985122193715209261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20669093323414795810139507 31003639985122193715209261)
                ·
                  refine ⟨11626364994420822643203473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31003639985122193715209261 11626364994420822643203473)
                  ·
                    refine ⟨8719773745815616982402605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11626364994420822643203473 8719773745815616982402605)
                    ·
                      refine ⟨3269915154680856368400977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719773745815616982402605 3269915154680856368400977)
                      ·
                        rfl

theorem cell23_6368137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_6368137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368137 prefixEnd_6368137 := by exact prefixLift 6368137
  have htrace : WordTrace (prefixWord ++ tailWord_6368137) baseStart_6368137 baseEnd_6368137 := by
    simpa [prefixWord, tailWord_6368137, baseEnd_6368137] using wordTrace_append hprefix tailTrace_6368137
  have hstable : (prefixWord ++ tailWord_6368137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368137).length < 2 ^ (prefixWord ++ tailWord_6368137).sum := by decide
  have hdescent : baseEnd_6368137 < baseStart_6368137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368151 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_6368151 : Nat := 118140960795 + 6368151 * 2 ^ 59
def prefixEnd_6368151 : Nat := 4983230072969 + 3 ^ 40 * 6368151 * 2
def baseEnd_6368151 : Nat := 3269922343410019313625913

theorem tailTrace_6368151 : CollatzResearch.WordTrace tailWord_6368151 prefixEnd_6368151 3269922343410019313625913 := by
  unfold tailWord_6368151
  simp only [CollatzResearch.WordTrace]
  refine ⟨232265548352283995448160307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154843698901522663632106871 232265548352283995448160307)
  ·
    refine ⟨348398322528425993172240461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232265548352283995448160307 348398322528425993172240461)
    ·
      refine ⟨130649370948159747439590173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348398322528425993172240461 130649370948159747439590173)
      ·
        refine ⟨48993514105559905289846315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130649370948159747439590173 48993514105559905289846315)
        ·
          refine ⟨73490271158339857934769473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48993514105559905289846315 73490271158339857934769473)
          ·
            refine ⟨55117703368754893451077105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73490271158339857934769473 55117703368754893451077105)
            ·
              refine ⟨41338277526566170088307829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55117703368754893451077105 41338277526566170088307829)
              ·
                refine ⟨3875463518115578445778859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41338277526566170088307829 3875463518115578445778859)
                ·
                  refine ⟨5813195277173367668668289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875463518115578445778859 5813195277173367668668289)
                  ·
                    refine ⟨4359896457880025751501217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5813195277173367668668289 4359896457880025751501217)
                    ·
                      refine ⟨3269922343410019313625913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359896457880025751501217 3269922343410019313625913)
                      ·
                        rfl

theorem cell23_6368151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_6368151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368151 prefixEnd_6368151 := by exact prefixLift 6368151
  have htrace : WordTrace (prefixWord ++ tailWord_6368151) baseStart_6368151 baseEnd_6368151 := by
    simpa [prefixWord, tailWord_6368151, baseEnd_6368151] using wordTrace_append hprefix tailTrace_6368151
  have hstable : (prefixWord ++ tailWord_6368151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368151).length < 2 ^ (prefixWord ++ tailWord_6368151).sum := by decide
  have hdescent : baseEnd_6368151 < baseStart_6368151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368154 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6368154 : Nat := 118140960795 + 6368154 * 2 ^ 59
def prefixEnd_6368154 : Nat := 4983230072969 + 3 ^ 40 * 6368154 * 2
def baseEnd_6368154 : Nat := 3269923883851982801888399

theorem tailTrace_6368154 : CollatzResearch.WordTrace tailWord_6368154 prefixEnd_6368154 3269923883851982801888399 := by
  unfold tailWord_6368154
  simp only [CollatzResearch.WordTrace]
  refine ⟨58066414442818281740129879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154843771847515417973679677 58066414442818281740129879)
  ·
    refine ⟨87099621664227422610194819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58066414442818281740129879 87099621664227422610194819)
    ·
      refine ⟨130649432496341133915292229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87099621664227422610194819 130649432496341133915292229)
      ·
        refine ⟨24496768593063962609117293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130649432496341133915292229 24496768593063962609117293)
        ·
          refine ⟨9186288222398985978418985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24496768593063962609117293 9186288222398985978418985)
          ·
            refine ⟨6889716166799239483814239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9186288222398985978418985 6889716166799239483814239)
            ·
              refine ⟨10334574250198859225721359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889716166799239483814239 10334574250198859225721359)
              ·
                refine ⟨15501861375298288838582039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334574250198859225721359 15501861375298288838582039)
                ·
                  refine ⟨23252792062947433257873059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15501861375298288838582039 23252792062947433257873059)
                  ·
                    refine ⟨34879188094421149886809589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23252792062947433257873059 34879188094421149886809589)
                    ·
                      refine ⟨3269923883851982801888399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34879188094421149886809589 3269923883851982801888399)
                      ·
                        rfl

theorem cell23_6368154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6368154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368154 prefixEnd_6368154 := by exact prefixLift 6368154
  have htrace : WordTrace (prefixWord ++ tailWord_6368154) baseStart_6368154 baseEnd_6368154 := by
    simpa [prefixWord, tailWord_6368154, baseEnd_6368154] using wordTrace_append hprefix tailTrace_6368154
  have hstable : (prefixWord ++ tailWord_6368154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368154).length < 2 ^ (prefixWord ++ tailWord_6368154).sum := by decide
  have hdescent : baseEnd_6368154 < baseStart_6368154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368184 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_6368184 : Nat := 118140960795 + 6368184 * 2 ^ 59
def prefixEnd_6368184 : Nat := 4983230072969 + 3 ^ 40 * 6368184 * 2
def baseEnd_6368184 : Nat := 3269939288271617684513261

theorem tailTrace_6368184 : CollatzResearch.WordTrace tailWord_6368184 prefixEnd_6368184 3269939288271617684513261 := by
  unfold tailWord_6368184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116133375980582221042055803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154844501307442961389407737 116133375980582221042055803)
  ·
    refine ⟨174200063970873331563083705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116133375980582221042055803 174200063970873331563083705)
    ·
      refine ⟨130650047978154998672312779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174200063970873331563083705 130650047978154998672312779)
      ·
        refine ⟨195975071967232498008469169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130650047978154998672312779 195975071967232498008469169)
        ·
          refine ⟨146981303975424373506351877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195975071967232498008469169 146981303975424373506351877)
          ·
            refine ⟨27558994495392070032440977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146981303975424373506351877 27558994495392070032440977)
            ·
              refine ⟨20669245871544052524330733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27558994495392070032440977 20669245871544052524330733)
              ·
                refine ⟨7750967201829019696624025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20669245871544052524330733 7750967201829019696624025)
                ·
                  refine ⟨5813225401371764772468019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750967201829019696624025 5813225401371764772468019)
                  ·
                    refine ⟨8719838102057647158702029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5813225401371764772468019 8719838102057647158702029)
                    ·
                      refine ⟨3269939288271617684513261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719838102057647158702029 3269939288271617684513261)
                      ·
                        rfl

theorem cell23_6368184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_6368184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368184 prefixEnd_6368184 := by exact prefixLift 6368184
  have htrace : WordTrace (prefixWord ++ tailWord_6368184) baseStart_6368184 baseEnd_6368184 := by
    simpa [prefixWord, tailWord_6368184, baseEnd_6368184] using wordTrace_append hprefix tailTrace_6368184
  have hstable : (prefixWord ++ tailWord_6368184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368184).length < 2 ^ (prefixWord ++ tailWord_6368184).sum := by decide
  have hdescent : baseEnd_6368184 < baseStart_6368184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368205 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6368205 : Nat := 118140960795 + 6368205 * 2 ^ 59
def prefixEnd_6368205 : Nat := 4983230072969 + 3 ^ 40 * 6368205 * 2
def baseEnd_6368205 : Nat := 3269950071365362102350665

theorem tailTrace_6368205 : CollatzResearch.WordTrace tailWord_6368205 prefixEnd_6368205 3269950071365362102350665 := by
  unfold tailWord_6368205
  simp only [CollatzResearch.WordTrace]
  refine ⟨232267517894088362670626069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154845011929392241780417379 232267517894088362670626069)
  ·
    refine ⟨10887539901285392000185597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232267517894088362670626069 10887539901285392000185597)
    ·
      refine ⟨4082827462982022000069599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10887539901285392000185597 4082827462982022000069599)
      ·
        refine ⟨6124241194473033000104399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082827462982022000069599 6124241194473033000104399)
        ·
          refine ⟨9186361791709549500156599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124241194473033000104399 9186361791709549500156599)
          ·
            refine ⟨13779542687564324250234899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186361791709549500156599 13779542687564324250234899)
            ·
              refine ⟨20669314031346486375352349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779542687564324250234899 20669314031346486375352349)
              ·
                refine ⟨7750992761754932390757131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20669314031346486375352349 7750992761754932390757131)
                ·
                  refine ⟨11626489142632398586135697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7750992761754932390757131 11626489142632398586135697)
                  ·
                    refine ⟨8719866856974298939601773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11626489142632398586135697 8719866856974298939601773)
                    ·
                      refine ⟨3269950071365362102350665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8719866856974298939601773 3269950071365362102350665)
                      ·
                        rfl

theorem cell23_6368205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6368205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368205 prefixEnd_6368205 := by exact prefixLift 6368205
  have htrace : WordTrace (prefixWord ++ tailWord_6368205) baseStart_6368205 baseEnd_6368205 := by
    simpa [prefixWord, tailWord_6368205, baseEnd_6368205] using wordTrace_append hprefix tailTrace_6368205
  have hstable : (prefixWord ++ tailWord_6368205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368205).length < 2 ^ (prefixWord ++ tailWord_6368205).sum := by decide
  have hdescent : baseEnd_6368205 < baseStart_6368205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368241 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_6368241 : Nat := 118140960795 + 6368241 * 2 ^ 59
def prefixEnd_6368241 : Nat := 4983230072969 + 3 ^ 40 * 6368241 * 2
def baseEnd_6368241 : Nat := 3269968556668923961500499

theorem tailTrace_6368241 : CollatzResearch.WordTrace tailWord_6368241 prefixEnd_6368241 3269968556668923961500499 := by
  unfold tailWord_6368241
  simp only [CollatzResearch.WordTrace]
  refine ⟨232268830921957940818936577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154845887281305293879291051 232268830921957940818936577)
  ·
    refine ⟨174201623191468455614202433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232268830921957940818936577 174201623191468455614202433)
    ·
      refine ⟨130651217393601341710651825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174201623191468455614202433 130651217393601341710651825)
      ·
        refine ⟨97988413045201006282988869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130651217393601341710651825 97988413045201006282988869)
        ·
          refine ⟨18372827445975188678060413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97988413045201006282988869 18372827445975188678060413)
          ·
            refine ⟨6889810292240695754272655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18372827445975188678060413 6889810292240695754272655)
            ·
              refine ⟨10334715438361043631408983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889810292240695754272655 10334715438361043631408983)
              ·
                refine ⟨15502073157541565447113475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334715438361043631408983 15502073157541565447113475)
                ·
                  refine ⟨23253109736312348170670213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15502073157541565447113475 23253109736312348170670213)
                  ·
                    refine ⟨4359958075558565282000665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23253109736312348170670213 4359958075558565282000665)
                    ·
                      refine ⟨3269968556668923961500499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359958075558565282000665 3269968556668923961500499)
                      ·
                        rfl

theorem cell23_6368241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_6368241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368241 prefixEnd_6368241 := by exact prefixLift 6368241
  have htrace : WordTrace (prefixWord ++ tailWord_6368241) baseStart_6368241 baseEnd_6368241 := by
    simpa [prefixWord, tailWord_6368241, baseEnd_6368241] using wordTrace_append hprefix tailTrace_6368241
  have hstable : (prefixWord ++ tailWord_6368241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368241).length < 2 ^ (prefixWord ++ tailWord_6368241).sum := by decide
  have hdescent : baseEnd_6368241 < baseStart_6368241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368245 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6368245 : Nat := 118140960795 + 6368245 * 2 ^ 59
def prefixEnd_6368245 : Nat := 4983230072969 + 3 ^ 40 * 6368245 * 2
def baseEnd_6368245 : Nat := 3269970610591541945850481

theorem tailTrace_6368245 : CollatzResearch.WordTrace tailWord_6368245 prefixEnd_6368245 3269970610591541945850481 := by
  unfold tailWord_6368245
  simp only [CollatzResearch.WordTrace]
  refine ⟨232268976813943449502082189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154845984542628966334721459 232268976813943449502082189)
  ·
    refine ⟨87100866305228793563280821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232268976813943449502082189 87100866305228793563280821)
    ·
      refine ⟨8165706216115199396557577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87100866305228793563280821 8165706216115199396557577)
      ·
        refine ⟨6124279662086399547418183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8165706216115199396557577 6124279662086399547418183)
        ·
          refine ⟨9186419493129599321127275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124279662086399547418183 9186419493129599321127275)
          ·
            refine ⟨13779629239694398981690913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186419493129599321127275 13779629239694398981690913)
            ·
              refine ⟨10334721929770799236268185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13779629239694398981690913 10334721929770799236268185)
              ·
                refine ⟨7751041447328099427201139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10334721929770799236268185 7751041447328099427201139)
                ·
                  refine ⟨11626562170992149140801709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751041447328099427201139 11626562170992149140801709)
                  ·
                    refine ⟨4359960814122055927800641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11626562170992149140801709 4359960814122055927800641)
                    ·
                      refine ⟨3269970610591541945850481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4359960814122055927800641 3269970610591541945850481)
                      ·
                        rfl

theorem cell23_6368245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6368245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368245 prefixEnd_6368245 := by exact prefixLift 6368245
  have htrace : WordTrace (prefixWord ++ tailWord_6368245) baseStart_6368245 baseEnd_6368245 := by
    simpa [prefixWord, tailWord_6368245, baseEnd_6368245] using wordTrace_append hprefix tailTrace_6368245
  have hstable : (prefixWord ++ tailWord_6368245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368245).length < 2 ^ (prefixWord ++ tailWord_6368245).sum := by decide
  have hdescent : baseEnd_6368245 < baseStart_6368245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368264 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 5]
def baseStart_6368264 : Nat := 118140960795 + 6368264 * 2 ^ 59
def prefixEnd_6368264 : Nat := 4983230072969 + 3 ^ 40 * 6368264 * 2
def baseEnd_6368264 : Nat := 363331151858219707945877

theorem tailTrace_6368264 : CollatzResearch.WordTrace tailWord_6368264 prefixEnd_6368264 363331151858219707945877 := by
  unfold tailWord_6368264
  simp only [CollatzResearch.WordTrace]
  refine ⟨116134834900437307873511923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154846446533916410498015897 116134834900437307873511923)
  ·
    refine ⟨174202252350655961810267885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116134834900437307873511923 174202252350655961810267885)
    ·
      refine ⟨65325844631495985678850457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174202252350655961810267885 65325844631495985678850457)
      ·
        refine ⟨48994383473621989259137843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65325844631495985678850457 48994383473621989259137843)
        ·
          refine ⟨73491575210432983888706765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48994383473621989259137843 73491575210432983888706765)
          ·
            refine ⟨27559340703912368958265037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73491575210432983888706765 27559340703912368958265037)
            ·
              refine ⟨10334752763967138359349389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27559340703912368958265037 10334752763967138359349389)
              ·
                refine ⟨3875532286487676884756021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10334752763967138359349389 3875532286487676884756021)
                ·
                  refine ⟨363331151858219707945877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875532286487676884756021 363331151858219707945877)
                  ·
                    rfl

theorem cell23_6368264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 5].length) (baseStart_6368264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368264 prefixEnd_6368264 := by exact prefixLift 6368264
  have htrace : WordTrace (prefixWord ++ tailWord_6368264) baseStart_6368264 baseEnd_6368264 := by
    simpa [prefixWord, tailWord_6368264, baseEnd_6368264] using wordTrace_append hprefix tailTrace_6368264
  have hstable : (prefixWord ++ tailWord_6368264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368264).length < 2 ^ (prefixWord ++ tailWord_6368264).sum := by decide
  have hdescent : baseEnd_6368264 < baseStart_6368264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368277 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_6368277 : Nat := 118140960795 + 6368277 * 2 ^ 59
def prefixEnd_6368277 : Nat := 4983230072969 + 3 ^ 40 * 6368277 * 2
def baseEnd_6368277 : Nat := 1089995680657495273550111

theorem tailTrace_6368277 : CollatzResearch.WordTrace tailWord_6368277 prefixEnd_6368277 1089995680657495273550111 := by
  unfold tailWord_6368277
  simp only [CollatzResearch.WordTrace]
  refine ⟨232270143949827518967247085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154846762633218345978164723 232270143949827518967247085)
  ·
    refine ⟨87101303981185319612717657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232270143949827518967247085 87101303981185319612717657)
    ·
      refine ⟨65325977985888989709538243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87101303981185319612717657 65325977985888989709538243)
      ·
        refine ⟨97988966978833484564307365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65325977985888989709538243 97988966978833484564307365)
        ·
          refine ⟨18372931308531278355807631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97988966978833484564307365 18372931308531278355807631)
          ·
            refine ⟨27559396962796917533711447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18372931308531278355807631 27559396962796917533711447)
            ·
              refine ⟨41339095444195376300567171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27559396962796917533711447 41339095444195376300567171)
              ·
                refine ⟨62008643166293064450850757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41339095444195376300567171 62008643166293064450850757)
                ·
                  refine ⟨11626620593679949584534517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62008643166293064450850757 11626620593679949584534517)
                  ·
                    refine ⟨1089995680657495273550111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11626620593679949584534517 1089995680657495273550111)
                    ·
                      rfl

theorem cell23_6368277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_6368277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368277 prefixEnd_6368277 := by exact prefixLift 6368277
  have htrace : WordTrace (prefixWord ++ tailWord_6368277) baseStart_6368277 baseEnd_6368277 := by
    simpa [prefixWord, tailWord_6368277, baseEnd_6368277] using wordTrace_append hprefix tailTrace_6368277
  have hstable : (prefixWord ++ tailWord_6368277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368277).length < 2 ^ (prefixWord ++ tailWord_6368277).sum := by decide
  have hdescent : baseEnd_6368277 < baseStart_6368277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368287 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_6368287 : Nat := 118140960795 + 6368287 * 2 ^ 59
def prefixEnd_6368287 : Nat := 4983230072969 + 3 ^ 40 * 6368287 * 2
def baseEnd_6368287 : Nat := 3269992176779030781525287

theorem tailTrace_6368287 : CollatzResearch.WordTrace tailWord_6368287 prefixEnd_6368287 3269992176779030781525287 := by
  unfold tailWord_6368287
  simp only [CollatzResearch.WordTrace]
  refine ⟨232270508679791290675111115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154847005786527527116740743 232270508679791290675111115)
  ·
    refine ⟨348405763019686936012666673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232270508679791290675111115 348405763019686936012666673)
    ·
      refine ⟨261304322264765202009500005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348405763019686936012666673 261304322264765202009500005)
      ·
        refine ⟨48994560424643475376781251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261304322264765202009500005 48994560424643475376781251)
        ·
          refine ⟨73491840636965213065171877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48994560424643475376781251 73491840636965213065171877)
          ·
            refine ⟨13779720119430977449719727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73491840636965213065171877 13779720119430977449719727)
            ·
              refine ⟨20669580179146466174579591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779720119430977449719727 20669580179146466174579591)
              ·
                refine ⟨31004370268719699261869387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20669580179146466174579591 31004370268719699261869387)
                ·
                  refine ⟨46506555403079548892804081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31004370268719699261869387 46506555403079548892804081)
                  ·
                    refine ⟨34879916552309661669603061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46506555403079548892804081 34879916552309661669603061)
                    ·
                      refine ⟨3269992176779030781525287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34879916552309661669603061 3269992176779030781525287)
                      ·
                        rfl

theorem cell23_6368287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_6368287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368287 prefixEnd_6368287 := by exact prefixLift 6368287
  have htrace : WordTrace (prefixWord ++ tailWord_6368287) baseStart_6368287 baseEnd_6368287 := by
    simpa [prefixWord, tailWord_6368287, baseEnd_6368287] using wordTrace_append hprefix tailTrace_6368287
  have hstable : (prefixWord ++ tailWord_6368287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368287).length < 2 ^ (prefixWord ++ tailWord_6368287).sum := by decide
  have hdescent : baseEnd_6368287 < baseStart_6368287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368307 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 5, 4]
def baseStart_6368307 : Nat := 118140960795 + 6368307 * 2 ^ 59
def prefixEnd_6368307 : Nat := 4983230072969 + 3 ^ 40 * 6368307 * 2
def baseEnd_6368307 : Nat := 1090000815464040234425065

theorem tailTrace_6368307 : CollatzResearch.WordTrace tailWord_6368307 prefixEnd_6368307 1090000815464040234425065 := by
  unfold tailWord_6368307
  simp only [CollatzResearch.WordTrace]
  refine ⟨232271238139718834090839175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154847492093145889393892783 232271238139718834090839175)
  ·
    refine ⟨348406857209578251136258763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232271238139718834090839175 348406857209578251136258763)
    ·
      refine ⟨522610285814367376704388145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348406857209578251136258763 522610285814367376704388145)
      ·
        refine ⟨391957714360775532528291109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522610285814367376704388145 391957714360775532528291109)
        ·
          refine ⟨73492071442645412349054583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391957714360775532528291109 73492071442645412349054583)
          ·
            refine ⟨110238107163968118523581875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73492071442645412349054583 110238107163968118523581875)
            ·
              refine ⟨165357160745952177785372813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110238107163968118523581875 165357160745952177785372813)
              ·
                refine ⟨62008935279732066669514805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165357160745952177785372813 62008935279732066669514805)
                ·
                  refine ⟨5813337682474881250267013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62008935279732066669514805 5813337682474881250267013)
                  ·
                    refine ⟨1090000815464040234425065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813337682474881250267013 1090000815464040234425065)
                    ·
                      rfl

theorem cell23_6368307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 4].length) (baseStart_6368307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368307 prefixEnd_6368307 := by exact prefixLift 6368307
  have htrace : WordTrace (prefixWord ++ tailWord_6368307) baseStart_6368307 baseEnd_6368307 := by
    simpa [prefixWord, tailWord_6368307, baseEnd_6368307] using wordTrace_append hprefix tailTrace_6368307
  have hstable : (prefixWord ++ tailWord_6368307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368307).length < 2 ^ (prefixWord ++ tailWord_6368307).sum := by decide
  have hdescent : baseEnd_6368307 < baseStart_6368307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368334 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_6368334 : Nat := 118140960795 + 6368334 * 2 ^ 59
def prefixEnd_6368334 : Nat := 4983230072969 + 3 ^ 40 * 6368334 * 2
def baseEnd_6368334 : Nat := 3270016310369792097637571

theorem tailTrace_6368334 : CollatzResearch.WordTrace tailWord_6368334 prefixEnd_6368334 3270016310369792097637571 := by
  unfold tailWord_6368334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034027863827627212759007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154848148607080678468048037 29034027863827627212759007)
  ·
    refine ⟨43551041795741440819138511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29034027863827627212759007 43551041795741440819138511)
    ·
      refine ⟨65326562693612161228707767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43551041795741440819138511 65326562693612161228707767)
      ·
        refine ⟨97989844040418241843061651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65326562693612161228707767 97989844040418241843061651)
        ·
          refine ⟨146984766060627362764592477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97989844040418241843061651 146984766060627362764592477)
          ·
            refine ⟨55119287272735261036722179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146984766060627362764592477 55119287272735261036722179)
            ·
              refine ⟨82678930909102891555083269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55119287272735261036722179 82678930909102891555083269)
              ·
                refine ⟨15502299545456792166578113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82678930909102891555083269 15502299545456792166578113)
                ·
                  refine ⟨11626724659092594124933585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15502299545456792166578113 11626724659092594124933585)
                  ·
                    refine ⟨8720043494319445593700189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11626724659092594124933585 8720043494319445593700189)
                    ·
                      refine ⟨3270016310369792097637571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720043494319445593700189 3270016310369792097637571)
                      ·
                        rfl

theorem cell23_6368334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_6368334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368334 prefixEnd_6368334 := by exact prefixLift 6368334
  have htrace : WordTrace (prefixWord ++ tailWord_6368334) baseStart_6368334 baseEnd_6368334 := by
    simpa [prefixWord, tailWord_6368334, baseEnd_6368334] using wordTrace_append hprefix tailTrace_6368334
  have hstable : (prefixWord ++ tailWord_6368334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368334).length < 2 ^ (prefixWord ++ tailWord_6368334).sum := by decide
  have hdescent : baseEnd_6368334 < baseStart_6368334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368337 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 6]
def baseStart_6368337 : Nat := 118140960795 + 6368337 * 2 ^ 59
def prefixEnd_6368337 : Nat := 4983230072969 + 3 ^ 40 * 6368337 * 2
def baseEnd_6368337 : Nat := 363335316756861731766673

theorem tailTrace_6368337 : CollatzResearch.WordTrace tailWord_6368337 prefixEnd_6368337 363335316756861731766673 := by
  unfold tailWord_6368337
  simp only [CollatzResearch.WordTrace]
  refine ⟨232272332329610149214431265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154848221553073432809620843 232272332329610149214431265)
  ·
    refine ⟨174204249247207611910823449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232272332329610149214431265 174204249247207611910823449)
    ·
      refine ⟨130653186935405708933117587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174204249247207611910823449 130653186935405708933117587)
      ·
        refine ⟨195979780403108563399676381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130653186935405708933117587 195979780403108563399676381)
        ·
          refine ⟨73492417651165711274878643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195979780403108563399676381 73492417651165711274878643)
          ·
            refine ⟨110238626476748566912317965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73492417651165711274878643 110238626476748566912317965)
            ·
              refine ⟨41339484928780712592119237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110238626476748566912317965 41339484928780712592119237)
              ·
                refine ⟨7751153424146383611022357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41339484928780712592119237 7751153424146383611022357)
                ·
                  refine ⟨363335316756861731766673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7751153424146383611022357 363335316756861731766673)
                  ·
                    rfl

theorem cell23_6368337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_6368337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368337 prefixEnd_6368337 := by exact prefixLift 6368337
  have htrace : WordTrace (prefixWord ++ tailWord_6368337) baseStart_6368337 baseEnd_6368337 := by
    simpa [prefixWord, tailWord_6368337, baseEnd_6368337] using wordTrace_append hprefix tailTrace_6368337
  have hstable : (prefixWord ++ tailWord_6368337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368337).length < 2 ^ (prefixWord ++ tailWord_6368337).sum := by decide
  have hdescent : baseEnd_6368337 < baseStart_6368337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368341 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6368341 : Nat := 118140960795 + 6368341 * 2 ^ 59
def prefixEnd_6368341 : Nat := 4983230072969 + 3 ^ 40 * 6368341 * 2
def baseEnd_6368341 : Nat := 1090006634911457856750013

theorem tailTrace_6368341 : CollatzResearch.WordTrace tailWord_6368341 prefixEnd_6368341 1090006634911457856750013 := by
  unfold tailWord_6368341
  simp only [CollatzResearch.WordTrace]
  refine ⟨232272478221595657897576877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154848318814397105265051251 232272478221595657897576877)
  ·
    refine ⟨87102179333098371711591329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232272478221595657897576877 87102179333098371711591329)
    ·
      refine ⟨65326634499823778783693497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87102179333098371711591329 65326634499823778783693497)
      ·
        refine ⟨48994975874867834087770123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65326634499823778783693497 48994975874867834087770123)
        ·
          refine ⟨73492463812301751131655185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48994975874867834087770123 73492463812301751131655185)
          ·
            refine ⟨55119347859226313348741389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73492463812301751131655185 55119347859226313348741389)
            ·
              refine ⟨20669755447209867505778021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55119347859226313348741389 20669755447209867505778021)
              ·
                refine ⟨3875579146351850157333379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20669755447209867505778021 3875579146351850157333379)
                ·
                  refine ⟨5813368719527775236000069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875579146351850157333379 5813368719527775236000069)
                  ·
                    refine ⟨1090006634911457856750013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813368719527775236000069 1090006634911457856750013)
                    ·
                      rfl

theorem cell23_6368341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6368341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368341 prefixEnd_6368341 := by exact prefixLift 6368341
  have htrace : WordTrace (prefixWord ++ tailWord_6368341) baseStart_6368341 baseEnd_6368341 := by
    simpa [prefixWord, tailWord_6368341, baseEnd_6368341] using wordTrace_append hprefix tailTrace_6368341
  have hstable : (prefixWord ++ tailWord_6368341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368341).length < 2 ^ (prefixWord ++ tailWord_6368341).sum := by decide
  have hdescent : baseEnd_6368341 < baseStart_6368341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368367 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 3, 5]
def baseStart_6368367 : Nat := 118140960795 + 6368367 * 2 ^ 59
def prefixEnd_6368367 : Nat := 4983230072969 + 3 ^ 40 * 6368367 * 2
def baseEnd_6368367 : Nat := 1090011085077130156174973

theorem tailTrace_6368367 : CollatzResearch.WordTrace tailWord_6368367 prefixEnd_6368367 1090011085077130156174973 := by
  unfold tailWord_6368367
  simp only [CollatzResearch.WordTrace]
  refine ⟨232273426519501464338023355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154848951013000976225348903 232273426519501464338023355)
  ·
    refine ⟨348410139779252196507035033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232273426519501464338023355 348410139779252196507035033)
    ·
      refine ⟨261307604834439147380276275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348410139779252196507035033 261307604834439147380276275)
      ·
        refine ⟨391961407251658721070414413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261307604834439147380276275 391961407251658721070414413)
        ·
          refine ⟨146985527719372020401405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391961407251658721070414413 146985527719372020401405405)
          ·
            refine ⟨55119572894764507650527027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146985527719372020401405405 55119572894764507650527027)
            ·
              refine ⟨82679359342146761475790541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55119572894764507650527027 82679359342146761475790541)
              ·
                refine ⟨31004759753305035553421453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82679359342146761475790541 31004759753305035553421453)
                ·
                  refine ⟨11626784907489388332533045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31004759753305035553421453 11626784907489388332533045)
                  ·
                    refine ⟨1090011085077130156174973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11626784907489388332533045 1090011085077130156174973)
                    ·
                      rfl

theorem cell23_6368367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_6368367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368367 prefixEnd_6368367 := by exact prefixLift 6368367
  have htrace : WordTrace (prefixWord ++ tailWord_6368367) baseStart_6368367 baseEnd_6368367 := by
    simpa [prefixWord, tailWord_6368367, baseEnd_6368367] using wordTrace_append hprefix tailTrace_6368367
  have hstable : (prefixWord ++ tailWord_6368367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368367).length < 2 ^ (prefixWord ++ tailWord_6368367).sum := by decide
  have hdescent : baseEnd_6368367 < baseStart_6368367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368398 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6368398 : Nat := 118140960795 + 6368398 * 2 ^ 59
def prefixEnd_6368398 : Nat := 4983230072969 + 3 ^ 40 * 6368398 * 2
def baseEnd_6368398 : Nat := 3270049173131679847237277

theorem tailTrace_6368398 : CollatzResearch.WordTrace tailWord_6368398 prefixEnd_6368398 3270049173131679847237277 := by
  unfold tailWord_6368398
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034319647798644579050231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154849704788259437754934565 29034319647798644579050231)
  ·
    refine ⟨43551479471697966868575347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29034319647798644579050231 43551479471697966868575347)
    ·
      refine ⟨65327219207546950302863021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43551479471697966868575347 65327219207546950302863021)
      ·
        refine ⟨24497707202830106363573633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65327219207546950302863021 24497707202830106363573633)
        ·
          refine ⟨18373280402122579772680225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24497707202830106363573633 18373280402122579772680225)
          ·
            refine ⟨13779960301591934829510169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18373280402122579772680225 13779960301591934829510169)
            ·
              refine ⟨10334970226193951122132627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13779960301591934829510169 10334970226193951122132627)
              ·
                refine ⟨15502455339290926683198941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334970226193951122132627 15502455339290926683198941)
                ·
                  refine ⟨5813420752234097506199603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15502455339290926683198941 5813420752234097506199603)
                  ·
                    refine ⟨8720131128351146259299405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5813420752234097506199603 8720131128351146259299405)
                    ·
                      refine ⟨3270049173131679847237277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720131128351146259299405 3270049173131679847237277)
                      ·
                        rfl

theorem cell23_6368398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6368398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368398 prefixEnd_6368398 := by exact prefixLift 6368398
  have htrace : WordTrace (prefixWord ++ tailWord_6368398) baseStart_6368398 baseEnd_6368398 := by
    simpa [prefixWord, tailWord_6368398, baseEnd_6368398] using wordTrace_append hprefix tailTrace_6368398
  have hstable : (prefixWord ++ tailWord_6368398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368398).length < 2 ^ (prefixWord ++ tailWord_6368398).sum := by decide
  have hdescent : baseEnd_6368398 < baseStart_6368398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368418 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_6368418 : Nat := 118140960795 + 6368418 * 2 ^ 59
def prefixEnd_6368418 : Nat := 4983230072969 + 3 ^ 40 * 6368418 * 2
def baseEnd_6368418 : Nat := 1090019814248256589662395

theorem tailTrace_6368418 : CollatzResearch.WordTrace tailWord_6368418 prefixEnd_6368418 1090019814248256589662395 := by
  unfold tailWord_6368418
  simp only [CollatzResearch.WordTrace]
  refine ⟨58068821660579175012032477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154850191094877800032086605 58068821660579175012032477)
  ·
    refine ⟨21775808122717190629512179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58068821660579175012032477 21775808122717190629512179)
    ·
      refine ⟨32663712184075785944268269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21775808122717190629512179 32663712184075785944268269)
      ·
        refine ⟨12248892069028419729100601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32663712184075785944268269 12248892069028419729100601)
        ·
          refine ⟨9186669051771314796825451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12248892069028419729100601 9186669051771314796825451)
          ·
            refine ⟨13780003577656972195238177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186669051771314796825451 13780003577656972195238177)
            ·
              refine ⟨10335002683242729146428633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13780003577656972195238177 10335002683242729146428633)
              ·
                refine ⟨7751252012432046859821475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335002683242729146428633 7751252012432046859821475)
                ·
                  refine ⟨11626878018648070289732213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751252012432046859821475 11626878018648070289732213)
                  ·
                    refine ⟨1090019814248256589662395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11626878018648070289732213 1090019814248256589662395)
                    ·
                      rfl

theorem cell23_6368418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_6368418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368418 prefixEnd_6368418 := by exact prefixLift 6368418
  have htrace : WordTrace (prefixWord ++ tailWord_6368418) baseStart_6368418 baseEnd_6368418 := by
    simpa [prefixWord, tailWord_6368418, baseEnd_6368418] using wordTrace_append hprefix tailTrace_6368418
  have hstable : (prefixWord ++ tailWord_6368418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368418).length < 2 ^ (prefixWord ++ tailWord_6368418).sum := by decide
  have hdescent : baseEnd_6368418 < baseStart_6368418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368421 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_6368421 : Nat := 118140960795 + 6368421 * 2 ^ 59
def prefixEnd_6368421 : Nat := 4983230072969 + 3 ^ 40 * 6368421 * 2
def baseEnd_6368421 : Nat := 3270060983186733257249671

theorem tailTrace_6368421 : CollatzResearch.WordTrace tailWord_6368421 prefixEnd_6368421 3270060983186733257249671 := by
  unfold tailWord_6368421
  simp only [CollatzResearch.WordTrace]
  refine ⟨232275396061305831560489117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154850264040870554373659411 232275396061305831560489117)
  ·
    refine ⟨87103273522989686835183419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232275396061305831560489117 87103273522989686835183419)
    ·
      refine ⟨130654910284484530252775129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87103273522989686835183419 130654910284484530252775129)
      ·
        refine ⟨97991182713363397689581347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130654910284484530252775129 97991182713363397689581347)
        ·
          refine ⟨146986774070045096534372021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97991182713363397689581347 146986774070045096534372021)
          ·
            refine ⟨13780010069066727800097377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146986774070045096534372021 13780010069066727800097377)
            ·
              refine ⟨10335007551800045850073033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13780010069066727800097377 10335007551800045850073033)
              ·
                refine ⟨7751255663850034387554775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335007551800045850073033 7751255663850034387554775)
                ·
                  refine ⟨11626883495775051581332163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751255663850034387554775 11626883495775051581332163)
                  ·
                    refine ⟨17440325243662577371998245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11626883495775051581332163 17440325243662577371998245)
                    ·
                      refine ⟨3270060983186733257249671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17440325243662577371998245 3270060983186733257249671)
                      ·
                        rfl

theorem cell23_6368421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_6368421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368421 prefixEnd_6368421 := by exact prefixLift 6368421
  have htrace : WordTrace (prefixWord ++ tailWord_6368421) baseStart_6368421 baseEnd_6368421 := by
    simpa [prefixWord, tailWord_6368421, baseEnd_6368421] using wordTrace_append hprefix tailTrace_6368421
  have hstable : (prefixWord ++ tailWord_6368421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368421).length < 2 ^ (prefixWord ++ tailWord_6368421).sum := by decide
  have hdescent : baseEnd_6368421 < baseStart_6368421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368441 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6368441 : Nat := 118140960795 + 6368441 * 2 ^ 59
def prefixEnd_6368441 : Nat := 4983230072969 + 3 ^ 40 * 6368441 * 2
def baseEnd_6368441 : Nat := 3270071252799823178999579

theorem tailTrace_6368441 : CollatzResearch.WordTrace tailWord_6368441 prefixEnd_6368441 3270071252799823178999579 := by
  unfold tailWord_6368441
  simp only [CollatzResearch.WordTrace]
  refine ⟨232276125521233374976217177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154850750347488916650811451 232276125521233374976217177)
  ·
    refine ⟨174207094140925031232162883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232276125521233374976217177 174207094140925031232162883)
    ·
      refine ⟨261310641211387546848244325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174207094140925031232162883 261310641211387546848244325)
      ·
        refine ⟨48995745227135165034045811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261310641211387546848244325 48995745227135165034045811)
        ·
          refine ⟨73493617840702747551068717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48995745227135165034045811 73493617840702747551068717)
          ·
            refine ⟨27560106690263530331650769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73493617840702747551068717 27560106690263530331650769)
            ·
              refine ⟨20670080017697647748738077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27560106690263530331650769 20670080017697647748738077)
              ·
                refine ⟨7751280006636617905776779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20670080017697647748738077 7751280006636617905776779)
                ·
                  refine ⟨11626920009954926858665169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751280006636617905776779 11626920009954926858665169)
                  ·
                    refine ⟨8720190007466195143998877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11626920009954926858665169 8720190007466195143998877)
                    ·
                      refine ⟨3270071252799823178999579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720190007466195143998877 3270071252799823178999579)
                      ·
                        rfl

theorem cell23_6368441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6368441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368441 prefixEnd_6368441 := by exact prefixLift 6368441
  have htrace : WordTrace (prefixWord ++ tailWord_6368441) baseStart_6368441 baseEnd_6368441 := by
    simpa [prefixWord, tailWord_6368441, baseEnd_6368441] using wordTrace_append hprefix tailTrace_6368441
  have hstable : (prefixWord ++ tailWord_6368441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368441).length < 2 ^ (prefixWord ++ tailWord_6368441).sum := by decide
  have hdescent : baseEnd_6368441 < baseStart_6368441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368444 : List Nat := [2, 2, 2, 3, 2, 3, 9]
def baseStart_6368444 : Nat := 118140960795 + 6368444 * 2 ^ 59
def prefixEnd_6368444 : Nat := 4983230072969 + 3 ^ 40 * 6368444 * 2
def baseEnd_6368444 : Nat := 40371269052367736632865

theorem tailTrace_6368444 : CollatzResearch.WordTrace tailWord_6368444 prefixEnd_6368444 40371269052367736632865 := by
  unfold tailWord_6368444
  simp only [CollatzResearch.WordTrace]
  refine ⟨116138117470111253244288193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154850823293481670992384257 116138117470111253244288193)
  ·
    refine ⟨87103588102583439933216145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116138117470111253244288193 87103588102583439933216145)
    ·
      refine ⟨65327691076937579949912109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87103588102583439933216145 65327691076937579949912109)
      ·
        refine ⟨24497884153851592481217041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65327691076937579949912109 24497884153851592481217041)
        ·
          refine ⟨18373413115388694360912781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24497884153851592481217041 18373413115388694360912781)
          ·
            refine ⟨6890029918270760385342293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18373413115388694360912781 6890029918270760385342293)
            ·
              refine ⟨40371269052367736632865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6890029918270760385342293 40371269052367736632865)
              ·
                rfl

theorem cell23_6368444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 9].length) (baseStart_6368444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368444 prefixEnd_6368444 := by exact prefixLift 6368444
  have htrace : WordTrace (prefixWord ++ tailWord_6368444) baseStart_6368444 baseEnd_6368444 := by
    simpa [prefixWord, tailWord_6368444, baseEnd_6368444] using wordTrace_append hprefix tailTrace_6368444
  have hstable : (prefixWord ++ tailWord_6368444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368444).length < 2 ^ (prefixWord ++ tailWord_6368444).sum := by decide
  have hdescent : baseEnd_6368444 < baseStart_6368444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368467 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_6368467 : Nat := 118140960795 + 6368467 * 2 ^ 59
def prefixEnd_6368467 : Nat := 4983230072969 + 3 ^ 40 * 6368467 * 2
def baseEnd_6368467 : Nat := 3270084603296840077274459

theorem tailTrace_6368467 : CollatzResearch.WordTrace tailWord_6368467 prefixEnd_6368467 3270084603296840077274459 := by
  unfold tailWord_6368467
  simp only [CollatzResearch.WordTrace]
  refine ⟨232277073819139181416663655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154851382546092787611109103 232277073819139181416663655)
  ·
    refine ⟨348415610728708772124995483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232277073819139181416663655 348415610728708772124995483)
    ·
      refine ⟨522623416093063158187493225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348415610728708772124995483 522623416093063158187493225)
      ·
        refine ⟨391967562069797368640619919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522623416093063158187493225 391967562069797368640619919)
        ·
          refine ⟨587951343104696052960929879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391967562069797368640619919 587951343104696052960929879)
          ·
            refine ⟨881927014657044079441394819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587951343104696052960929879 881927014657044079441394819)
            ·
              refine ⟨1322890521985566119162092229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881927014657044079441394819 1322890521985566119162092229)
              ·
                refine ⟨248041972872293647342892293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1322890521985566119162092229 248041972872293647342892293)
                ·
                  refine ⟨46507869913555058876792305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248041972872293647342892293 46507869913555058876792305)
                  ·
                    refine ⟨34880902435166294157594229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46507869913555058876792305 34880902435166294157594229)
                    ·
                      refine ⟨3270084603296840077274459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34880902435166294157594229 3270084603296840077274459)
                      ·
                        rfl

theorem cell23_6368467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_6368467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368467 prefixEnd_6368467 := by exact prefixLift 6368467
  have htrace : WordTrace (prefixWord ++ tailWord_6368467) baseStart_6368467 baseEnd_6368467 := by
    simpa [prefixWord, tailWord_6368467, baseEnd_6368467] using wordTrace_append hprefix tailTrace_6368467
  have hstable : (prefixWord ++ tailWord_6368467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368467).length < 2 ^ (prefixWord ++ tailWord_6368467).sum := by decide
  have hdescent : baseEnd_6368467 < baseStart_6368467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368524 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6368524 : Nat := 118140960795 + 6368524 * 2 ^ 59
def prefixEnd_6368524 : Nat := 4983230072969 + 3 ^ 40 * 6368524 * 2
def baseEnd_6368524 : Nat := 3270113871694146354261697

theorem tailTrace_6368524 : CollatzResearch.WordTrace tailWord_6368524 prefixEnd_6368524 3270113871694146354261697 := by
  unfold tailWord_6368524
  simp only [CollatzResearch.WordTrace]
  refine ⟨116139576389966340075744313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154852768519955120100992417 116139576389966340075744313)
  ·
    refine ⟨87104682292474755056808235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116139576389966340075744313 87104682292474755056808235)
    ·
      refine ⟨130657023438712132585212353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87104682292474755056808235 130657023438712132585212353)
      ·
        refine ⟨97992767579034099438909265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130657023438712132585212353 97992767579034099438909265)
        ·
          refine ⟨73494575684275574579181949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97992767579034099438909265 73494575684275574579181949)
          ·
            refine ⟨27560465881603340467193231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73494575684275574579181949 27560465881603340467193231)
            ·
              refine ⟨41340698822405010700789847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27560465881603340467193231 41340698822405010700789847)
              ·
                refine ⟨62011048233607516051184771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41340698822405010700789847 62011048233607516051184771)
                ·
                  refine ⟨93016572350411274076777157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62011048233607516051184771 93016572350411274076777157)
                  ·
                    refine ⟨17440607315702113889395717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93016572350411274076777157 17440607315702113889395717)
                    ·
                      refine ⟨3270113871694146354261697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17440607315702113889395717 3270113871694146354261697)
                      ·
                        rfl

theorem cell23_6368524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6368524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368524 prefixEnd_6368524 := by exact prefixLift 6368524
  have htrace : WordTrace (prefixWord ++ tailWord_6368524) baseStart_6368524 baseEnd_6368524 := by
    simpa [prefixWord, tailWord_6368524, baseEnd_6368524] using wordTrace_append hprefix tailTrace_6368524
  have hstable : (prefixWord ++ tailWord_6368524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368524).length < 2 ^ (prefixWord ++ tailWord_6368524).sum := by decide
  have hdescent : baseEnd_6368524 < baseStart_6368524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368561 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_6368561 : Nat := 118140960795 + 6368561 * 2 ^ 59
def prefixEnd_6368561 : Nat := 4983230072969 + 3 ^ 40 * 6368561 * 2
def baseEnd_6368561 : Nat := 3270132870478362709499027

theorem tailTrace_6368561 : CollatzResearch.WordTrace tailWord_6368561 prefixEnd_6368561 3270132870478362709499027 := by
  unfold tailWord_6368561
  simp only [CollatzResearch.WordTrace]
  refine ⟨232280502280798635470585537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154853668187199090313723691 232280502280798635470585537)
  ·
    refine ⟨174210376710598976602939153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232280502280798635470585537 174210376710598976602939153)
    ·
      refine ⟨130657782532949232452204365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174210376710598976602939153 130657782532949232452204365)
      ·
        refine ⟨48996668449855962169576637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130657782532949232452204365 48996668449855962169576637)
        ·
          refine ⟨18373750668695985813591239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48996668449855962169576637 18373750668695985813591239)
          ·
            refine ⟨27560626003043978720386859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18373750668695985813591239 27560626003043978720386859)
            ·
              refine ⟨41340939004565968080580289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27560626003043978720386859 41340939004565968080580289)
              ·
                refine ⟨31005704253424476060435217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41340939004565968080580289 31005704253424476060435217)
                ·
                  refine ⟨23254278190068357045326413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31005704253424476060435217 23254278190068357045326413)
                  ·
                    refine ⟨8720354321275633891997405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23254278190068357045326413 8720354321275633891997405)
                    ·
                      refine ⟨3270132870478362709499027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720354321275633891997405 3270132870478362709499027)
                      ·
                        rfl

theorem cell23_6368561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_6368561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368561 prefixEnd_6368561 := by exact prefixLift 6368561
  have htrace : WordTrace (prefixWord ++ tailWord_6368561) baseStart_6368561 baseEnd_6368561 := by
    simpa [prefixWord, tailWord_6368561, baseEnd_6368561] using wordTrace_append hprefix tailTrace_6368561
  have hstable : (prefixWord ++ tailWord_6368561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368561).length < 2 ^ (prefixWord ++ tailWord_6368561).sum := by decide
  have hdescent : baseEnd_6368561 < baseStart_6368561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368562 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_6368562 : Nat := 118140960795 + 6368562 * 2 ^ 59
def prefixEnd_6368562 : Nat := 4983230072969 + 3 ^ 40 * 6368562 * 2
def baseEnd_6368562 : Nat := 3270133383959017205586523

theorem tailTrace_6368562 : CollatzResearch.WordTrace tailWord_6368562 prefixEnd_6368562 3270133383959017205586523 := by
  unfold tailWord_6368562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070134688448753160342985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154853692502530008427581293 58070134688448753160342985)
  ·
    refine ⟨43552601016336564870257239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58070134688448753160342985 43552601016336564870257239)
    ·
      refine ⟨65328901524504847305385859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43552601016336564870257239 65328901524504847305385859)
      ·
        refine ⟨97993352286757270958078789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65328901524504847305385859 97993352286757270958078789)
        ·
          refine ⟨18373753553766988304639773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97993352286757270958078789 18373753553766988304639773)
          ·
            refine ⟨6890157582662620614239915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18373753553766988304639773 6890157582662620614239915)
            ·
              refine ⟨10335236373993930921359873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890157582662620614239915 10335236373993930921359873)
              ·
                refine ⟨7751427280495448191019905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335236373993930921359873 7751427280495448191019905)
                ·
                  refine ⟨5813570460371586143264929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751427280495448191019905 5813570460371586143264929)
                  ·
                    refine ⟨4360177845278689607448697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5813570460371586143264929 4360177845278689607448697)
                    ·
                      refine ⟨3270133383959017205586523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360177845278689607448697 3270133383959017205586523)
                      ·
                        rfl

theorem cell23_6368562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_6368562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368562 prefixEnd_6368562 := by exact prefixLift 6368562
  have htrace : WordTrace (prefixWord ++ tailWord_6368562) baseStart_6368562 baseEnd_6368562 := by
    simpa [prefixWord, tailWord_6368562, baseEnd_6368562] using wordTrace_append hprefix tailTrace_6368562
  have hstable : (prefixWord ++ tailWord_6368562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368562).length < 2 ^ (prefixWord ++ tailWord_6368562).sum := by decide
  have hdescent : baseEnd_6368562 < baseStart_6368562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368594 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_6368594 : Nat := 118140960795 + 6368594 * 2 ^ 59
def prefixEnd_6368594 : Nat := 4983230072969 + 3 ^ 40 * 6368594 * 2
def baseEnd_6368594 : Nat := 1090049938446653693462125

theorem tailTrace_6368594 : CollatzResearch.WordTrace tailWord_6368594 prefixEnd_6368594 1090049938446653693462125 := by
  unfold tailWord_6368594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070426472419770526634209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154854470593119388071024557 58070426472419770526634209)
  ·
    refine ⟨43552819854314827894975657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58070426472419770526634209 43552819854314827894975657)
    ·
      refine ⟨32664614890736120921231743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43552819854314827894975657 32664614890736120921231743)
      ·
        refine ⟨48996922336104181381847615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32664614890736120921231743 48996922336104181381847615)
        ·
          refine ⟨73495383504156272072771423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48996922336104181381847615 73495383504156272072771423)
          ·
            refine ⟨110243075256234408109157135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73495383504156272072771423 110243075256234408109157135)
            ·
              refine ⟨165364612884351612163735703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110243075256234408109157135 165364612884351612163735703)
              ·
                refine ⟨248046919326527418245603555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165364612884351612163735703 248046919326527418245603555)
                ·
                  refine ⟨372070378989791127368405333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248046919326527418245603555 372070378989791127368405333)
                  ·
                    refine ⟨1090049938446653693462125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 372070378989791127368405333 1090049938446653693462125)
                    ·
                      rfl

theorem cell23_6368594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_6368594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368594 prefixEnd_6368594 := by exact prefixLift 6368594
  have htrace : WordTrace (prefixWord ++ tailWord_6368594) baseStart_6368594 baseEnd_6368594 := by
    simpa [prefixWord, tailWord_6368594, baseEnd_6368594] using wordTrace_append hprefix tailTrace_6368594
  have hstable : (prefixWord ++ tailWord_6368594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368594).length < 2 ^ (prefixWord ++ tailWord_6368594).sum := by decide
  have hdescent : baseEnd_6368594 < baseStart_6368594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368601 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 6, 2]
def baseStart_6368601 : Nat := 118140960795 + 6368601 * 2 ^ 59
def prefixEnd_6368601 : Nat := 4983230072969 + 3 ^ 40 * 6368601 * 2
def baseEnd_6368601 : Nat := 3270153409704542552998843

theorem tailTrace_6368601 : CollatzResearch.WordTrace tailWord_6368601 prefixEnd_6368601 3270153409704542552998843 := by
  unfold tailWord_6368601
  simp only [CollatzResearch.WordTrace]
  refine ⟨232281961200653722302041657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154854640800435814868027771 232281961200653722302041657)
  ·
    refine ⟨174211470900490291726531243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232281961200653722302041657 174211470900490291726531243)
    ·
      refine ⟨261317206350735437589796865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174211470900490291726531243 261317206350735437589796865)
      ·
        refine ⟨195987904763051578192347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261317206350735437589796865 195987904763051578192347649)
        ·
          refine ⟨146990928572288683644260737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195987904763051578192347649 146990928572288683644260737)
          ·
            refine ⟨110243196429216512733195553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146990928572288683644260737 110243196429216512733195553)
            ·
              refine ⟨82682397321912384549896665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110243196429216512733195553 82682397321912384549896665)
              ·
                refine ⟨62011797991434288412422499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82682397321912384549896665 62011797991434288412422499)
                ·
                  refine ⟨93017696987151432618633749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62011797991434288412422499 93017696987151432618633749)
                  ·
                    refine ⟨4360204546272723403998457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93017696987151432618633749 4360204546272723403998457)
                    ·
                      refine ⟨3270153409704542552998843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360204546272723403998457 3270153409704542552998843)
                      ·
                        rfl

theorem cell23_6368601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_6368601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368601 prefixEnd_6368601 := by exact prefixLift 6368601
  have htrace : WordTrace (prefixWord ++ tailWord_6368601) baseStart_6368601 baseEnd_6368601 := by
    simpa [prefixWord, tailWord_6368601, baseEnd_6368601] using wordTrace_append hprefix tailTrace_6368601
  have hstable : (prefixWord ++ tailWord_6368601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368601).length < 2 ^ (prefixWord ++ tailWord_6368601).sum := by decide
  have hdescent : baseEnd_6368601 < baseStart_6368601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368624 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 8]
def baseStart_6368624 : Nat := 118140960795 + 6368624 * 2 ^ 59
def prefixEnd_6368624 : Nat := 4983230072969 + 3 ^ 40 * 6368624 * 2
def baseEnd_6368624 : Nat := 363351691084399551445693

theorem tailTrace_6368624 : CollatzResearch.WordTrace tailWord_6368624 prefixEnd_6368624 363351691084399551445693 := by
  unfold tailWord_6368624
  simp only [CollatzResearch.WordTrace]
  refine ⟨116141400039785198615064463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154855200053046931486752617 116141400039785198615064463)
  ·
    refine ⟨174212100059677797922596695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116141400039785198615064463 174212100059677797922596695)
    ·
      refine ⟨261318150089516696883895043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174212100059677797922596695 261318150089516696883895043)
      ·
        refine ⟨391977225134275045325842565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261318150089516696883895043 391977225134275045325842565)
        ·
          refine ⟨73495729712676570998595481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391977225134275045325842565 73495729712676570998595481)
          ·
            refine ⟨55121797284507428248946611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73495729712676570998595481 55121797284507428248946611)
            ·
              refine ⟨82682695926761142373419917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55121797284507428248946611 82682695926761142373419917)
              ·
                refine ⟨31006010972535428390032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82682695926761142373419917 31006010972535428390032469)
                ·
                  refine ⟨363351691084399551445693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31006010972535428390032469 363351691084399551445693)
                  ·
                    rfl

theorem cell23_6368624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_6368624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368624 prefixEnd_6368624 := by exact prefixLift 6368624
  have htrace : WordTrace (prefixWord ++ tailWord_6368624) baseStart_6368624 baseEnd_6368624 := by
    simpa [prefixWord, tailWord_6368624, baseEnd_6368624] using wordTrace_append hprefix tailTrace_6368624
  have hstable : (prefixWord ++ tailWord_6368624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368624).length < 2 ^ (prefixWord ++ tailWord_6368624).sum := by decide
  have hdescent : baseEnd_6368624 < baseStart_6368624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368725 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6368725 : Nat := 118140960795 + 6368725 * 2 ^ 59
def prefixEnd_6368725 : Nat := 4983230072969 + 3 ^ 40 * 6368725 * 2
def baseEnd_6368725 : Nat := 3270217081305700067848273

theorem tailTrace_6368725 : CollatzResearch.WordTrace tailWord_6368725 prefixEnd_6368725 3270217081305700067848273 := by
  unfold tailWord_6368725
  simp only [CollatzResearch.WordTrace]
  refine ⟨232286483852204491479555629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154857655901469660986370419 232286483852204491479555629)
  ·
    refine ⟨87107431444576684304833361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232286483852204491479555629 87107431444576684304833361)
    ·
      refine ⟨65330573583432513228625021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87107431444576684304833361 65330573583432513228625021)
      ·
        refine ⟨24498965093787192460734383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65330573583432513228625021 24498965093787192460734383)
        ·
          refine ⟨36748447640680788691101575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24498965093787192460734383 36748447640680788691101575)
          ·
            refine ⟨55122671461021183036652363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36748447640680788691101575 55122671461021183036652363)
            ·
              refine ⟨82684007191531774554978545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55122671461021183036652363 82684007191531774554978545)
              ·
                refine ⟨62013005393648830916233909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82684007191531774554978545 62013005393648830916233909)
                ·
                  refine ⟨5813719255654577898396929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62013005393648830916233909 5813719255654577898396929)
                  ·
                    refine ⟨4360289441740933423797697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5813719255654577898396929 4360289441740933423797697)
                    ·
                      refine ⟨3270217081305700067848273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360289441740933423797697 3270217081305700067848273)
                      ·
                        rfl

theorem cell23_6368725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6368725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368725 prefixEnd_6368725 := by exact prefixLift 6368725
  have htrace : WordTrace (prefixWord ++ tailWord_6368725) baseStart_6368725 baseEnd_6368725 := by
    simpa [prefixWord, tailWord_6368725, baseEnd_6368725] using wordTrace_append hprefix tailTrace_6368725
  have hstable : (prefixWord ++ tailWord_6368725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368725).length < 2 ^ (prefixWord ++ tailWord_6368725).sum := by decide
  have hdescent : baseEnd_6368725 < baseStart_6368725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368775 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6368775 : Nat := 118140960795 + 6368775 * 2 ^ 59
def prefixEnd_6368775 : Nat := 4983230072969 + 3 ^ 40 * 6368775 * 2
def baseEnd_6368775 : Nat := 3270242755338424872223043

theorem tailTrace_6368775 : CollatzResearch.WordTrace tailWord_6368775 prefixEnd_6368775 3270242755338424872223043 := by
  unfold tailWord_6368775
  simp only [CollatzResearch.WordTrace]
  refine ⟨232288307502023350018875779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154858871668015566679250519 232288307502023350018875779)
  ·
    refine ⟨348432461253035025028313669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232288307502023350018875779 348432461253035025028313669)
    ·
      refine ⟨65331086484944067192808813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348432461253035025028313669 65331086484944067192808813)
      ·
        refine ⟨24499157431854025197303305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65331086484944067192808813 24499157431854025197303305)
        ·
          refine ⟨18374368073890518897977479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24499157431854025197303305 18374368073890518897977479)
          ·
            refine ⟨27561552110835778346966219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18374368073890518897977479 27561552110835778346966219)
            ·
              refine ⟨41342328166253667520449329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27561552110835778346966219 41342328166253667520449329)
              ·
                refine ⟨31006746124690250640336997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41342328166253667520449329 31006746124690250640336997)
                ·
                  refine ⟨5813764898379421995063187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31006746124690250640336997 5813764898379421995063187)
                  ·
                    refine ⟨8720647347569132992594781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5813764898379421995063187 8720647347569132992594781)
                    ·
                      refine ⟨3270242755338424872223043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720647347569132992594781 3270242755338424872223043)
                      ·
                        rfl

theorem cell23_6368775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6368775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368775 prefixEnd_6368775 := by exact prefixLift 6368775
  have htrace : WordTrace (prefixWord ++ tailWord_6368775) baseStart_6368775 baseEnd_6368775 := by
    simpa [prefixWord, tailWord_6368775, baseEnd_6368775] using wordTrace_append hprefix tailTrace_6368775
  have hstable : (prefixWord ++ tailWord_6368775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368775).length < 2 ^ (prefixWord ++ tailWord_6368775).sum := by decide
  have hdescent : baseEnd_6368775 < baseStart_6368775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368785 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_6368785 : Nat := 118140960795 + 6368785 * 2 ^ 59
def prefixEnd_6368785 : Nat := 4983230072969 + 3 ^ 40 * 6368785 * 2
def baseEnd_6368785 : Nat := 3270247890144969833097997

theorem tailTrace_6368785 : CollatzResearch.WordTrace tailWord_6368785 prefixEnd_6368785 3270247890144969833097997 := by
  unfold tailWord_6368785
  simp only [CollatzResearch.WordTrace]
  refine ⟨232288672231987121726739809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154859114821324747817826539 232288672231987121726739809)
  ·
    refine ⟨174216504173990341295054857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232288672231987121726739809 174216504173990341295054857)
    ·
      refine ⟨130662378130492755971291143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174216504173990341295054857 130662378130492755971291143)
      ·
        refine ⟨195993567195739133956936715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130662378130492755971291143 195993567195739133956936715)
        ·
          refine ⟨293990350793608700935405073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195993567195739133956936715 293990350793608700935405073)
          ·
            refine ⟨220492763095206525701553805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293990350793608700935405073 220492763095206525701553805)
            ·
              refine ⟨82684786160702447138082677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220492763095206525701553805 82684786160702447138082677)
              ·
                refine ⟨7751698702565854419195251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82684786160702447138082677 7751698702565854419195251)
                ·
                  refine ⟨11627548053848781628792877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751698702565854419195251 11627548053848781628792877)
                  ·
                    refine ⟨4360330520193293110797329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11627548053848781628792877 4360330520193293110797329)
                    ·
                      refine ⟨3270247890144969833097997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360330520193293110797329 3270247890144969833097997)
                      ·
                        rfl

theorem cell23_6368785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_6368785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368785 prefixEnd_6368785 := by exact prefixLift 6368785
  have htrace : WordTrace (prefixWord ++ tailWord_6368785) baseStart_6368785 baseEnd_6368785 := by
    simpa [prefixWord, tailWord_6368785, baseEnd_6368785] using wordTrace_append hprefix tailTrace_6368785
  have hstable : (prefixWord ++ tailWord_6368785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368785).length < 2 ^ (prefixWord ++ tailWord_6368785).sum := by decide
  have hdescent : baseEnd_6368785 < baseStart_6368785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368848 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_6368848 : Nat := 118140960795 + 6368848 * 2 ^ 59
def prefixEnd_6368848 : Nat := 4983230072969 + 3 ^ 40 * 6368848 * 2
def baseEnd_6368848 : Nat := 3270280239426203086610207

theorem tailTrace_6368848 : CollatzResearch.WordTrace tailWord_6368848 prefixEnd_6368848 3270280239426203086610207 := by
  unfold tailWord_6368848
  simp only [CollatzResearch.WordTrace]
  refine ⟨116145485015379441743141599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154860646687172588990855465 116145485015379441743141599)
  ·
    refine ⟨174218227523069162614712399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116145485015379441743141599 174218227523069162614712399)
    ·
      refine ⟨261327341284603743922068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174218227523069162614712399 261327341284603743922068599)
      ·
        refine ⟨391991011926905615883102899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261327341284603743922068599 391991011926905615883102899)
        ·
          refine ⟨587986517890358423824654349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391991011926905615883102899 587986517890358423824654349)
          ·
            refine ⟨220494944208884408934245381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587986517890358423824654349 220494944208884408934245381)
            ·
              refine ⟨41342802039165826675171009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220494944208884408934245381 41342802039165826675171009)
              ·
                refine ⟨31007101529374370006378257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41342802039165826675171009 31007101529374370006378257)
                ·
                  refine ⟨23255326147030777504783693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31007101529374370006378257 23255326147030777504783693)
                  ·
                    refine ⟨8720747305136541564293885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23255326147030777504783693 8720747305136541564293885)
                    ·
                      refine ⟨3270280239426203086610207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720747305136541564293885 3270280239426203086610207)
                      ·
                        rfl

theorem cell23_6368848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_6368848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368848 prefixEnd_6368848 := by exact prefixLift 6368848
  have htrace : WordTrace (prefixWord ++ tailWord_6368848) baseStart_6368848 baseEnd_6368848 := by
    simpa [prefixWord, tailWord_6368848, baseEnd_6368848] using wordTrace_append hprefix tailTrace_6368848
  have hstable : (prefixWord ++ tailWord_6368848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368848).length < 2 ^ (prefixWord ++ tailWord_6368848).sum := by decide
  have hdescent : baseEnd_6368848 < baseStart_6368848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368855 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 5]
def baseStart_6368855 : Nat := 118140960795 + 6368855 * 2 ^ 59
def prefixEnd_6368855 : Nat := 4983230072969 + 3 ^ 40 * 6368855 * 2
def baseEnd_6368855 : Nat := 363364870421198284358075

theorem tailTrace_6368855 : CollatzResearch.WordTrace tailWord_6368855 prefixEnd_6368855 363364870421198284358075 := by
  unfold tailWord_6368855
  simp only [CollatzResearch.WordTrace]
  refine ⟨232291225341733523681788019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154860816894489015787858679 232291225341733523681788019)
  ·
    refine ⟨348436838012600285522682029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232291225341733523681788019 348436838012600285522682029)
    ·
      refine ⟨130663814254725107071005761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348436838012600285522682029 130663814254725107071005761)
      ·
        refine ⟨97997860691043830303254321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130663814254725107071005761 97997860691043830303254321)
        ·
          refine ⟨73498395518282872727440741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97997860691043830303254321 73498395518282872727440741)
          ·
            refine ⟨13780949159678038636395139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73498395518282872727440741 13780949159678038636395139)
            ·
              refine ⟨20671423739517057954592709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13780949159678038636395139 20671423739517057954592709)
              ·
                refine ⟨3875891951159448366486133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20671423739517057954592709 3875891951159448366486133)
                ·
                  refine ⟨363364870421198284358075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875891951159448366486133 363364870421198284358075)
                  ·
                    rfl

theorem cell23_6368855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 5].length) (baseStart_6368855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368855 prefixEnd_6368855 := by exact prefixLift 6368855
  have htrace : WordTrace (prefixWord ++ tailWord_6368855) baseStart_6368855 baseEnd_6368855 := by
    simpa [prefixWord, tailWord_6368855, baseEnd_6368855] using wordTrace_append hprefix tailTrace_6368855
  have hstable : (prefixWord ++ tailWord_6368855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368855).length < 2 ^ (prefixWord ++ tailWord_6368855).sum := by decide
  have hdescent : baseEnd_6368855 < baseStart_6368855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368885 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6368885 : Nat := 118140960795 + 6368885 * 2 ^ 59
def prefixEnd_6368885 : Nat := 4983230072969 + 3 ^ 40 * 6368885 * 2
def baseEnd_6368885 : Nat := 1090099746070139813949179

theorem tailTrace_6368885 : CollatzResearch.WordTrace tailWord_6368885 prefixEnd_6368885 1090099746070139813949179 := by
  unfold tailWord_6368885
  simp only [CollatzResearch.WordTrace]
  refine ⟨232292319531624838805380109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154861546354416559203586739 232292319531624838805380109)
  ·
    refine ⟨87109619824359314552017541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232292319531624838805380109 87109619824359314552017541)
    ·
      refine ⟨16333053717067371478503289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87109619824359314552017541 16333053717067371478503289)
      ·
        refine ⟨12249790287800528608877467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16333053717067371478503289 12249790287800528608877467)
        ·
          refine ⟨18374685431700792913316201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249790287800528608877467 18374685431700792913316201)
          ·
            refine ⟨13781014073775594684987151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18374685431700792913316201 13781014073775594684987151)
            ·
              refine ⟨20671521110663392027480727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13781014073775594684987151 20671521110663392027480727)
              ·
                refine ⟨31007281665995088041221091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20671521110663392027480727 31007281665995088041221091)
                ·
                  refine ⟨46510922498992632061831637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31007281665995088041221091 46510922498992632061831637)
                  ·
                    refine ⟨1090099746070139813949179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46510922498992632061831637 1090099746070139813949179)
                    ·
                      rfl

theorem cell23_6368885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6368885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368885 prefixEnd_6368885 := by exact prefixLift 6368885
  have htrace : WordTrace (prefixWord ++ tailWord_6368885) baseStart_6368885 baseEnd_6368885 := by
    simpa [prefixWord, tailWord_6368885, baseEnd_6368885] using wordTrace_append hprefix tailTrace_6368885
  have hstable : (prefixWord ++ tailWord_6368885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368885).length < 2 ^ (prefixWord ++ tailWord_6368885).sum := by decide
  have hdescent : baseEnd_6368885 < baseStart_6368885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368905 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 4, 2]
def baseStart_6368905 : Nat := 118140960795 + 6368905 * 2 ^ 59
def prefixEnd_6368905 : Nat := 4983230072969 + 3 ^ 40 * 6368905 * 2
def baseEnd_6368905 : Nat := 3270309507823509363597445

theorem tailTrace_6368905 : CollatzResearch.WordTrace tailWord_6368905 prefixEnd_6368905 3270309507823509363597445 := by
  unfold tailWord_6368905
  simp only [CollatzResearch.WordTrace]
  refine ⟨232293048991552382221108169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154862032661034921480738779 232293048991552382221108169)
  ·
    refine ⟨174219786743664286665831127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232293048991552382221108169 174219786743664286665831127)
    ·
      refine ⟨261329680115496429998746691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174219786743664286665831127 261329680115496429998746691)
      ·
        refine ⟨391994520173244644998120037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261329680115496429998746691 391994520173244644998120037)
        ·
          refine ⟨73498972532483370937147507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391994520173244644998120037 73498972532483370937147507)
          ·
            refine ⟨110248458798725056405721261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73498972532483370937147507 110248458798725056405721261)
            ·
              refine ⟨41343172049521896152145473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110248458798725056405721261 41343172049521896152145473)
              ·
                refine ⟨31007379037141422114109105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41343172049521896152145473 31007379037141422114109105)
                ·
                  refine ⟨23255534277856066585581829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31007379037141422114109105 23255534277856066585581829)
                  ·
                    refine ⟨4360412677098012484796593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23255534277856066585581829 4360412677098012484796593)
                    ·
                      refine ⟨3270309507823509363597445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360412677098012484796593 3270309507823509363597445)
                      ·
                        rfl

theorem cell23_6368905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4, 2].length) (baseStart_6368905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368905 prefixEnd_6368905 := by exact prefixLift 6368905
  have htrace : WordTrace (prefixWord ++ tailWord_6368905) baseStart_6368905 baseEnd_6368905 := by
    simpa [prefixWord, tailWord_6368905, baseEnd_6368905] using wordTrace_append hprefix tailTrace_6368905
  have hstable : (prefixWord ++ tailWord_6368905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368905).length < 2 ^ (prefixWord ++ tailWord_6368905).sum := by decide
  have hdescent : baseEnd_6368905 < baseStart_6368905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368955 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 3]
def baseStart_6368955 : Nat := 118140960795 + 6368955 * 2 ^ 59
def prefixEnd_6368955 : Nat := 4983230072969 + 3 ^ 40 * 6368955 * 2
def baseEnd_6368955 : Nat := 3270335181856234167972215

theorem tailTrace_6368955 : CollatzResearch.WordTrace tailWord_6368955 prefixEnd_6368955 3270335181856234167972215 := by
  unfold tailWord_6368955
  simp only [CollatzResearch.WordTrace]
  refine ⟨232294872641371240760428319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154863248427580827173618879 232294872641371240760428319)
  ·
    refine ⟨348442308962056861140642479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232294872641371240760428319 348442308962056861140642479)
    ·
      refine ⟨522663463443085291710963719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348442308962056861140642479 522663463443085291710963719)
      ·
        refine ⟨783995195164627937566445579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522663463443085291710963719 783995195164627937566445579)
        ·
          refine ⟨1175992792746941906349668369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783995195164627937566445579 1175992792746941906349668369)
          ·
            refine ⟨881994594560206429762251277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175992792746941906349668369 881994594560206429762251277)
            ·
              refine ⟨330747972960077411160844229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881994594560206429762251277 330747972960077411160844229)
              ·
                refine ⟨62015244930014514592658293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330747972960077411160844229 62015244930014514592658293)
                ·
                  refine ⟨5813929212188860743061715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62015244930014514592658293 5813929212188860743061715)
                  ·
                    refine ⟨8720893818283291114592573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5813929212188860743061715 8720893818283291114592573)
                    ·
                      refine ⟨3270335181856234167972215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8720893818283291114592573 3270335181856234167972215)
                      ·
                        rfl

theorem cell23_6368955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 3].length) (baseStart_6368955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368955 prefixEnd_6368955 := by exact prefixLift 6368955
  have htrace : WordTrace (prefixWord ++ tailWord_6368955) baseStart_6368955 baseEnd_6368955 := by
    simpa [prefixWord, tailWord_6368955, baseEnd_6368955] using wordTrace_append hprefix tailTrace_6368955
  have hstable : (prefixWord ++ tailWord_6368955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368955).length < 2 ^ (prefixWord ++ tailWord_6368955).sum := by decide
  have hdescent : baseEnd_6368955 < baseStart_6368955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6368966 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6368966 : Nat := 118140960795 + 6368966 * 2 ^ 59
def prefixEnd_6368966 : Nat := 4983230072969 + 3 ^ 40 * 6368966 * 2
def baseEnd_6368966 : Nat := 1090113610047811208311555

theorem tailTrace_6368966 : CollatzResearch.WordTrace tailWord_6368966 prefixEnd_6368966 1090113610047811208311555 := by
  unfold tailWord_6368966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259227307635355926221211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154863515896220926426052501 7259227307635355926221211)
  ·
    refine ⟨10888840961453033889331817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259227307635355926221211 10888840961453033889331817)
    ·
      refine ⟨8166630721089775416998863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10888840961453033889331817 8166630721089775416998863)
      ·
        refine ⟨12249946081634663125498295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166630721089775416998863 12249946081634663125498295)
        ·
          refine ⟨18374919122451994688247443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249946081634663125498295 18374919122451994688247443)
          ·
            refine ⟨27562378683677992032371165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18374919122451994688247443 27562378683677992032371165)
            ·
              refine ⟨10335892006379247012139187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27562378683677992032371165 10335892006379247012139187)
              ·
                refine ⟨15503838009568870518208781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335892006379247012139187 15503838009568870518208781)
                ·
                  refine ⟨5813939253588326444328293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15503838009568870518208781 5813939253588326444328293)
                  ·
                    refine ⟨1090113610047811208311555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813939253588326444328293 1090113610047811208311555)
                    ·
                      rfl

theorem cell23_6368966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6368966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6368966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6368966 prefixEnd_6368966 := by exact prefixLift 6368966
  have htrace : WordTrace (prefixWord ++ tailWord_6368966) baseStart_6368966 baseEnd_6368966 := by
    simpa [prefixWord, tailWord_6368966, baseEnd_6368966] using wordTrace_append hprefix tailTrace_6368966
  have hstable : (prefixWord ++ tailWord_6368966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6368966).length < 2 ^ (prefixWord ++ tailWord_6368966).sum := by decide
  have hdescent : baseEnd_6368966 < baseStart_6368966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6368966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369005 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_6369005 : Nat := 118140960795 + 6369005 * 2 ^ 59
def prefixEnd_6369005 : Nat := 4983230072969 + 3 ^ 40 * 6369005 * 2
def baseEnd_6369005 : Nat := 1090120285296319657448995

theorem tailTrace_6369005 : CollatzResearch.WordTrace tailWord_6369005 prefixEnd_6369005 1090120285296319657448995 := by
  unfold tailWord_6369005
  simp only [CollatzResearch.WordTrace]
  refine ⟨232296696291190099299748469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154864464194126732866498979 232296696291190099299748469)
  ·
    refine ⟨21777815277299071809351419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232296696291190099299748469 21777815277299071809351419)
    ·
      refine ⟨32666722915948607714027129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21777815277299071809351419 32666722915948607714027129)
      ·
        refine ⟨24500042186961455785520347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32666722915948607714027129 24500042186961455785520347)
        ·
          refine ⟨36750063280442183678280521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24500042186961455785520347 36750063280442183678280521)
          ·
            refine ⟨27562547460331637758710391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36750063280442183678280521 27562547460331637758710391)
            ·
              refine ⟨41343821190497456638065587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27562547460331637758710391 41343821190497456638065587)
              ·
                refine ⟨62015731785746184957098381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41343821190497456638065587 62015731785746184957098381)
                ·
                  refine ⟨23255899419654819358911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62015731785746184957098381 23255899419654819358911893)
                  ·
                    refine ⟨1090120285296319657448995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23255899419654819358911893 1090120285296319657448995)
                    ·
                      rfl

theorem cell23_6369005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_6369005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369005 prefixEnd_6369005 := by exact prefixLift 6369005
  have htrace : WordTrace (prefixWord ++ tailWord_6369005) baseStart_6369005 baseEnd_6369005 := by
    simpa [prefixWord, tailWord_6369005, baseEnd_6369005] using wordTrace_append hprefix tailTrace_6369005
  have hstable : (prefixWord ++ tailWord_6369005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369005).length < 2 ^ (prefixWord ++ tailWord_6369005).sum := by decide
  have hdescent : baseEnd_6369005 < baseStart_6369005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369008 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_6369008 : Nat := 118140960795 + 6369008 * 2 ^ 59
def prefixEnd_6369008 : Nat := 4983230072969 + 3 ^ 40 * 6369008 * 2
def baseEnd_6369008 : Nat := 3270362396330922460609471

theorem tailTrace_6369008 : CollatzResearch.WordTrace tailWord_6369008 prefixEnd_6369008 3270362396330922460609471 := by
  unfold tailWord_6369008
  simp only [CollatzResearch.WordTrace]
  refine ⟨116148402855089615406053839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154864537140119487208071785 116148402855089615406053839)
  ·
    refine ⟨174222604282634423109080759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116148402855089615406053839 174222604282634423109080759)
    ·
      refine ⟨261333906423951634663621139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174222604282634423109080759 261333906423951634663621139)
      ·
        refine ⟨392000859635927451995431709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261333906423951634663621139 392000859635927451995431709)
        ·
          refine ⟨147000322363472794498286891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392000859635927451995431709 147000322363472794498286891)
          ·
            refine ⟨220500483545209191747430337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147000322363472794498286891 220500483545209191747430337)
            ·
              refine ⟨165375362658906893810572753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220500483545209191747430337 165375362658906893810572753)
              ·
                refine ⟨124031521994180170357929565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165375362658906893810572753 124031521994180170357929565)
                ·
                  refine ⟨46511820747817563884223587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124031521994180170357929565 46511820747817563884223587)
                  ·
                    refine ⟨69767731121726345826335381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46511820747817563884223587 69767731121726345826335381)
                    ·
                      refine ⟨3270362396330922460609471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69767731121726345826335381 3270362396330922460609471)
                      ·
                        rfl

theorem cell23_6369008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_6369008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369008 prefixEnd_6369008 := by exact prefixLift 6369008
  have htrace : WordTrace (prefixWord ++ tailWord_6369008) baseStart_6369008 baseEnd_6369008 := by
    simpa [prefixWord, tailWord_6369008, baseEnd_6369008] using wordTrace_append hprefix tailTrace_6369008
  have hstable : (prefixWord ++ tailWord_6369008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369008).length < 2 ^ (prefixWord ++ tailWord_6369008).sum := by decide
  have hdescent : baseEnd_6369008 < baseStart_6369008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369015 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_6369015 : Nat := 118140960795 + 6369015 * 2 ^ 59
def prefixEnd_6369015 : Nat := 4983230072969 + 3 ^ 40 * 6369015 * 2
def baseEnd_6369015 : Nat := 3270365990695503933221939

theorem tailTrace_6369015 : CollatzResearch.WordTrace tailWord_6369015 prefixEnd_6369015 3270365990695503933221939 := by
  unfold tailWord_6369015
  simp only [CollatzResearch.WordTrace]
  refine ⟨232297061021153871007612499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154864707347435914005074999 232297061021153871007612499)
  ·
    refine ⟨348445591531730806511418749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232297061021153871007612499 348445591531730806511418749)
    ·
      refine ⟨130667096824399052441782031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348445591531730806511418749 130667096824399052441782031)
      ·
        refine ⟨196000645236598578662673047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130667096824399052441782031 196000645236598578662673047)
        ·
          refine ⟨294000967854897867994009571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196000645236598578662673047 294000967854897867994009571)
          ·
            refine ⟨441001451782346801991014357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294000967854897867994009571 441001451782346801991014357)
            ·
              refine ⟨10335971526148753171664399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 441001451782346801991014357 10335971526148753171664399)
              ·
                refine ⟨15503957289223129757496599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335971526148753171664399 15503957289223129757496599)
                ·
                  refine ⟨23255935933834694636244899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15503957289223129757496599 23255935933834694636244899)
                  ·
                    refine ⟨34883903900752041954367349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23255935933834694636244899 34883903900752041954367349)
                    ·
                      refine ⟨3270365990695503933221939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34883903900752041954367349 3270365990695503933221939)
                      ·
                        rfl

theorem cell23_6369015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_6369015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369015 prefixEnd_6369015 := by exact prefixLift 6369015
  have htrace : WordTrace (prefixWord ++ tailWord_6369015) baseStart_6369015 baseEnd_6369015 := by
    simpa [prefixWord, tailWord_6369015, baseEnd_6369015] using wordTrace_append hprefix tailTrace_6369015
  have hstable : (prefixWord ++ tailWord_6369015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369015).length < 2 ^ (prefixWord ++ tailWord_6369015).sum := by decide
  have hdescent : baseEnd_6369015 < baseStart_6369015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369095 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 6]
def baseStart_6369095 : Nat := 118140960795 + 6369095 * 2 ^ 59
def prefixEnd_6369095 : Nat := 4983230072969 + 3 ^ 40 * 6369095 * 2
def baseEnd_6369095 : Nat := 1090135689715954540073857

theorem tailTrace_6369095 : CollatzResearch.WordTrace tailWord_6369095 prefixEnd_6369095 1090135689715954540073857 := by
  unfold tailWord_6369095
  simp only [CollatzResearch.WordTrace]
  refine ⟨232299978860864044670524739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154866652573909363113683159 232299978860864044670524739)
  ·
    refine ⟨348449968291296067005787109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232299978860864044670524739 348449968291296067005787109)
    ·
      refine ⟨65334369054618012563585083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348449968291296067005787109 65334369054618012563585083)
      ·
        refine ⟨98001553581927018845377625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65334369054618012563585083 98001553581927018845377625)
        ·
          refine ⟨73501165186445264134033219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98001553581927018845377625 73501165186445264134033219)
          ·
            refine ⟨110251747779667896201049829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73501165186445264134033219 110251747779667896201049829)
            ·
              refine ⟨20672202708687730537696843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110251747779667896201049829 20672202708687730537696843)
              ·
                refine ⟨31008304063031595806545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20672202708687730537696843 31008304063031595806545265)
                ·
                  refine ⟨23256228047273696854908949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31008304063031595806545265 23256228047273696854908949)
                  ·
                    refine ⟨1090135689715954540073857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23256228047273696854908949 1090135689715954540073857)
                    ·
                      rfl

theorem cell23_6369095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_6369095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369095 prefixEnd_6369095 := by exact prefixLift 6369095
  have htrace : WordTrace (prefixWord ++ tailWord_6369095) baseStart_6369095 baseEnd_6369095 := by
    simpa [prefixWord, tailWord_6369095, baseEnd_6369095] using wordTrace_append hprefix tailTrace_6369095
  have hstable : (prefixWord ++ tailWord_6369095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369095).length < 2 ^ (prefixWord ++ tailWord_6369095).sum := by decide
  have hdescent : baseEnd_6369095 < baseStart_6369095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369096 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_6369096 : Nat := 118140960795 + 6369096 * 2 ^ 59
def prefixEnd_6369096 : Nat := 4983230072969 + 3 ^ 40 * 6369096 * 2
def baseEnd_6369096 : Nat := 3270407582628518116309067

theorem tailTrace_6369096 : CollatzResearch.WordTrace tailWord_6369096 prefixEnd_6369096 3270407582628518116309067 := by
  unfold tailWord_6369096
  simp only [CollatzResearch.WordTrace]
  refine ⟨116150007666930210920655571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154866676889240281227540761 116150007666930210920655571)
  ·
    refine ⟨174225011500395316380983357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116150007666930210920655571 174225011500395316380983357)
    ·
      refine ⟨65334379312648243642868759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174225011500395316380983357 65334379312648243642868759)
      ·
        refine ⟨98001568968972365464303139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65334379312648243642868759 98001568968972365464303139)
        ·
          refine ⟨147002353453458548196454709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98001568968972365464303139 147002353453458548196454709)
          ·
            refine ⟨13781470636261738893417629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147002353453458548196454709 13781470636261738893417629)
            ·
              refine ⟨5168051488598152085031611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13781470636261738893417629 5168051488598152085031611)
              ·
                refine ⟨7752077232897228127547417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168051488598152085031611 7752077232897228127547417)
                ·
                  refine ⟨5814057924672921095660563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7752077232897228127547417 5814057924672921095660563)
                  ·
                    refine ⟨8721086887009381643490845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5814057924672921095660563 8721086887009381643490845)
                    ·
                      refine ⟨3270407582628518116309067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721086887009381643490845 3270407582628518116309067)
                      ·
                        rfl

theorem cell23_6369096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_6369096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369096 prefixEnd_6369096 := by exact prefixLift 6369096
  have htrace : WordTrace (prefixWord ++ tailWord_6369096) baseStart_6369096 baseEnd_6369096 := by
    simpa [prefixWord, tailWord_6369096, baseEnd_6369096] using wordTrace_append hprefix tailTrace_6369096
  have hstable : (prefixWord ++ tailWord_6369096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369096).length < 2 ^ (prefixWord ++ tailWord_6369096).sum := by decide
  have hdescent : baseEnd_6369096 < baseStart_6369096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369106 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_6369106 : Nat := 118140960795 + 6369106 * 2 ^ 59
def prefixEnd_6369106 : Nat := 4983230072969 + 3 ^ 40 * 6369106 * 2
def baseEnd_6369106 : Nat := 3270412717435063077184021

theorem tailTrace_6369106 : CollatzResearch.WordTrace tailWord_6369106 prefixEnd_6369106 3270412717435063077184021 := by
  unfold tailWord_6369106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075095015956048387293793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154866920042549462366116781 58075095015956048387293793)
  ·
    refine ⟨43556321261967036290470345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58075095015956048387293793 43556321261967036290470345)
    ·
      refine ⟨32667240946475277217852759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43556321261967036290470345 32667240946475277217852759)
      ·
        refine ⟨49000861419712915826779139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32667240946475277217852759 49000861419712915826779139)
        ·
          refine ⟨73501292129569373740168709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49000861419712915826779139 73501292129569373740168709)
          ·
            refine ⟨13781492274294257576281633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73501292129569373740168709 13781492274294257576281633)
            ·
              refine ⟨10336119205720693182211225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13781492274294257576281633 10336119205720693182211225)
              ·
                refine ⟨7752089404290519886658419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10336119205720693182211225 7752089404290519886658419)
                ·
                  refine ⟨11628134106435779829987629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752089404290519886658419 11628134106435779829987629)
                  ·
                    refine ⟨4360550289913417436245361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11628134106435779829987629 4360550289913417436245361)
                    ·
                      refine ⟨3270412717435063077184021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360550289913417436245361 3270412717435063077184021)
                      ·
                        rfl

theorem cell23_6369106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_6369106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369106 prefixEnd_6369106 := by exact prefixLift 6369106
  have htrace : WordTrace (prefixWord ++ tailWord_6369106) baseStart_6369106 baseEnd_6369106 := by
    simpa [prefixWord, tailWord_6369106, baseEnd_6369106] using wordTrace_append hprefix tailTrace_6369106
  have hstable : (prefixWord ++ tailWord_6369106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369106).length < 2 ^ (prefixWord ++ tailWord_6369106).sum := by decide
  have hdescent : baseEnd_6369106 < baseStart_6369106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369119 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 4, 2, 2]
def baseStart_6369119 : Nat := 118140960795 + 6369119 * 2 ^ 59
def prefixEnd_6369119 : Nat := 4983230072969 + 3 ^ 40 * 6369119 * 2
def baseEnd_6369119 : Nat := 3270419392683571526321461

theorem tailTrace_6369119 : CollatzResearch.WordTrace tailWord_6369119 prefixEnd_6369119 3270419392683571526321461 := by
  unfold tailWord_6369119
  simp only [CollatzResearch.WordTrace]
  refine ⟨232300854212777096769398411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154867236141851397846265607 232300854212777096769398411)
  ·
    refine ⟨348451281319165645154097617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232300854212777096769398411 348451281319165645154097617)
    ·
      refine ⟨261338460989374233865573213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348451281319165645154097617 261338460989374233865573213)
      ·
        refine ⟨98001922871015337699589955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261338460989374233865573213 98001922871015337699589955)
        ·
          refine ⟨147002884306523006549384933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98001922871015337699589955 147002884306523006549384933)
          ·
            refine ⟨27563040807473063728009675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147002884306523006549384933 27563040807473063728009675)
            ·
              refine ⟨41344561211209595592014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27563040807473063728009675 41344561211209595592014513)
              ·
                refine ⟨31008420908407196694010885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41344561211209595592014513 31008420908407196694010885)
                ·
                  refine ⟨5814078920326349380127041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31008420908407196694010885 5814078920326349380127041)
                  ·
                    refine ⟨4360559190244762035095281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814078920326349380127041 4360559190244762035095281)
                    ·
                      refine ⟨3270419392683571526321461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360559190244762035095281 3270419392683571526321461)
                      ·
                        rfl

theorem cell23_6369119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_6369119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369119 prefixEnd_6369119 := by exact prefixLift 6369119
  have htrace : WordTrace (prefixWord ++ tailWord_6369119) baseStart_6369119 baseEnd_6369119 := by
    simpa [prefixWord, tailWord_6369119, baseEnd_6369119] using wordTrace_append hprefix tailTrace_6369119
  have hstable : (prefixWord ++ tailWord_6369119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369119).length < 2 ^ (prefixWord ++ tailWord_6369119).sum := by decide
  have hdescent : baseEnd_6369119 < baseStart_6369119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369122 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6369122 : Nat := 118140960795 + 6369122 * 2 ^ 59
def prefixEnd_6369122 : Nat := 4983230072969 + 3 ^ 40 * 6369122 * 2
def baseEnd_6369122 : Nat := 3270420933125535014583947

theorem tailTrace_6369122 : CollatzResearch.WordTrace tailWord_6369122 prefixEnd_6369122 3270420933125535014583947 := by
  unfold tailWord_6369122
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075240907941557070439405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154867309087844152187838413 58075240907941557070439405)
  ·
    refine ⟨21778215340478083901414777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58075240907941557070439405 21778215340478083901414777)
    ·
      refine ⟨16333661505358562926061083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21778215340478083901414777 16333661505358562926061083)
      ·
        refine ⟨24500492258037844389091625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16333661505358562926061083 24500492258037844389091625)
        ·
          refine ⟨18375369193528383291818719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24500492258037844389091625 18375369193528383291818719)
          ·
            refine ⟨27563053790292574937728079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18375369193528383291818719 27563053790292574937728079)
            ·
              refine ⟨41344580685438862406592119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27563053790292574937728079 41344580685438862406592119)
              ·
                refine ⟨62016871028158293609888179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41344580685438862406592119 62016871028158293609888179)
                ·
                  refine ⟨93025306542237440414832269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62016871028158293609888179 93025306542237440414832269)
                  ·
                    refine ⟨34884489953339040155562101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93025306542237440414832269 34884489953339040155562101)
                    ·
                      refine ⟨3270420933125535014583947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34884489953339040155562101 3270420933125535014583947)
                      ·
                        rfl

theorem cell23_6369122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6369122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369122 prefixEnd_6369122 := by exact prefixLift 6369122
  have htrace : WordTrace (prefixWord ++ tailWord_6369122) baseStart_6369122 baseEnd_6369122 := by
    simpa [prefixWord, tailWord_6369122, baseEnd_6369122] using wordTrace_append hprefix tailTrace_6369122
  have hstable : (prefixWord ++ tailWord_6369122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369122).length < 2 ^ (prefixWord ++ tailWord_6369122).sum := by decide
  have hdescent : baseEnd_6369122 < baseStart_6369122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369202 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_6369202 : Nat := 118140960795 + 6369202 * 2 ^ 59
def prefixEnd_6369202 : Nat := 4983230072969 + 3 ^ 40 * 6369202 * 2
def baseEnd_6369202 : Nat := 1090154003859298233861193

theorem tailTrace_6369202 : CollatzResearch.WordTrace tailWord_6369202 prefixEnd_6369202 1090154003859298233861193 := by
  unfold tailWord_6369202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075970367869100486167465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154869254314317601296446573 58075970367869100486167465)
  ·
    refine ⟨43556977775901825364625599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58075970367869100486167465 43556977775901825364625599)
    ·
      refine ⟨65335466663852738046938399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43556977775901825364625599 65335466663852738046938399)
      ·
        refine ⟨98003199995779107070407599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65335466663852738046938399 98003199995779107070407599)
        ·
          refine ⟨147004799993668660605611399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98003199995779107070407599 147004799993668660605611399)
          ·
            refine ⟨220507199990502990908417099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147004799993668660605611399 220507199990502990908417099)
            ·
              refine ⟨330760799985754486362625649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220507199990502990908417099 330760799985754486362625649)
              ·
                refine ⟨248070599989315864771969237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330760799985754486362625649 248070599989315864771969237)
                ·
                  refine ⟨5814154687249590580593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 248070599989315864771969237 5814154687249590580593029)
                  ·
                    refine ⟨1090154003859298233861193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814154687249590580593029 1090154003859298233861193)
                    ·
                      rfl

theorem cell23_6369202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_6369202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369202 prefixEnd_6369202 := by exact prefixLift 6369202
  have htrace : WordTrace (prefixWord ++ tailWord_6369202) baseStart_6369202 baseEnd_6369202 := by
    simpa [prefixWord, tailWord_6369202, baseEnd_6369202] using wordTrace_append hprefix tailTrace_6369202
  have hstable : (prefixWord ++ tailWord_6369202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369202).length < 2 ^ (prefixWord ++ tailWord_6369202).sum := by decide
  have hdescent : baseEnd_6369202 < baseStart_6369202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369209 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6369209 : Nat := 118140960795 + 6369209 * 2 ^ 59
def prefixEnd_6369209 : Nat := 4983230072969 + 3 ^ 40 * 6369209 * 2
def baseEnd_6369209 : Nat := 3270465605942476174196047

theorem tailTrace_6369209 : CollatzResearch.WordTrace tailWord_6369209 prefixEnd_6369209 3270465605942476174196047 := by
  unfold tailWord_6369209
  simp only [CollatzResearch.WordTrace]
  refine ⟨232304136782451042140174681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154869424521634028093449787 232304136782451042140174681)
  ·
    refine ⟨174228102586838281605131011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232304136782451042140174681 174228102586838281605131011)
    ·
      refine ⟨261342153880257422407696517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174228102586838281605131011 261342153880257422407696517)
      ·
        refine ⟨49001653852548266701443097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261342153880257422407696517 49001653852548266701443097)
        ·
          refine ⟨36751240389411200026082323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49001653852548266701443097 36751240389411200026082323)
          ·
            refine ⟨55126860584116800039123485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36751240389411200026082323 55126860584116800039123485)
            ·
              refine ⟨20672572719043800014671307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55126860584116800039123485 20672572719043800014671307)
              ·
                refine ⟨31008859078565700022006961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20672572719043800014671307 31008859078565700022006961)
                ·
                  refine ⟨23256644308924275016505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31008859078565700022006961 23256644308924275016505221)
                  ·
                    refine ⟨4360620807923301565594729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23256644308924275016505221 4360620807923301565594729)
                    ·
                      refine ⟨3270465605942476174196047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360620807923301565594729 3270465605942476174196047)
                      ·
                        rfl

theorem cell23_6369209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6369209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369209 prefixEnd_6369209 := by exact prefixLift 6369209
  have htrace : WordTrace (prefixWord ++ tailWord_6369209) baseStart_6369209 baseEnd_6369209 := by
    simpa [prefixWord, tailWord_6369209, baseEnd_6369209] using wordTrace_append hprefix tailTrace_6369209
  have hstable : (prefixWord ++ tailWord_6369209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369209).length < 2 ^ (prefixWord ++ tailWord_6369209).sum := by decide
  have hdescent : baseEnd_6369209 < baseStart_6369209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369292 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_6369292 : Nat := 118140960795 + 6369292 * 2 ^ 59
def prefixEnd_6369292 : Nat := 4983230072969 + 3 ^ 40 * 6369292 * 2
def baseEnd_6369292 : Nat := 1090169408278933116486055

theorem tailTrace_6369292 : CollatzResearch.WordTrace tailWord_6369292 prefixEnd_6369292 1090169408278933116486055 := by
  unfold tailWord_6369292
  simp only [CollatzResearch.WordTrace]
  refine ⟨116153582020575173657723065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154871442694100231543630753 116153582020575173657723065)
  ·
    refine ⟨87115186515431380243292299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116153582020575173657723065 87115186515431380243292299)
    ·
      refine ⟨130672779773147070364938449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87115186515431380243292299 130672779773147070364938449)
      ·
        refine ⟨98004584829860302773703837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130672779773147070364938449 98004584829860302773703837)
        ·
          refine ⟨36751719311197613540138939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98004584829860302773703837 36751719311197613540138939)
          ·
            refine ⟨55127578966796420310208409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36751719311197613540138939 55127578966796420310208409)
            ·
              refine ⟨41345684225097315232656307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55127578966796420310208409 41345684225097315232656307)
              ·
                refine ⟨62018526337645972848984461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41345684225097315232656307 62018526337645972848984461)
                ·
                  refine ⟨23256947376617239818369173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62018526337645972848984461 23256947376617239818369173)
                  ·
                    refine ⟨1090169408278933116486055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23256947376617239818369173 1090169408278933116486055)
                    ·
                      rfl

theorem cell23_6369292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_6369292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369292 prefixEnd_6369292 := by exact prefixLift 6369292
  have htrace : WordTrace (prefixWord ++ tailWord_6369292) baseStart_6369292 baseEnd_6369292 := by
    simpa [prefixWord, tailWord_6369292, baseEnd_6369292] using wordTrace_append hprefix tailTrace_6369292
  have hstable : (prefixWord ++ tailWord_6369292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369292).length < 2 ^ (prefixWord ++ tailWord_6369292).sum := by decide
  have hdescent : baseEnd_6369292 < baseStart_6369292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369299 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 4]
def baseStart_6369299 : Nat := 118140960795 + 6369299 * 2 ^ 59
def prefixEnd_6369299 : Nat := 4983230072969 + 3 ^ 40 * 6369299 * 2
def baseEnd_6369299 : Nat := 3270511819201380822070633

theorem tailTrace_6369299 : CollatzResearch.WordTrace tailWord_6369299 prefixEnd_6369299 3270511819201380822070633 := by
  unfold tailWord_6369299
  simp only [CollatzResearch.WordTrace]
  refine ⟨232307419352124987510950951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154871612901416658340633967 232307419352124987510950951)
  ·
    refine ⟨348461129028187481266426427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232307419352124987510950951 348461129028187481266426427)
    ·
      refine ⟨522691693542281221899639641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348461129028187481266426427 522691693542281221899639641)
      ·
        refine ⟨392018770156710916424729731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522691693542281221899639641 392018770156710916424729731)
        ·
          refine ⟨588028155235066374637094597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392018770156710916424729731 588028155235066374637094597)
          ·
            refine ⟨110255279106574945244455237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 588028155235066374637094597 110255279106574945244455237)
            ·
              refine ⟨20672864832482802233335357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110255279106574945244455237 20672864832482802233335357)
              ·
                refine ⟨7752324312181050837500759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20672864832482802233335357 7752324312181050837500759)
                ·
                  refine ⟨11628486468271576256251139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752324312181050837500759 11628486468271576256251139)
                  ·
                    refine ⟨17442729702407364384376709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11628486468271576256251139 17442729702407364384376709)
                    ·
                      refine ⟨3270511819201380822070633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17442729702407364384376709 3270511819201380822070633)
                      ·
                        rfl

theorem cell23_6369299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_6369299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369299 prefixEnd_6369299 := by exact prefixLift 6369299
  have htrace : WordTrace (prefixWord ++ tailWord_6369299) baseStart_6369299 baseEnd_6369299 := by
    simpa [prefixWord, tailWord_6369299, baseEnd_6369299] using wordTrace_append hprefix tailTrace_6369299
  have hstable : (prefixWord ++ tailWord_6369299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369299).length < 2 ^ (prefixWord ++ tailWord_6369299).sum := by decide
  have hdescent : baseEnd_6369299 < baseStart_6369299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369303 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6369303 : Nat := 118140960795 + 6369303 * 2 ^ 59
def prefixEnd_6369303 : Nat := 4983230072969 + 3 ^ 40 * 6369303 * 2
def baseEnd_6369303 : Nat := 3270513873123998806420615

theorem tailTrace_6369303 : CollatzResearch.WordTrace tailWord_6369303 prefixEnd_6369303 3270513873123998806420615 := by
  unfold tailWord_6369303
  simp only [CollatzResearch.WordTrace]
  refine ⟨232307565244110496194096563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154871710162740330796064375 232307565244110496194096563)
  ·
    refine ⟨348461347866165744291144845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232307565244110496194096563 348461347866165744291144845)
    ·
      refine ⟨130673005449812154109179317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348461347866165744291144845 130673005449812154109179317)
      ·
        refine ⟨12250594260919889447735561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130673005449812154109179317 12250594260919889447735561)
        ·
          refine ⟨9187945695689917085801671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12250594260919889447735561 9187945695689917085801671)
          ·
            refine ⟨13781918543534875628702507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187945695689917085801671 13781918543534875628702507)
            ·
              refine ⟨20672877815302313443053761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13781918543534875628702507 20672877815302313443053761)
              ·
                refine ⟨15504658361476735082290321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20672877815302313443053761 15504658361476735082290321)
                ·
                  refine ⟨11628493771107551311717741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15504658361476735082290321 11628493771107551311717741)
                  ·
                    refine ⟨4360685164165331741894153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11628493771107551311717741 4360685164165331741894153)
                    ·
                      refine ⟨3270513873123998806420615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360685164165331741894153 3270513873123998806420615)
                      ·
                        rfl

theorem cell23_6369303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6369303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369303 prefixEnd_6369303 := by exact prefixLift 6369303
  have htrace : WordTrace (prefixWord ++ tailWord_6369303) baseStart_6369303 baseEnd_6369303 := by
    simpa [prefixWord, tailWord_6369303, baseEnd_6369303] using wordTrace_append hprefix tailTrace_6369303
  have hstable : (prefixWord ++ tailWord_6369303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369303).length < 2 ^ (prefixWord ++ tailWord_6369303).sum := by decide
  have hdescent : baseEnd_6369303 < baseStart_6369303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369336 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_6369336 : Nat := 118140960795 + 6369336 * 2 ^ 59
def prefixEnd_6369336 : Nat := 4983230072969 + 3 ^ 40 * 6369336 * 2
def baseEnd_6369336 : Nat := 3270530817985597177307963

theorem tailTrace_6369336 : CollatzResearch.WordTrace tailWord_6369336 prefixEnd_6369336 3270530817985597177307963 := by
  unfold tailWord_6369336
  simp only [CollatzResearch.WordTrace]
  refine ⟨116154384426495471415023931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154872512568660628553365241 116154384426495471415023931)
  ·
    refine ⟨174231576639743207122535897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116154384426495471415023931 174231576639743207122535897)
    ·
      refine ⟨130673682479807405341901923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174231576639743207122535897 130673682479807405341901923)
      ·
        refine ⟨196010523719711108012852885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130673682479807405341901923 196010523719711108012852885)
        ·
          refine ⟨9187993299361458188102479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196010523719711108012852885 9187993299361458188102479)
          ·
            refine ⟨13781989949042187282153719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187993299361458188102479 13781989949042187282153719)
            ·
              refine ⟨20672984923563280923230579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13781989949042187282153719 20672984923563280923230579)
              ·
                refine ⟨31009477385344921384845869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20672984923563280923230579 31009477385344921384845869)
                ·
                  refine ⟨11628554019504345519317201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31009477385344921384845869 11628554019504345519317201)
                  ·
                    refine ⟨8721415514628259139487901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11628554019504345519317201 8721415514628259139487901)
                    ·
                      refine ⟨3270530817985597177307963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721415514628259139487901 3270530817985597177307963)
                      ·
                        rfl

theorem cell23_6369336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_6369336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369336 prefixEnd_6369336 := by exact prefixLift 6369336
  have htrace : WordTrace (prefixWord ++ tailWord_6369336) baseStart_6369336 baseEnd_6369336 := by
    simpa [prefixWord, tailWord_6369336, baseEnd_6369336] using wordTrace_append hprefix tailTrace_6369336
  have hstable : (prefixWord ++ tailWord_6369336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369336).length < 2 ^ (prefixWord ++ tailWord_6369336).sum := by decide
  have hdescent : baseEnd_6369336 < baseStart_6369336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369350 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6369350 : Nat := 118140960795 + 6369350 * 2 ^ 59
def prefixEnd_6369350 : Nat := 4983230072969 + 3 ^ 40 * 6369350 * 2
def baseEnd_6369350 : Nat := 3270538006714760122532899

theorem tailTrace_6369350 : CollatzResearch.WordTrace tailWord_6369350 prefixEnd_6369350 3270538006714760122532899 := by
  unfold tailWord_6369350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259664983591881975658047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154872852983293482147371669 7259664983591881975658047)
  ·
    refine ⟨10889497475387822963487071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259664983591881975658047 10889497475387822963487071)
    ·
      refine ⟨16334246213081734445230607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889497475387822963487071 16334246213081734445230607)
      ·
        refine ⟨24501369319622601667845911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16334246213081734445230607 24501369319622601667845911)
        ·
          refine ⟨36752053979433902501768867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24501369319622601667845911 36752053979433902501768867)
          ·
            refine ⟨55128080969150853752653301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36752053979433902501768867 55128080969150853752653301)
            ·
              refine ⟨5168257590857892539311247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55128080969150853752653301 5168257590857892539311247)
              ·
                refine ⟨7752386386286838808966871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168257590857892539311247 7752386386286838808966871)
                ·
                  refine ⟨11628579579430258213450307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752386386286838808966871 11628579579430258213450307)
                  ·
                    refine ⟨17442869369145387320175461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11628579579430258213450307 17442869369145387320175461)
                    ·
                      refine ⟨3270538006714760122532899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17442869369145387320175461 3270538006714760122532899)
                      ·
                        rfl

theorem cell23_6369350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6369350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369350 prefixEnd_6369350 := by exact prefixLift 6369350
  have htrace : WordTrace (prefixWord ++ tailWord_6369350) baseStart_6369350 baseEnd_6369350 := by
    simpa [prefixWord, tailWord_6369350, baseEnd_6369350] using wordTrace_append hprefix tailTrace_6369350
  have hstable : (prefixWord ++ tailWord_6369350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369350).length < 2 ^ (prefixWord ++ tailWord_6369350).sum := by decide
  have hdescent : baseEnd_6369350 < baseStart_6369350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369376 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2]
def baseStart_6369376 : Nat := 118140960795 + 6369376 * 2 ^ 59
def prefixEnd_6369376 : Nat := 4983230072969 + 3 ^ 40 * 6369376 * 2
def baseEnd_6369376 : Nat := 3270551357211777020807779

theorem tailTrace_6369376 : CollatzResearch.WordTrace tailWord_6369376 prefixEnd_6369376 3270551357211777020807779 := by
  unfold tailWord_6369376
  simp only [CollatzResearch.WordTrace]
  refine ⟨116155113886423014830751991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154873485181897353107669321 116155113886423014830751991)
  ·
    refine ⟨174232670829634522246127987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116155113886423014830751991 174232670829634522246127987)
    ·
      refine ⟨261349006244451783369191981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174232670829634522246127987 261349006244451783369191981)
      ·
        refine ⟨98005877341669418763446993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261349006244451783369191981 98005877341669418763446993)
        ·
          refine ⟨73504408006252064072585245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98005877341669418763446993 73504408006252064072585245)
          ·
            refine ⟨27564153002344524027219467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73504408006252064072585245 27564153002344524027219467)
            ·
              refine ⟨41346229503516786040829201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27564153002344524027219467 41346229503516786040829201)
              ·
                refine ⟨31009672127637589530621901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41346229503516786040829201 31009672127637589530621901)
                ·
                  refine ⟨11628627047864096073983213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31009672127637589530621901 11628627047864096073983213)
                  ·
                    refine ⟨4360735142949036027743705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11628627047864096073983213 4360735142949036027743705)
                    ·
                      refine ⟨3270551357211777020807779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360735142949036027743705 3270551357211777020807779)
                      ·
                        rfl

theorem cell23_6369376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_6369376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369376 prefixEnd_6369376 := by exact prefixLift 6369376
  have htrace : WordTrace (prefixWord ++ tailWord_6369376) baseStart_6369376 baseEnd_6369376 := by
    simpa [prefixWord, tailWord_6369376, baseEnd_6369376] using wordTrace_append hprefix tailTrace_6369376
  have hstable : (prefixWord ++ tailWord_6369376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369376).length < 2 ^ (prefixWord ++ tailWord_6369376).sum := by decide
  have hdescent : baseEnd_6369376 < baseStart_6369376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369389 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6369389 : Nat := 118140960795 + 6369389 * 2 ^ 59
def prefixEnd_6369389 : Nat := 4983230072969 + 3 ^ 40 * 6369389 * 2
def baseEnd_6369389 : Nat := 3270558032460285469945219

theorem tailTrace_6369389 : CollatzResearch.WordTrace tailWord_6369389 prefixEnd_6369389 3270558032460285469945219 := by
  unfold tailWord_6369389
  simp only [CollatzResearch.WordTrace]
  refine ⟨232310701921798932881727221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154873801281199288587818147 232310701921798932881727221)
  ·
    refine ⟨21779128305168649957661927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232310701921798932881727221 21779128305168649957661927)
    ·
      refine ⟨32668692457752974936492891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21779128305168649957661927 32668692457752974936492891)
      ·
        refine ⟨49003038686629462404739337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32668692457752974936492891 49003038686629462404739337)
        ·
          refine ⟨36752279014972096803554503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49003038686629462404739337 36752279014972096803554503)
          ·
            refine ⟨55128418522458145205331755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36752279014972096803554503 55128418522458145205331755)
            ·
              refine ⟨82692627783687217807997633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55128418522458145205331755 82692627783687217807997633)
              ·
                refine ⟨62019470837765413355998225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82692627783687217807997633 62019470837765413355998225)
                ·
                  refine ⟨46514603128324060016998669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62019470837765413355998225 46514603128324060016998669)
                  ·
                    refine ⟨17442976173121522506374501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46514603128324060016998669 17442976173121522506374501)
                    ·
                      refine ⟨3270558032460285469945219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17442976173121522506374501 3270558032460285469945219)
                      ·
                        rfl

theorem cell23_6369389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6369389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369389 prefixEnd_6369389 := by exact prefixLift 6369389
  have htrace : WordTrace (prefixWord ++ tailWord_6369389) baseStart_6369389 baseEnd_6369389 := by
    simpa [prefixWord, tailWord_6369389, baseEnd_6369389] using wordTrace_append hprefix tailTrace_6369389
  have hstable : (prefixWord ++ tailWord_6369389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369389).length < 2 ^ (prefixWord ++ tailWord_6369389).sum := by decide
  have hdescent : baseEnd_6369389 < baseStart_6369389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369429 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 7]
def baseStart_6369429 : Nat := 118140960795 + 6369429 * 2 ^ 59
def prefixEnd_6369429 : Nat := 4983230072969 + 3 ^ 40 * 6369429 * 2
def baseEnd_6369429 : Nat := 363397619076273923716115

theorem tailTrace_6369429 : CollatzResearch.WordTrace tailWord_6369429 prefixEnd_6369429 363397619076273923716115 := by
  unfold tailWord_6369429
  simp only [CollatzResearch.WordTrace]
  refine ⟨232312160841654019713183341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154874773894436013142122227 232312160841654019713183341)
  ·
    refine ⟨87117060315620257392443753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232312160841654019713183341 87117060315620257392443753)
    ·
      refine ⟨65337795236715193044332815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87117060315620257392443753 65337795236715193044332815)
      ·
        refine ⟨98006692855072789566499223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65337795236715193044332815 98006692855072789566499223)
        ·
          refine ⟨147010039282609184349748835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98006692855072789566499223 147010039282609184349748835)
          ·
            refine ⟨220515058923913776524623253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147010039282609184349748835 220515058923913776524623253)
            ·
              refine ⟨10336643387058458274591715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220515058923913776524623253 10336643387058458274591715)
              ·
                refine ⟨15504965080587687411887573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10336643387058458274591715 15504965080587687411887573)
                ·
                  refine ⟨363397619076273923716115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15504965080587687411887573 363397619076273923716115)
                  ·
                    rfl

theorem cell23_6369429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_6369429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369429 prefixEnd_6369429 := by exact prefixLift 6369429
  have htrace : WordTrace (prefixWord ++ tailWord_6369429) baseStart_6369429 baseEnd_6369429 := by
    simpa [prefixWord, tailWord_6369429, baseEnd_6369429] using wordTrace_append hprefix tailTrace_6369429
  have hstable : (prefixWord ++ tailWord_6369429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369429).length < 2 ^ (prefixWord ++ tailWord_6369429).sum := by decide
  have hdescent : baseEnd_6369429 < baseStart_6369429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369459 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 2, 5]
def baseStart_6369459 : Nat := 118140960795 + 6369459 * 2 ^ 59
def prefixEnd_6369459 : Nat := 4983230072969 + 3 ^ 40 * 6369459 * 2
def baseEnd_6369459 : Nat := 1090197992035366732023299

theorem tailTrace_6369459 : CollatzResearch.WordTrace tailWord_6369459 prefixEnd_6369459 1090197992035366732023299 := by
  unfold tailWord_6369459
  simp only [CollatzResearch.WordTrace]
  refine ⟨232313255031545334836775431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154875503354363556557850287 232313255031545334836775431)
  ·
    refine ⟨348469882547318002255163147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232313255031545334836775431 348469882547318002255163147)
    ·
      refine ⟨522704823820977003382744721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348469882547318002255163147 522704823820977003382744721)
      ·
        refine ⟨392028617865732752537058541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522704823820977003382744721 392028617865732752537058541)
        ·
          refine ⟨147010731699649782201396953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392028617865732752537058541 147010731699649782201396953)
          ·
            refine ⟨110258048774737336651047715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147010731699649782201396953 110258048774737336651047715)
            ·
              refine ⟨165387073162106004976571573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110258048774737336651047715 165387073162106004976571573)
              ·
                refine ⟨15505038108947437966553585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165387073162106004976571573 15505038108947437966553585)
                ·
                  refine ⟨11628778581710578474915189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15505038108947437966553585 11628778581710578474915189)
                  ·
                    refine ⟨1090197992035366732023299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11628778581710578474915189 1090197992035366732023299)
                    ·
                      rfl

theorem cell23_6369459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].length) (baseStart_6369459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369459 prefixEnd_6369459 := by exact prefixLift 6369459
  have htrace : WordTrace (prefixWord ++ tailWord_6369459) baseStart_6369459 baseEnd_6369459 := by
    simpa [prefixWord, tailWord_6369459, baseEnd_6369459] using wordTrace_append hprefix tailTrace_6369459
  have hstable : (prefixWord ++ tailWord_6369459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369459).length < 2 ^ (prefixWord ++ tailWord_6369459).sum := by decide
  have hdescent : baseEnd_6369459 < baseStart_6369459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369463 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 5]
def baseStart_6369463 : Nat := 118140960795 + 6369463 * 2 ^ 59
def prefixEnd_6369463 : Nat := 4983230072969 + 3 ^ 40 * 6369463 * 2
def baseEnd_6369463 : Nat := 363399558892079797824431

theorem tailTrace_6369463 : CollatzResearch.WordTrace tailWord_6369463 prefixEnd_6369463 363399558892079797824431 := by
  unfold tailWord_6369463
  simp only [CollatzResearch.WordTrace]
  refine ⟨232313400923530843519921043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154875600615687229013280695 232313400923530843519921043)
  ·
    refine ⟨348470101385296265279881565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232313400923530843519921043 348470101385296265279881565)
    ·
      refine ⟨130676288019486099479955587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348470101385296265279881565 130676288019486099479955587)
      ·
        refine ⟨196014432029229149219933381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130676288019486099479955587 196014432029229149219933381)
        ·
          refine ⟨36752706005480465478737509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196014432029229149219933381 36752706005480465478737509)
          ·
            refine ⟨6891132376027587277263283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36752706005480465478737509 6891132376027587277263283)
            ·
              refine ⟨10336698564041380915894925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891132376027587277263283 10336698564041380915894925)
              ·
                refine ⟨3876261961515517843460597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10336698564041380915894925 3876261961515517843460597)
                ·
                  refine ⟨363399558892079797824431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3876261961515517843460597 363399558892079797824431)
                  ·
                    rfl

theorem cell23_6369463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 5].length) (baseStart_6369463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369463 prefixEnd_6369463 := by exact prefixLift 6369463
  have htrace : WordTrace (prefixWord ++ tailWord_6369463) baseStart_6369463 baseEnd_6369463 := by
    simpa [prefixWord, tailWord_6369463, baseEnd_6369463] using wordTrace_append hprefix tailTrace_6369463
  have hstable : (prefixWord ++ tailWord_6369463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369463).length < 2 ^ (prefixWord ++ tailWord_6369463).sum := by decide
  have hdescent : baseEnd_6369463 < baseStart_6369463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369469 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_6369469 : Nat := 118140960795 + 6369469 * 2 ^ 59
def prefixEnd_6369469 : Nat := 4983230072969 + 3 ^ 40 * 6369469 * 2
def baseEnd_6369469 : Nat := 3270599110912645156944851

theorem tailTrace_6369469 : CollatzResearch.WordTrace tailWord_6369469 prefixEnd_6369469 3270599110912645156944851 := by
  unfold tailWord_6369469
  simp only [CollatzResearch.WordTrace]
  refine ⟨232313619761509106544639461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154875746507672737696426307 232313619761509106544639461)
  ·
    refine ⟨43558803705282957477119899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232313619761509106544639461 43558803705282957477119899)
    ·
      refine ⟨65338205557924436215679849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43558803705282957477119899 65338205557924436215679849)
      ·
        refine ⟨49003654168443327161759887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65338205557924436215679849 49003654168443327161759887)
        ·
          refine ⟨73505481252664990742639831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49003654168443327161759887 73505481252664990742639831)
          ·
            refine ⟨110258221878997486113959747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73505481252664990742639831 110258221878997486113959747)
            ·
              refine ⟨165387332818496229170939621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110258221878997486113959747 165387332818496229170939621)
              ·
                refine ⟨31010124903468042969551179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165387332818496229170939621 31010124903468042969551179)
                ·
                  refine ⟨46515187355202064454326769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31010124903468042969551179 46515187355202064454326769)
                  ·
                    refine ⟨34886390516401548340745077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46515187355202064454326769 34886390516401548340745077)
                    ·
                      refine ⟨3270599110912645156944851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34886390516401548340745077 3270599110912645156944851)
                      ·
                        rfl

theorem cell23_6369469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_6369469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369469 prefixEnd_6369469 := by exact prefixLift 6369469
  have htrace : WordTrace (prefixWord ++ tailWord_6369469) baseStart_6369469 baseEnd_6369469 := by
    simpa [prefixWord, tailWord_6369469, baseEnd_6369469] using wordTrace_append hprefix tailTrace_6369469
  have hstable : (prefixWord ++ tailWord_6369469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369469).length < 2 ^ (prefixWord ++ tailWord_6369469).sum := by decide
  have hdescent : baseEnd_6369469 < baseStart_6369469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369476 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6369476 : Nat := 118140960795 + 6369476 * 2 ^ 59
def prefixEnd_6369476 : Nat := 4983230072969 + 3 ^ 40 * 6369476 * 2
def baseEnd_6369476 : Nat := 1090200901759075543185773

theorem tailTrace_6369476 : CollatzResearch.WordTrace tailWord_6369476 prefixEnd_6369476 1090200901759075543185773 := by
  unfold tailWord_6369476
  simp only [CollatzResearch.WordTrace]
  refine ⟨116156937536241873370072141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154875916714989164493429521 116156937536241873370072141)
  ·
    refine ⟨43558851576090702513777053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116156937536241873370072141 43558851576090702513777053)
    ·
      refine ⟨16334569341034013442666395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43558851576090702513777053 16334569341034013442666395)
      ·
        refine ⟨24501854011551020163999593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16334569341034013442666395 24501854011551020163999593)
        ·
          refine ⟨18376390508663265122999695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24501854011551020163999593 18376390508663265122999695)
          ·
            refine ⟨27564585762994897684499543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18376390508663265122999695 27564585762994897684499543)
            ·
              refine ⟨41346878644492346526749315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27564585762994897684499543 41346878644492346526749315)
              ·
                refine ⟨62020317966738519790123973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41346878644492346526749315 62020317966738519790123973)
                ·
                  refine ⟨11628809618763472460648245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62020317966738519790123973 11628809618763472460648245)
                  ·
                    refine ⟨1090200901759075543185773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11628809618763472460648245 1090200901759075543185773)
                    ·
                      rfl

theorem cell23_6369476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6369476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369476 prefixEnd_6369476 := by exact prefixLift 6369476
  have htrace : WordTrace (prefixWord ++ tailWord_6369476) baseStart_6369476 baseEnd_6369476 := by
    simpa [prefixWord, tailWord_6369476, baseEnd_6369476] using wordTrace_append hprefix tailTrace_6369476
  have hstable : (prefixWord ++ tailWord_6369476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369476).length < 2 ^ (prefixWord ++ tailWord_6369476).sum := by decide
  have hdescent : baseEnd_6369476 < baseStart_6369476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369486 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6369486 : Nat := 118140960795 + 6369486 * 2 ^ 59
def prefixEnd_6369486 : Nat := 4983230072969 + 3 ^ 40 * 6369486 * 2
def baseEnd_6369486 : Nat := 3270607840083771590432273

theorem tailTrace_6369486 : CollatzResearch.WordTrace tailWord_6369486 prefixEnd_6369486 3270607840083771590432273 := by
  unfold tailWord_6369486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29039279975305939806001039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154876159868298345632005541 29039279975305939806001039)
  ·
    refine ⟨43558919962958909709001559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29039279975305939806001039 43558919962958909709001559)
    ·
      refine ⟨65338379944438364563502339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43558919962958909709001559 65338379944438364563502339)
      ·
        refine ⟨98007569916657546845253509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65338379944438364563502339 98007569916657546845253509)
        ·
          refine ⟨18376419359373290033485033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98007569916657546845253509 18376419359373290033485033)
          ·
            refine ⟨13782314519529967525113775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18376419359373290033485033 13782314519529967525113775)
            ·
              refine ⟨20673471779294951287670663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13782314519529967525113775 20673471779294951287670663)
              ·
                refine ⟨31010207668942426931505995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20673471779294951287670663 31010207668942426931505995)
                ·
                  refine ⟨46515311503413640397258993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31010207668942426931505995 46515311503413640397258993)
                  ·
                    refine ⟨34886483627560230297944245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46515311503413640397258993 34886483627560230297944245)
                    ·
                      refine ⟨3270607840083771590432273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34886483627560230297944245 3270607840083771590432273)
                      ·
                        rfl

theorem cell23_6369486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6369486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369486 prefixEnd_6369486 := by exact prefixLift 6369486
  have htrace : WordTrace (prefixWord ++ tailWord_6369486) baseStart_6369486 baseEnd_6369486 := by
    simpa [prefixWord, tailWord_6369486, baseEnd_6369486] using wordTrace_append hprefix tailTrace_6369486
  have hstable : (prefixWord ++ tailWord_6369486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369486).length < 2 ^ (prefixWord ++ tailWord_6369486).sum := by decide
  have hdescent : baseEnd_6369486 < baseStart_6369486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369523 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 1, 4]
def baseStart_6369523 : Nat := 118140960795 + 6369523 * 2 ^ 59
def prefixEnd_6369523 : Nat := 4983230072969 + 3 ^ 40 * 6369523 * 2
def baseEnd_6369523 : Nat := 1090208946289329315223201

theorem tailTrace_6369523 : CollatzResearch.WordTrace tailWord_6369523 prefixEnd_6369523 1090208946289329315223201 := by
  unfold tailWord_6369523
  simp only [CollatzResearch.WordTrace]
  refine ⟨232315589303313473767105223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154877059535542315844736815 232315589303313473767105223)
  ·
    refine ⟨348473383954970210650657835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232315589303313473767105223 348473383954970210650657835)
    ·
      refine ⟨522710075932455315975986753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348473383954970210650657835 522710075932455315975986753)
      ·
        refine ⟨392032556949341486981990065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522710075932455315975986753 392032556949341486981990065)
        ·
          refine ⟨294024417712006115236492549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392032556949341486981990065 294024417712006115236492549)
          ·
            refine ⟨55129578321001146606842353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294024417712006115236492549 55129578321001146606842353)
            ·
              refine ⟨41347183740750859955131765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55129578321001146606842353 41347183740750859955131765)
              ·
                refine ⟨3876298475695393120793603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41347183740750859955131765 3876298475695393120793603)
                ·
                  refine ⟨5814447713543089681190405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876298475695393120793603 5814447713543089681190405)
                  ·
                    refine ⟨1090208946289329315223201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814447713543089681190405 1090208946289329315223201)
                    ·
                      rfl

theorem cell23_6369523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 4].length) (baseStart_6369523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369523 prefixEnd_6369523 := by exact prefixLift 6369523
  have htrace : WordTrace (prefixWord ++ tailWord_6369523) baseStart_6369523 baseEnd_6369523 := by
    simpa [prefixWord, tailWord_6369523, baseEnd_6369523] using wordTrace_append hprefix tailTrace_6369523
  have hstable : (prefixWord ++ tailWord_6369523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369523).length < 2 ^ (prefixWord ++ tailWord_6369523).sum := by decide
  have hdescent : baseEnd_6369523 < baseStart_6369523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369539 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_6369539 : Nat := 118140960795 + 6369539 * 2 ^ 59
def prefixEnd_6369539 : Nat := 4983230072969 + 3 ^ 40 * 6369539 * 2
def baseEnd_6369539 : Nat := 3270635054558459883069529

theorem tailTrace_6369539 : CollatzResearch.WordTrace tailWord_6369539 prefixEnd_6369539 3270635054558459883069529 := by
  unfold tailWord_6369539
  simp only [CollatzResearch.WordTrace]
  refine ⟨232316172871255508499687671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154877448580837005666458447 232316172871255508499687671)
  ·
    refine ⟨348474259306883262749531507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232316172871255508499687671 348474259306883262749531507)
    ·
      refine ⟨522711388960324894124297261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348474259306883262749531507 522711388960324894124297261)
      ·
        refine ⟨196016770860121835296611473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522711388960324894124297261 196016770860121835296611473)
        ·
          refine ⟨147012578145091376472458605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196016770860121835296611473 147012578145091376472458605)
          ·
            refine ⟨55129716804409266177171977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147012578145091376472458605 55129716804409266177171977)
            ·
              refine ⟨41347287603306949632878983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55129716804409266177171977 41347287603306949632878983)
              ·
                refine ⟨62020931404960424449318475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41347287603306949632878983 62020931404960424449318475)
                ·
                  refine ⟨93031397107440636673977713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62020931404960424449318475 93031397107440636673977713)
                  ·
                    refine ⟨69773547830580477505483285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93031397107440636673977713 69773547830580477505483285)
                    ·
                      refine ⟨3270635054558459883069529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69773547830580477505483285 3270635054558459883069529)
                      ·
                        rfl

theorem cell23_6369539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_6369539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369539 prefixEnd_6369539 := by exact prefixLift 6369539
  have htrace : WordTrace (prefixWord ++ tailWord_6369539) baseStart_6369539 baseEnd_6369539 := by
    simpa [prefixWord, tailWord_6369539, baseEnd_6369539] using wordTrace_append hprefix tailTrace_6369539
  have hstable : (prefixWord ++ tailWord_6369539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369539).length < 2 ^ (prefixWord ++ tailWord_6369539).sum := by decide
  have hdescent : baseEnd_6369539 < baseStart_6369539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369580 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_6369580 : Nat := 118140960795 + 6369580 * 2 ^ 59
def prefixEnd_6369580 : Nat := 4983230072969 + 3 ^ 40 * 6369580 * 2
def baseEnd_6369580 : Nat := 3270656107265294222656841

theorem tailTrace_6369580 : CollatzResearch.WordTrace tailWord_6369580 prefixEnd_6369580 3270656107265294222656841 := by
  unfold tailWord_6369580
  simp only [CollatzResearch.WordTrace]
  refine ⟨116158834132053486250965097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154878445509404648334620129 116158834132053486250965097)
  ·
    refine ⟨87119125599040114688223823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116158834132053486250965097 87119125599040114688223823)
    ·
      refine ⟨130678688398560172032335735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87119125599040114688223823 130678688398560172032335735)
      ·
        refine ⟨196018032597840258048503603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130678688398560172032335735 196018032597840258048503603)
        ·
          refine ⟨294027048896760387072755405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196018032597840258048503603 294027048896760387072755405)
          ·
            refine ⟨110260143336285145152283277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294027048896760387072755405 110260143336285145152283277)
            ·
              refine ⟨41347553751106929432106229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110260143336285145152283277 41347553751106929432106229)
              ·
                refine ⟨3876333164166274634259959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41347553751106929432106229 3876333164166274634259959)
                ·
                  refine ⟨5814499746249411951389939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876333164166274634259959 5814499746249411951389939)
                  ·
                    refine ⟨8721749619374117927084909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5814499746249411951389939 8721749619374117927084909)
                    ·
                      refine ⟨3270656107265294222656841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721749619374117927084909 3270656107265294222656841)
                      ·
                        rfl

theorem cell23_6369580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_6369580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369580 prefixEnd_6369580 := by exact prefixLift 6369580
  have htrace : WordTrace (prefixWord ++ tailWord_6369580) baseStart_6369580 baseEnd_6369580 := by
    simpa [prefixWord, tailWord_6369580, baseEnd_6369580] using wordTrace_append hprefix tailTrace_6369580
  have hstable : (prefixWord ++ tailWord_6369580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369580).length < 2 ^ (prefixWord ++ tailWord_6369580).sum := by decide
  have hdescent : baseEnd_6369580 < baseStart_6369580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369583 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 1, 5]
def baseStart_6369583 : Nat := 118140960795 + 6369583 * 2 ^ 59
def prefixEnd_6369583 : Nat := 4983230072969 + 3 ^ 40 * 6369583 * 2
def baseEnd_6369583 : Nat := 1090219215902419236973109

theorem tailTrace_6369583 : CollatzResearch.WordTrace tailWord_6369583 prefixEnd_6369583 1090219215902419236973109 := by
  unfold tailWord_6369583
  simp only [CollatzResearch.WordTrace]
  refine ⟨232317777683096104014289403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154878518455397402676192935 232317777683096104014289403)
  ·
    refine ⟨348476666524644156021434105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232317777683096104014289403 348476666524644156021434105)
    ·
      refine ⟨261357499893483117016075579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348476666524644156021434105 261357499893483117016075579)
      ·
        refine ⟨392036249840224675524113369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261357499893483117016075579 392036249840224675524113369)
        ·
          refine ⟨294027187380168506643085027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392036249840224675524113369 294027187380168506643085027)
          ·
            refine ⟨441040781070252759964627541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294027187380168506643085027 441040781070252759964627541)
            ·
              refine ⟨5168446653167024530835479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 441040781070252759964627541 5168446653167024530835479)
              ·
                refine ⟨7752669979750536796253219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168446653167024530835479 7752669979750536796253219)
                ·
                  refine ⟨11629004969625805194379829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752669979750536796253219 11629004969625805194379829)
                  ·
                    refine ⟨1090219215902419236973109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11629004969625805194379829 1090219215902419236973109)
                    ·
                      rfl

theorem cell23_6369583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_6369583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369583 prefixEnd_6369583 := by exact prefixLift 6369583
  have htrace : WordTrace (prefixWord ++ tailWord_6369583) baseStart_6369583 baseEnd_6369583 := by
    simpa [prefixWord, tailWord_6369583, baseEnd_6369583] using wordTrace_append hprefix tailTrace_6369583
  have hstable : (prefixWord ++ tailWord_6369583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369583).length < 2 ^ (prefixWord ++ tailWord_6369583).sum := by decide
  have hdescent : baseEnd_6369583 < baseStart_6369583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369609 : List Nat := [1, 2, 1, 1, 2, 3, 1, 12]
def baseStart_6369609 : Nat := 118140960795 + 6369609 * 2 ^ 59
def prefixEnd_6369609 : Nat := 4983230072969 + 3 ^ 40 * 6369609 * 2
def baseEnd_6369609 : Nat := 121135962896454615155341

theorem tailTrace_6369609 : CollatzResearch.WordTrace tailWord_6369609 prefixEnd_6369609 121135962896454615155341 := by
  unfold tailWord_6369609
  simp only [CollatzResearch.WordTrace]
  refine ⟨232318725981001910454735881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154879150654001273636490587 232318725981001910454735881)
  ·
    refine ⟨174239044485751432841051911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232318725981001910454735881 174239044485751432841051911)
    ·
      refine ⟨261358566728627149261577867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174239044485751432841051911 261358566728627149261577867)
      ·
        refine ⟨392037850092940723892366801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261358566728627149261577867 392037850092940723892366801)
        ·
          refine ⟨294028387569705542919275101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392037850092940723892366801 294028387569705542919275101)
          ·
            refine ⟨110260645338639578594728163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294028387569705542919275101 110260645338639578594728163)
            ·
              refine ⟨165390968007959367892092245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110260645338639578594728163 165390968007959367892092245)
              ·
                refine ⟨121135962896454615155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 165390968007959367892092245 121135962896454615155341)
                ·
                  rfl

theorem cell23_6369609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 12].length) (baseStart_6369609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369609 prefixEnd_6369609 := by exact prefixLift 6369609
  have htrace : WordTrace (prefixWord ++ tailWord_6369609) baseStart_6369609 baseEnd_6369609 := by
    simpa [prefixWord, tailWord_6369609, baseEnd_6369609] using wordTrace_append hprefix tailTrace_6369609
  have hstable : (prefixWord ++ tailWord_6369609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369609).length < 2 ^ (prefixWord ++ tailWord_6369609).sum := by decide
  have hdescent : baseEnd_6369609 < baseStart_6369609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369616 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_6369616 : Nat := 118140960795 + 6369616 * 2 ^ 59
def prefixEnd_6369616 : Nat := 4983230072969 + 3 ^ 40 * 6369616 * 2
def baseEnd_6369616 : Nat := 3270674592568856081806675

theorem tailTrace_6369616 : CollatzResearch.WordTrace tailWord_6369616 prefixEnd_6369616 3270674592568856081806675 := by
  unfold tailWord_6369616
  simp only [CollatzResearch.WordTrace]
  refine ⟨116159490645988275325120351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154879320861317700433493801 116159490645988275325120351)
  ·
    refine ⟨174239235968982412987680527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116159490645988275325120351 174239235968982412987680527)
    ·
      refine ⟨261358853953473619481520791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174239235968982412987680527 261358853953473619481520791)
      ·
        refine ⟨392038280930210429222281187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261358853953473619481520791 392038280930210429222281187)
        ·
          refine ⟨588057421395315643833421781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392038280930210429222281187 588057421395315643833421781)
          ·
            refine ⟨13782595813952710402345823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 588057421395315643833421781 13782595813952710402345823)
            ·
              refine ⟨20673893720929065603518735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13782595813952710402345823 20673893720929065603518735)
              ·
                refine ⟨31010840581393598405278103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20673893720929065603518735 31010840581393598405278103)
                ·
                  refine ⟨46516260872090397607917155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31010840581393598405278103 46516260872090397607917155)
                  ·
                    refine ⟨69774391308135596411875733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46516260872090397607917155 69774391308135596411875733)
                    ·
                      refine ⟨3270674592568856081806675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69774391308135596411875733 3270674592568856081806675)
                      ·
                        rfl

theorem cell23_6369616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_6369616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369616 prefixEnd_6369616 := by exact prefixLift 6369616
  have htrace : WordTrace (prefixWord ++ tailWord_6369616) baseStart_6369616 baseEnd_6369616 := by
    simpa [prefixWord, tailWord_6369616, baseEnd_6369616] using wordTrace_append hprefix tailTrace_6369616
  have hstable : (prefixWord ++ tailWord_6369616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369616).length < 2 ^ (prefixWord ++ tailWord_6369616).sum := by decide
  have hdescent : baseEnd_6369616 < baseStart_6369616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369620 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_6369620 : Nat := 118140960795 + 6369620 * 2 ^ 59
def prefixEnd_6369620 : Nat := 4983230072969 + 3 ^ 40 * 6369620 * 2
def baseEnd_6369620 : Nat := 3270676646491474066156657

theorem tailTrace_6369620 : CollatzResearch.WordTrace tailWord_6369620 prefixEnd_6369620 3270676646491474066156657 := by
  unfold tailWord_6369620
  simp only [CollatzResearch.WordTrace]
  refine ⟨116159563591981029666693157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154879418122641372888924209 116159563591981029666693157)
  ·
    refine ⟨21779918173496443062504967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116159563591981029666693157 21779918173496443062504967)
    ·
      refine ⟨32669877260244664593757451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21779918173496443062504967 32669877260244664593757451)
      ·
        refine ⟨49004815890366996890636177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32669877260244664593757451 49004815890366996890636177)
        ·
          refine ⟨36753611917775247667977133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49004815890366996890636177 36753611917775247667977133)
          ·
            refine ⟨13782604469165717875491425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36753611917775247667977133 13782604469165717875491425)
            ·
              refine ⟨10336953351874288406618569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13782604469165717875491425 10336953351874288406618569)
              ·
                refine ⟨7752715013905716304963927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10336953351874288406618569 7752715013905716304963927)
                ·
                  refine ⟨11629072520858574457445891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752715013905716304963927 11629072520858574457445891)
                  ·
                    refine ⟨17443608781287861686168837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11629072520858574457445891 17443608781287861686168837)
                    ·
                      refine ⟨3270676646491474066156657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17443608781287861686168837 3270676646491474066156657)
                      ·
                        rfl

theorem cell23_6369620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_6369620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369620 prefixEnd_6369620 := by exact prefixLift 6369620
  have htrace : WordTrace (prefixWord ++ tailWord_6369620) baseStart_6369620 baseEnd_6369620 := by
    simpa [prefixWord, tailWord_6369620, baseEnd_6369620] using wordTrace_append hprefix tailTrace_6369620
  have hstable : (prefixWord ++ tailWord_6369620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369620).length < 2 ^ (prefixWord ++ tailWord_6369620).sum := by decide
  have hdescent : baseEnd_6369620 < baseStart_6369620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369640 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6369640 : Nat := 118140960795 + 6369640 * 2 ^ 59
def prefixEnd_6369640 : Nat := 4983230072969 + 3 ^ 40 * 6369640 * 2
def baseEnd_6369640 : Nat := 3270686916104563987906565

theorem tailTrace_6369640 : CollatzResearch.WordTrace tailWord_6369640 prefixEnd_6369640 3270686916104563987906565 := by
  unfold tailWord_6369640
  simp only [CollatzResearch.WordTrace]
  refine ⟨116159928321944801374557187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154879904429259735166076249 116159928321944801374557187)
  ·
    refine ⟨174239892482917202061835781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116159928321944801374557187 174239892482917202061835781)
    ·
      refine ⟨32669979840546975386594209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174239892482917202061835781 32669979840546975386594209)
      ·
        refine ⟨24502484880410231539945657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32669979840546975386594209 24502484880410231539945657)
        ·
          refine ⟨18376863660307673654959243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24502484880410231539945657 18376863660307673654959243)
          ·
            refine ⟨27565295490461510482438865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18376863660307673654959243 27565295490461510482438865)
            ·
              refine ⟨20673971617846132861829149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27565295490461510482438865 20673971617846132861829149)
              ·
                refine ⟨7752739356692299823185931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20673971617846132861829149 7752739356692299823185931)
                ·
                  refine ⟨11629109035038449734778897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752739356692299823185931 11629109035038449734778897)
                  ·
                    refine ⟨8721831776278837301084173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11629109035038449734778897 8721831776278837301084173)
                    ·
                      refine ⟨3270686916104563987906565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721831776278837301084173 3270686916104563987906565)
                      ·
                        rfl

theorem cell23_6369640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6369640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369640 prefixEnd_6369640 := by exact prefixLift 6369640
  have htrace : WordTrace (prefixWord ++ tailWord_6369640) baseStart_6369640 baseEnd_6369640 := by
    simpa [prefixWord, tailWord_6369640, baseEnd_6369640] using wordTrace_append hprefix tailTrace_6369640
  have hstable : (prefixWord ++ tailWord_6369640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369640).length < 2 ^ (prefixWord ++ tailWord_6369640).sum := by decide
  have hdescent : baseEnd_6369640 < baseStart_6369640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369663 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 5, 3, 2]
def baseStart_6369663 : Nat := 118140960795 + 6369663 * 2 ^ 59
def prefixEnd_6369663 : Nat := 4983230072969 + 3 ^ 40 * 6369663 * 2
def baseEnd_6369663 : Nat := 3270698726159617397918959

theorem tailTrace_6369663 : CollatzResearch.WordTrace tailWord_6369663 prefixEnd_6369663 3270698726159617397918959 := by
  unfold tailWord_6369663
  simp only [CollatzResearch.WordTrace]
  refine ⟨232320695522806277677201643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154880463681870851784801095 232320695522806277677201643)
  ·
    refine ⟨348481043284209416515802465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232320695522806277677201643 348481043284209416515802465)
    ·
      refine ⟨261360782463157062386851849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348481043284209416515802465 261360782463157062386851849)
      ·
        refine ⟨196020586847367796790138887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261360782463157062386851849 196020586847367796790138887)
        ·
          refine ⟨294030880271051695185208331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196020586847367796790138887 294030880271051695185208331)
          ·
            refine ⟨441046320406577542777812497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294030880271051695185208331 441046320406577542777812497)
            ·
              refine ⟨330784740304933157083359373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441046320406577542777812497 330784740304933157083359373)
              ·
                refine ⟨124044277614349933906259765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330784740304933157083359373 124044277614349933906259765)
                ·
                  refine ⟨11629151026345306303711853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124044277614349933906259765 11629151026345306303711853)
                  ·
                    refine ⟨4360931634879489863891945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11629151026345306303711853 4360931634879489863891945)
                    ·
                      refine ⟨3270698726159617397918959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4360931634879489863891945 3270698726159617397918959)
                      ·
                        rfl

theorem cell23_6369663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_6369663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369663 prefixEnd_6369663 := by exact prefixLift 6369663
  have htrace : WordTrace (prefixWord ++ tailWord_6369663) baseStart_6369663 baseEnd_6369663 := by
    simpa [prefixWord, tailWord_6369663, baseEnd_6369663] using wordTrace_append hprefix tailTrace_6369663
  have hstable : (prefixWord ++ tailWord_6369663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369663).length < 2 ^ (prefixWord ++ tailWord_6369663).sum := by decide
  have hdescent : baseEnd_6369663 < baseStart_6369663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369674 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6369674 : Nat := 118140960795 + 6369674 * 2 ^ 59
def prefixEnd_6369674 : Nat := 4983230072969 + 3 ^ 40 * 6369674 * 2
def baseEnd_6369674 : Nat := 3270704374446816854881409

theorem tailTrace_6369674 : CollatzResearch.WordTrace tailWord_6369674 prefixEnd_6369674 3270704374446816854881409 := by
  unfold tailWord_6369674
  simp only [CollatzResearch.WordTrace]
  refine ⟨58080274181441606638963019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154880731150510951037234717 58080274181441606638963019)
  ·
    refine ⟨87120411272162409958444529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58080274181441606638963019 87120411272162409958444529)
    ·
      refine ⟨65340308454121807468833397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87120411272162409958444529 65340308454121807468833397)
      ·
        refine ⟨6125653917573919450203131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65340308454121807468833397 6125653917573919450203131)
        ·
          refine ⟨9188480876360879175304697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125653917573919450203131 9188480876360879175304697)
          ·
            refine ⟨6891360657270659381478523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188480876360879175304697 6891360657270659381478523)
            ·
              refine ⟨10337040985905989072217785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891360657270659381478523 10337040985905989072217785)
              ·
                refine ⟨7752780739429491804163339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10337040985905989072217785 7752780739429491804163339)
                ·
                  refine ⟨11629171109144237706245009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752780739429491804163339 11629171109144237706245009)
                  ·
                    refine ⟨8721878331858178279683757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11629171109144237706245009 8721878331858178279683757)
                    ·
                      refine ⟨3270704374446816854881409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721878331858178279683757 3270704374446816854881409)
                      ·
                        rfl

theorem cell23_6369674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6369674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369674 prefixEnd_6369674 := by exact prefixLift 6369674
  have htrace : WordTrace (prefixWord ++ tailWord_6369674) baseStart_6369674 baseEnd_6369674 := by
    simpa [prefixWord, tailWord_6369674, baseEnd_6369674] using wordTrace_append hprefix tailTrace_6369674
  have hstable : (prefixWord ++ tailWord_6369674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369674).length < 2 ^ (prefixWord ++ tailWord_6369674).sum := by decide
  have hdescent : baseEnd_6369674 < baseStart_6369674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369704 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6369704 : Nat := 118140960795 + 6369704 * 2 ^ 59
def prefixEnd_6369704 : Nat := 4983230072969 + 3 ^ 40 * 6369704 * 2
def baseEnd_6369704 : Nat := 3270719778866451737506271

theorem tailTrace_6369704 : CollatzResearch.WordTrace tailWord_6369704 prefixEnd_6369704 3270719778866451737506271 := by
  unfold tailWord_6369704
  simp only [CollatzResearch.WordTrace]
  refine ⟨116161095457828870839722083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154881460610438494452962777 116161095457828870839722083)
  ·
    refine ⟨174241643186743306259583125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116161095457828870839722083 174241643186743306259583125)
    ·
      refine ⟨8167577024378592480917959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174241643186743306259583125 8167577024378592480917959)
      ·
        refine ⟨12251365536567888721376939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167577024378592480917959 12251365536567888721376939)
        ·
          refine ⟨18377048304851833082065409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12251365536567888721376939 18377048304851833082065409)
          ·
            refine ⟨13782786228638874811549057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18377048304851833082065409 13782786228638874811549057)
            ·
              refine ⟨10337089671479156108661793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13782786228638874811549057 10337089671479156108661793)
              ·
                refine ⟨7752817253609367081496345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10337089671479156108661793 7752817253609367081496345)
                ·
                  refine ⟨5814612940207025311122259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7752817253609367081496345 5814612940207025311122259)
                  ·
                    refine ⟨8721919410310537966683389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5814612940207025311122259 8721919410310537966683389)
                    ·
                      refine ⟨3270719778866451737506271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721919410310537966683389 3270719778866451737506271)
                      ·
                        rfl

theorem cell23_6369704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6369704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369704 prefixEnd_6369704 := by exact prefixLift 6369704
  have htrace : WordTrace (prefixWord ++ tailWord_6369704) baseStart_6369704 baseEnd_6369704 := by
    simpa [prefixWord, tailWord_6369704, baseEnd_6369704] using wordTrace_append hprefix tailTrace_6369704
  have hstable : (prefixWord ++ tailWord_6369704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369704).length < 2 ^ (prefixWord ++ tailWord_6369704).sum := by decide
  have hdescent : baseEnd_6369704 < baseStart_6369704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369713 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6369713 : Nat := 118140960795 + 6369713 * 2 ^ 59
def prefixEnd_6369713 : Nat := 4983230072969 + 3 ^ 40 * 6369713 * 2
def baseEnd_6369713 : Nat := 3270724400192342202293729

theorem tailTrace_6369713 : CollatzResearch.WordTrace tailWord_6369713 prefixEnd_6369713 3270724400192342202293729 := by
  unfold tailWord_6369713
  simp only [CollatzResearch.WordTrace]
  refine ⟨232322519172625136216521793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154881679448416757477681195 232322519172625136216521793)
  ·
    refine ⟨174241889379468852162391345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232322519172625136216521793 174241889379468852162391345)
    ·
      refine ⟨130681417034601639121793509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174241889379468852162391345 130681417034601639121793509)
      ·
        refine ⟨24502765693987807335336283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130681417034601639121793509 24502765693987807335336283)
        ·
          refine ⟨36754148540981711003004425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24502765693987807335336283 36754148540981711003004425)
          ·
            refine ⟨27565611405736283252253319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36754148540981711003004425 27565611405736283252253319)
            ·
              refine ⟨41348417108604424878379979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27565611405736283252253319 41348417108604424878379979)
              ·
                refine ⟨62022625662906637317569969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41348417108604424878379979 62022625662906637317569969)
                ·
                  refine ⟨46516969247179977988177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62022625662906637317569969 46516969247179977988177477)
                  ·
                    refine ⟨8721931733846245872783277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46516969247179977988177477 8721931733846245872783277)
                    ·
                      refine ⟨3270724400192342202293729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8721931733846245872783277 3270724400192342202293729)
                      ·
                        rfl

theorem cell23_6369713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6369713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369713 prefixEnd_6369713 := by exact prefixLift 6369713
  have htrace : WordTrace (prefixWord ++ tailWord_6369713) baseStart_6369713 baseEnd_6369713 := by
    simpa [prefixWord, tailWord_6369713, baseEnd_6369713] using wordTrace_append hprefix tailTrace_6369713
  have hstable : (prefixWord ++ tailWord_6369713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369713).length < 2 ^ (prefixWord ++ tailWord_6369713).sum := by decide
  have hdescent : baseEnd_6369713 < baseStart_6369713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369820 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6369820 : Nat := 118140960795 + 6369820 * 2 ^ 59
def prefixEnd_6369820 : Nat := 4983230072969 + 3 ^ 40 * 6369820 * 2
def baseEnd_6369820 : Nat := 3270779342622373283655737

theorem tailTrace_6369820 : CollatzResearch.WordTrace tailWord_6369820 prefixEnd_6369820 3270779342622373283655737 := by
  unfold tailWord_6369820
  simp only [CollatzResearch.WordTrace]
  refine ⟨116163210891618746745333457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154884281188824995660444609 116163210891618746745333457)
  ·
    refine ⟨87122408168714060059000093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116163210891618746745333457 87122408168714060059000093)
    ·
      refine ⟨32670903063267772522125035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87122408168714060059000093 32670903063267772522125035)
      ·
        refine ⟨49006354594901658783187553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32670903063267772522125035 49006354594901658783187553)
        ·
          refine ⟨36754765946176244087390665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49006354594901658783187553 36754765946176244087390665)
          ·
            refine ⟨27566074459632183065542999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36754765946176244087390665 27566074459632183065542999)
            ·
              refine ⟨41349111689448274598314499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27566074459632183065542999 41349111689448274598314499)
              ·
                refine ⟨62023667534172411897471749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41349111689448274598314499 62023667534172411897471749)
                ·
                  refine ⟨11629437662657327230775953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62023667534172411897471749 11629437662657327230775953)
                  ·
                    refine ⟨8722078246992995423081965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11629437662657327230775953 8722078246992995423081965)
                    ·
                      refine ⟨3270779342622373283655737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8722078246992995423081965 3270779342622373283655737)
                      ·
                        rfl

theorem cell23_6369820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6369820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369820 prefixEnd_6369820 := by exact prefixLift 6369820
  have htrace : WordTrace (prefixWord ++ tailWord_6369820) baseStart_6369820 baseEnd_6369820 := by
    simpa [prefixWord, tailWord_6369820, baseEnd_6369820] using wordTrace_append hprefix tailTrace_6369820
  have hstable : (prefixWord ++ tailWord_6369820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369820).length < 2 ^ (prefixWord ++ tailWord_6369820).sum := by decide
  have hdescent : baseEnd_6369820 < baseStart_6369820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369823 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 6]
def baseStart_6369823 : Nat := 118140960795 + 6369823 * 2 ^ 59
def prefixEnd_6369823 : Nat := 4983230072969 + 3 ^ 40 * 6369823 * 2
def baseEnd_6369823 : Nat := 363420098118259641324247

theorem tailTrace_6369823 : CollatzResearch.WordTrace tailWord_6369823 prefixEnd_6369823 363420098118259641324247 := by
  unfold tailWord_6369823
  simp only [CollatzResearch.WordTrace]
  refine ⟨232326531202226625003026123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154884354134817750002017415 232326531202226625003026123)
  ·
    refine ⟨348489796803339937504539185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232326531202226625003026123 348489796803339937504539185)
    ·
      refine ⟨261367347602504953128404389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348489796803339937504539185 261367347602504953128404389)
      ·
        refine ⟨49006377675469678711575823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261367347602504953128404389 49006377675469678711575823)
        ·
          refine ⟨73509566513204518067363735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49006377675469678711575823 73509566513204518067363735)
          ·
            refine ⟨110264349769806777101045603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73509566513204518067363735 110264349769806777101045603)
            ·
              refine ⟨165396524654710165651568405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110264349769806777101045603 165396524654710165651568405)
              ·
                refine ⟨7752962093189539014917269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165396524654710165651568405 7752962093189539014917269)
                ·
                  refine ⟨363420098118259641324247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7752962093189539014917269 363420098118259641324247)
                  ·
                    rfl

theorem cell23_6369823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 6].length) (baseStart_6369823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369823 prefixEnd_6369823 := by exact prefixLift 6369823
  have htrace : WordTrace (prefixWord ++ tailWord_6369823) baseStart_6369823 baseEnd_6369823 := by
    simpa [prefixWord, tailWord_6369823, baseEnd_6369823] using wordTrace_append hprefix tailTrace_6369823
  have hstable : (prefixWord ++ tailWord_6369823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369823).length < 2 ^ (prefixWord ++ tailWord_6369823).sum := by decide
  have hdescent : baseEnd_6369823 < baseStart_6369823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369827 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 3, 4]
def baseStart_6369827 : Nat := 118140960795 + 6369827 * 2 ^ 59
def prefixEnd_6369827 : Nat := 4983230072969 + 3 ^ 40 * 6369827 * 2
def baseEnd_6369827 : Nat := 1090260978995651585422735

theorem tailTrace_6369827 : CollatzResearch.WordTrace tailWord_6369827 prefixEnd_6369827 1090260978995651585422735 := by
  unfold tailWord_6369827
  simp only [CollatzResearch.WordTrace]
  refine ⟨232326677094212133686171735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154884451396141422457447823 232326677094212133686171735)
  ·
    refine ⟨348490015641318200529257603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232326677094212133686171735 348490015641318200529257603)
    ·
      refine ⟨522735023461977300793886405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348490015641318200529257603 522735023461977300793886405)
      ·
        refine ⟨98012816899120743898853701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 522735023461977300793886405 98012816899120743898853701)
        ·
          refine ⟨18377403168585139481035069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98012816899120743898853701 18377403168585139481035069)
          ·
            refine ⟨6891526188219427305388151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18377403168585139481035069 6891526188219427305388151)
            ·
              refine ⟨10337289282329140958082227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891526188219427305388151 10337289282329140958082227)
              ·
                refine ⟨15505933923493711437123341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10337289282329140958082227 15505933923493711437123341)
                ·
                  refine ⟨5814725221310141788921253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15505933923493711437123341 5814725221310141788921253)
                  ·
                    refine ⟨1090260978995651585422735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814725221310141788921253 1090260978995651585422735)
                    ·
                      rfl

theorem cell23_6369827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 4].length) (baseStart_6369827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369827 prefixEnd_6369827 := by exact prefixLift 6369827
  have htrace : WordTrace (prefixWord ++ tailWord_6369827) baseStart_6369827 baseEnd_6369827 := by
    simpa [prefixWord, tailWord_6369827, baseEnd_6369827] using wordTrace_append hprefix tailTrace_6369827
  have hstable : (prefixWord ++ tailWord_6369827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369827).length < 2 ^ (prefixWord ++ tailWord_6369827).sum := by decide
  have hdescent : baseEnd_6369827 < baseStart_6369827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369840 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 6]
def baseStart_6369840 : Nat := 118140960795 + 6369840 * 2 ^ 59
def prefixEnd_6369840 : Nat := 4983230072969 + 3 ^ 40 * 6369840 * 2
def baseEnd_6369840 : Nat := 363421068026162578378405

theorem tailTrace_6369840 : CollatzResearch.WordTrace tailWord_6369840 prefixEnd_6369840 363421068026162578378405 := by
  unfold tailWord_6369840
  simp only [CollatzResearch.WordTrace]
  refine ⟨116163575621582518453197487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154884767495443357937596649 116163575621582518453197487)
  ·
    refine ⟨174245363432373777679796231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116163575621582518453197487 174245363432373777679796231)
    ·
      refine ⟨261368045148560666519694347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174245363432373777679796231 261368045148560666519694347)
      ·
        refine ⟨392052067722840999779541521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261368045148560666519694347 392052067722840999779541521)
        ·
          refine ⟨294039050792130749834656141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392052067722840999779541521 294039050792130749834656141)
          ·
            refine ⟨110264644047049031187996053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294039050792130749834656141 110264644047049031187996053)
            ·
              refine ⟨5168655189705423336937315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110264644047049031187996053 5168655189705423336937315)
              ·
                refine ⟨7752982784558135005405973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168655189705423336937315 7752982784558135005405973)
                ·
                  refine ⟨363421068026162578378405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7752982784558135005405973 363421068026162578378405)
                  ·
                    rfl

theorem cell23_6369840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_6369840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369840 prefixEnd_6369840 := by exact prefixLift 6369840
  have htrace : WordTrace (prefixWord ++ tailWord_6369840) baseStart_6369840 baseEnd_6369840 := by
    simpa [prefixWord, tailWord_6369840, baseEnd_6369840] using wordTrace_append hprefix tailTrace_6369840
  have hstable : (prefixWord ++ tailWord_6369840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369840).length < 2 ^ (prefixWord ++ tailWord_6369840).sum := by decide
  have hdescent : baseEnd_6369840 < baseStart_6369840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369870 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_6369870 : Nat := 118140960795 + 6369870 * 2 ^ 59
def prefixEnd_6369870 : Nat := 4983230072969 + 3 ^ 40 * 6369870 * 2
def baseEnd_6369870 : Nat := 1090268338885032696010169

theorem tailTrace_6369870 : CollatzResearch.WordTrace tailWord_6369870 prefixEnd_6369870 1090268338885032696010169 := by
  unfold tailWord_6369870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29041030679132044003748383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154885496955370901353324709 29041030679132044003748383)
  ·
    refine ⟨43561546018698066005622575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29041030679132044003748383 43561546018698066005622575)
    ·
      refine ⟨65342319028047099008433863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43561546018698066005622575 65342319028047099008433863)
      ·
        refine ⟨98013478542070648512650795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65342319028047099008433863 98013478542070648512650795)
        ·
          refine ⟨147020217813105972768976193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98013478542070648512650795 147020217813105972768976193)
          ·
            refine ⟨110265163359829479576732145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147020217813105972768976193 110265163359829479576732145)
            ·
              refine ⟨82698872519872109682549109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110265163359829479576732145 82698872519872109682549109)
              ·
                refine ⟨7753019298738010282738979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82698872519872109682549109 7753019298738010282738979)
                ·
                  refine ⟨11629528948107015424108469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753019298738010282738979 11629528948107015424108469)
                  ·
                    refine ⟨1090268338885032696010169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11629528948107015424108469 1090268338885032696010169)
                    ·
                      rfl

theorem cell23_6369870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_6369870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369870 prefixEnd_6369870 := by exact prefixLift 6369870
  have htrace : WordTrace (prefixWord ++ tailWord_6369870) baseStart_6369870 baseEnd_6369870 := by
    simpa [prefixWord, tailWord_6369870, baseEnd_6369870] using wordTrace_append hprefix tailTrace_6369870
  have hstable : (prefixWord ++ tailWord_6369870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369870).length < 2 ^ (prefixWord ++ tailWord_6369870).sum := by decide
  have hdescent : baseEnd_6369870 < baseStart_6369870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369877 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6369877 : Nat := 118140960795 + 6369877 * 2 ^ 59
def prefixEnd_6369877 : Nat := 4983230072969 + 3 ^ 40 * 6369877 * 2
def baseEnd_6369877 : Nat := 3270808611019679560642975

theorem tailTrace_6369877 : CollatzResearch.WordTrace tailWord_6369877 prefixEnd_6369877 3270808611019679560642975 := by
  unfold tailWord_6369877
  simp only [CollatzResearch.WordTrace]
  refine ⟨232328500744030992225491885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154885667162687328150327923 232328500744030992225491885)
  ·
    refine ⟨87123187779011622084559457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232328500744030992225491885 87123187779011622084559457)
    ·
      refine ⟨65342390834258716563419593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87123187779011622084559457 65342390834258716563419593)
      ·
        refine ⟨49006793125694037422564695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65342390834258716563419593 49006793125694037422564695)
        ·
          refine ⟨73510189688541056133847043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49006793125694037422564695 73510189688541056133847043)
          ·
            refine ⟨110265284532811584200770565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73510189688541056133847043 110265284532811584200770565)
            ·
              refine ⟨20674740849902172037644481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110265284532811584200770565 20674740849902172037644481)
              ·
                refine ⟨15506055637426629028233361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20674740849902172037644481 15506055637426629028233361)
                ·
                  refine ⟨11629541728069971771175021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15506055637426629028233361 11629541728069971771175021)
                  ·
                    refine ⟨4361078148026239414190633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11629541728069971771175021 4361078148026239414190633)
                    ·
                      refine ⟨3270808611019679560642975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361078148026239414190633 3270808611019679560642975)
                      ·
                        rfl

theorem cell23_6369877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6369877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369877 prefixEnd_6369877 := by exact prefixLift 6369877
  have htrace : WordTrace (prefixWord ++ tailWord_6369877) baseStart_6369877 baseEnd_6369877 := by
    simpa [prefixWord, tailWord_6369877, baseEnd_6369877] using wordTrace_append hprefix tailTrace_6369877
  have hstable : (prefixWord ++ tailWord_6369877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369877).length < 2 ^ (prefixWord ++ tailWord_6369877).sum := by decide
  have hdescent : baseEnd_6369877 < baseStart_6369877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369903 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_6369903 : Nat := 118140960795 + 6369903 * 2 ^ 59
def prefixEnd_6369903 : Nat := 4983230072969 + 3 ^ 40 * 6369903 * 2
def baseEnd_6369903 : Nat := 3270821961516696458917855

theorem tailTrace_6369903 : CollatzResearch.WordTrace tailWord_6369903 prefixEnd_6369903 3270821961516696458917855 := by
  unfold tailWord_6369903
  simp only [CollatzResearch.WordTrace]
  refine ⟨232329449041936798665938363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154886299361291199110625575 232329449041936798665938363)
  ·
    refine ⟨348494173562905197998907545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232329449041936798665938363 348494173562905197998907545)
    ·
      refine ⟨261370630172178898499180659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348494173562905197998907545 261370630172178898499180659)
      ·
        refine ⟨392055945258268347748770989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261370630172178898499180659 392055945258268347748770989)
        ·
          refine ⟨147020979471850630405789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392055945258268347748770989 147020979471850630405789121)
          ·
            refine ⟨110265734603887972804341841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147020979471850630405789121 110265734603887972804341841)
            ·
              refine ⟨82699300952915979603256381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110265734603887972804341841 82699300952915979603256381)
              ·
                refine ⟨31012237857343492351221143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82699300952915979603256381 31012237857343492351221143)
                ·
                  refine ⟨46518356786015238526831715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31012237857343492351221143 46518356786015238526831715)
                  ·
                    refine ⟨69777535179022857790247573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46518356786015238526831715 69777535179022857790247573)
                    ·
                      refine ⟨3270821961516696458917855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69777535179022857790247573 3270821961516696458917855)
                      ·
                        rfl

theorem cell23_6369903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_6369903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369903 prefixEnd_6369903 := by exact prefixLift 6369903
  have htrace : WordTrace (prefixWord ++ tailWord_6369903) baseStart_6369903 baseEnd_6369903 := by
    simpa [prefixWord, tailWord_6369903, baseEnd_6369903] using wordTrace_append hprefix tailTrace_6369903
  have hstable : (prefixWord ++ tailWord_6369903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369903).length < 2 ^ (prefixWord ++ tailWord_6369903).sum := by decide
  have hdescent : baseEnd_6369903 < baseStart_6369903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369920 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_6369920 : Nat := 118140960795 + 6369920 * 2 ^ 59
def prefixEnd_6369920 : Nat := 4983230072969 + 3 ^ 40 * 6369920 * 2
def baseEnd_6369920 : Nat := 3270830690687822892405277

theorem tailTrace_6369920 : CollatzResearch.WordTrace tailWord_6369920 prefixEnd_6369920 3270830690687822892405277 := by
  unfold tailWord_6369920
  simp only [CollatzResearch.WordTrace]
  refine ⟨116165034541437605284653607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154886712721916807046204809 116165034541437605284653607)
  ·
    refine ⟨174247551812156407926980411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116165034541437605284653607 174247551812156407926980411)
    ·
      refine ⟨261371327718234611890470617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174247551812156407926980411 261371327718234611890470617)
      ·
        refine ⟨196028495788675958917852963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261371327718234611890470617 196028495788675958917852963)
        ·
          refine ⟨294042743683013938376779445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196028495788675958917852963 294042743683013938376779445)
          ·
            refine ⟨27566507220282556722823073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294042743683013938376779445 27566507220282556722823073)
            ·
              refine ⟨20674880415211917542117305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27566507220282556722823073 20674880415211917542117305)
              ·
                refine ⟨15506160311408938156587979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20674880415211917542117305 15506160311408938156587979)
                ·
                  refine ⟨23259240467113407234881969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15506160311408938156587979 23259240467113407234881969)
                  ·
                    refine ⟨17444430350335055426161477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23259240467113407234881969 17444430350335055426161477)
                    ·
                      refine ⟨3270830690687822892405277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17444430350335055426161477 3270830690687822892405277)
                      ·
                        rfl

theorem cell23_6369920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_6369920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369920 prefixEnd_6369920 := by exact prefixLift 6369920
  have htrace : WordTrace (prefixWord ++ tailWord_6369920) baseStart_6369920 baseEnd_6369920 := by
    simpa [prefixWord, tailWord_6369920, baseEnd_6369920] using wordTrace_append hprefix tailTrace_6369920
  have hstable : (prefixWord ++ tailWord_6369920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369920).length < 2 ^ (prefixWord ++ tailWord_6369920).sum := by decide
  have hdescent : baseEnd_6369920 < baseStart_6369920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369924 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_6369924 : Nat := 118140960795 + 6369924 * 2 ^ 59
def prefixEnd_6369924 : Nat := 4983230072969 + 3 ^ 40 * 6369924 * 2
def baseEnd_6369924 : Nat := 3270832744610440876755259

theorem tailTrace_6369924 : CollatzResearch.WordTrace tailWord_6369924 prefixEnd_6369924 3270832744610440876755259 := by
  unfold tailWord_6369924
  simp only [CollatzResearch.WordTrace]
  refine ⟨116165107487430359626226413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154886809983240479501635217 116165107487430359626226413)
  ·
    refine ⟨43561915307786384859834905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116165107487430359626226413 43561915307786384859834905)
    ·
      refine ⟨32671436480839788644876179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43561915307786384859834905 32671436480839788644876179)
      ·
        refine ⟨49007154721259682967314269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32671436480839788644876179 49007154721259682967314269)
        ·
          refine ⟨18377683020472381112742851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49007154721259682967314269 18377683020472381112742851)
          ·
            refine ⟨27566524530708571669114277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18377683020472381112742851 27566524530708571669114277)
            ·
              refine ⟨5168723349507857187958927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27566524530708571669114277 5168723349507857187958927)
              ·
                refine ⟨7753085024261785781938391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168723349507857187958927 7753085024261785781938391)
                ·
                  refine ⟨11629627536392678672907587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753085024261785781938391 11629627536392678672907587)
                  ·
                    refine ⟨17444441304589018009361381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11629627536392678672907587 17444441304589018009361381)
                    ·
                      refine ⟨3270832744610440876755259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17444441304589018009361381 3270832744610440876755259)
                      ·
                        rfl

theorem cell23_6369924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_6369924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369924 prefixEnd_6369924 := by exact prefixLift 6369924
  have htrace : WordTrace (prefixWord ++ tailWord_6369924) baseStart_6369924 baseEnd_6369924 := by
    simpa [prefixWord, tailWord_6369924, baseEnd_6369924] using wordTrace_append hprefix tailTrace_6369924
  have hstable : (prefixWord ++ tailWord_6369924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369924).length < 2 ^ (prefixWord ++ tailWord_6369924).sum := by decide
  have hdescent : baseEnd_6369924 < baseStart_6369924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369927 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_6369927 : Nat := 118140960795 + 6369927 * 2 ^ 59
def prefixEnd_6369927 : Nat := 4983230072969 + 3 ^ 40 * 6369927 * 2
def baseEnd_6369927 : Nat := 3270834285052404365017745

theorem tailTrace_6369927 : CollatzResearch.WordTrace tailWord_6369927 prefixEnd_6369927 3270834285052404365017745 := by
  unfold tailWord_6369927
  simp only [CollatzResearch.WordTrace]
  refine ⟨232330324393849850764812035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154886882929233233843208023 232330324393849850764812035)
  ·
    refine ⟨348495486590774776147218053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232330324393849850764812035 348495486590774776147218053)
    ·
      refine ⟨65342903735770270527603385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348495486590774776147218053 65342903735770270527603385)
      ·
        refine ⟨49007177801827702895702539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65342903735770270527603385 49007177801827702895702539)
        ·
          refine ⟨73510766702741554343553809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49007177801827702895702539 73510766702741554343553809)
          ·
            refine ⟨55133075027056165757665357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73510766702741554343553809 55133075027056165757665357)
            ·
              refine ⟨20674903135146062159124509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55133075027056165757665357 20674903135146062159124509)
              ·
                refine ⟨7753088675679773309671691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20674903135146062159124509 7753088675679773309671691)
                ·
                  refine ⟨11629633013519659964507537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753088675679773309671691 11629633013519659964507537)
                  ·
                    refine ⟨8722224760139744973380653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11629633013519659964507537 8722224760139744973380653)
                    ·
                      refine ⟨3270834285052404365017745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8722224760139744973380653 3270834285052404365017745)
                      ·
                        rfl

theorem cell23_6369927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_6369927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369927 prefixEnd_6369927 := by exact prefixLift 6369927
  have htrace : WordTrace (prefixWord ++ tailWord_6369927) baseStart_6369927 baseEnd_6369927 := by
    simpa [prefixWord, tailWord_6369927, baseEnd_6369927] using wordTrace_append hprefix tailTrace_6369927
  have hstable : (prefixWord ++ tailWord_6369927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369927).length < 2 ^ (prefixWord ++ tailWord_6369927).sum := by decide
  have hdescent : baseEnd_6369927 < baseStart_6369927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369930 : List Nat := [3, 1, 2, 3, 3, 1, 10]
def baseStart_6369930 : Nat := 118140960795 + 6369930 * 2 ^ 59
def prefixEnd_6369930 : Nat := 4983230072969 + 3 ^ 40 * 6369930 * 2
def baseEnd_6369930 : Nat := 40380689203634171028151

theorem tailTrace_6369930 : CollatzResearch.WordTrace tailWord_6369930 prefixEnd_6369930 40380689203634171028151 := by
  unfold tailWord_6369930
  simp only [CollatzResearch.WordTrace]
  refine ⟨58082608453209745569292811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154886955875225988184780829 58082608453209745569292811)
  ·
    refine ⟨87123912679814618353939217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58082608453209745569292811 87123912679814618353939217)
    ·
      refine ⟨65342934509860963765454413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87123912679814618353939217 65342934509860963765454413)
      ·
        refine ⟨24503600441197861412045405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65342934509860963765454413 24503600441197861412045405)
        ·
          refine ⟨9188850165449198029517027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24503600441197861412045405 9188850165449198029517027)
          ·
            refine ⟨13783275248173797044275541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188850165449198029517027 13783275248173797044275541)
            ·
              refine ⟨40380689203634171028151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13783275248173797044275541 40380689203634171028151)
              ·
                rfl

theorem cell23_6369930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 10].length) (baseStart_6369930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369930 prefixEnd_6369930 := by exact prefixLift 6369930
  have htrace : WordTrace (prefixWord ++ tailWord_6369930) baseStart_6369930 baseEnd_6369930 := by
    simpa [prefixWord, tailWord_6369930, baseEnd_6369930] using wordTrace_append hprefix tailTrace_6369930
  have hstable : (prefixWord ++ tailWord_6369930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369930).length < 2 ^ (prefixWord ++ tailWord_6369930).sum := by decide
  have hdescent : baseEnd_6369930 < baseStart_6369930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369975 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_6369975 : Nat := 118140960795 + 6369975 * 2 ^ 59
def prefixEnd_6369975 : Nat := 4983230072969 + 3 ^ 40 * 6369975 * 2
def baseEnd_6369975 : Nat := 3270858932123820177217525

theorem tailTrace_6369975 : CollatzResearch.WordTrace tailWord_6369975 prefixEnd_6369975 3270858932123820177217525 := by
  unfold tailWord_6369975
  simp only [CollatzResearch.WordTrace]
  refine ⟨232332075097675954962559379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154888050065117303308372919 232332075097675954962559379)
  ·
    refine ⟨348498112646513932443839069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232332075097675954962559379 348498112646513932443839069)
    ·
      refine ⟨130686792242442724666439651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348498112646513932443839069 130686792242442724666439651)
      ·
        refine ⟨196030188363664086999659477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130686792242442724666439651 196030188363664086999659477)
        ·
          refine ⟨4594457539773377039054519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196030188363664086999659477 4594457539773377039054519)
          ·
            refine ⟨6891686309660065558581779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594457539773377039054519 6891686309660065558581779)
            ·
              refine ⟨10337529464490098337872669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891686309660065558581779 10337529464490098337872669)
              ·
                refine ⟨3876573549183786876702251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10337529464490098337872669 3876573549183786876702251)
                ·
                  refine ⟨5814860323775680315053377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876573549183786876702251 5814860323775680315053377)
                  ·
                    refine ⟨4361145242831760236290033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814860323775680315053377 4361145242831760236290033)
                    ·
                      refine ⟨3270858932123820177217525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361145242831760236290033 3270858932123820177217525)
                      ·
                        rfl

theorem cell23_6369975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_6369975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369975 prefixEnd_6369975 := by exact prefixLift 6369975
  have htrace : WordTrace (prefixWord ++ tailWord_6369975) baseStart_6369975 baseEnd_6369975 := by
    simpa [prefixWord, tailWord_6369975, baseEnd_6369975] using wordTrace_append hprefix tailTrace_6369975
  have hstable : (prefixWord ++ tailWord_6369975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369975).length < 2 ^ (prefixWord ++ tailWord_6369975).sum := by decide
  have hdescent : baseEnd_6369975 < baseStart_6369975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6369984 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2]
def baseStart_6369984 : Nat := 118140960795 + 6369984 * 2 ^ 59
def prefixEnd_6369984 : Nat := 4983230072969 + 3 ^ 40 * 6369984 * 2
def baseEnd_6369984 : Nat := 3270863553449710642004983

theorem tailTrace_6369984 : CollatzResearch.WordTrace tailWord_6369984 prefixEnd_6369984 3270863553449710642004983 := by
  unfold tailWord_6369984
  simp only [CollatzResearch.WordTrace]
  refine ⟨116166201677321674749818503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154888268903095566333091337 116166201677321674749818503)
  ·
    refine ⟨174249302515982512124727755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116166201677321674749818503 174249302515982512124727755)
    ·
      refine ⟨261373953773973768187091633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174249302515982512124727755 261373953773973768187091633)
      ·
        refine ⟨196030465330480326140318725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261373953773973768187091633 196030465330480326140318725)
        ·
          refine ⟨36755712249465061151309761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196030465330480326140318725 36755712249465061151309761)
          ·
            refine ⟨27566784187098795863482321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36755712249465061151309761 27566784187098795863482321)
            ·
              refine ⟨20675088140324096897611741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27566784187098795863482321 20675088140324096897611741)
              ·
                refine ⟨7753158052621536336604403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20675088140324096897611741 7753158052621536336604403)
                ·
                  refine ⟨11629737078932304504906605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753158052621536336604403 11629737078932304504906605)
                  ·
                    refine ⟨4361151404599614189339977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11629737078932304504906605 4361151404599614189339977)
                    ·
                      refine ⟨3270863553449710642004983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361151404599614189339977 3270863553449710642004983)
                      ·
                        rfl

theorem cell23_6369984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_6369984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6369984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6369984 prefixEnd_6369984 := by exact prefixLift 6369984
  have htrace : WordTrace (prefixWord ++ tailWord_6369984) baseStart_6369984 baseEnd_6369984 := by
    simpa [prefixWord, tailWord_6369984, baseEnd_6369984] using wordTrace_append hprefix tailTrace_6369984
  have hstable : (prefixWord ++ tailWord_6369984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6369984).length < 2 ^ (prefixWord ++ tailWord_6369984).sum := by decide
  have hdescent : baseEnd_6369984 < baseStart_6369984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6369984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370010 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_6370010 : Nat := 118140960795 + 6370010 * 2 ^ 59
def prefixEnd_6370010 : Nat := 4983230072969 + 3 ^ 40 * 6370010 * 2
def baseEnd_6370010 : Nat := 3270876903946727540279863

theorem tailTrace_6370010 : CollatzResearch.WordTrace tailWord_6370010 prefixEnd_6370010 3270876903946727540279863 := by
  unfold tailWord_6370010
  simp only [CollatzResearch.WordTrace]
  refine ⟨58083337913137288985020871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154888901101699437293388989 58083337913137288985020871)
  ·
    refine ⟨87125006869705933477531307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58083337913137288985020871 87125006869705933477531307)
    ·
      refine ⟨130687510304558900216296961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87125006869705933477531307 130687510304558900216296961)
      ·
        refine ⟨98015632728419175162222721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130687510304558900216296961 98015632728419175162222721)
        ·
          refine ⟨73511724546314381371667041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98015632728419175162222721 73511724546314381371667041)
          ·
            refine ⟨55133793409735786028750281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73511724546314381371667041 55133793409735786028750281)
            ·
              refine ⟨41350345057301839521562711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55133793409735786028750281 41350345057301839521562711)
              ·
                refine ⟨62025517585952759282344067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41350345057301839521562711 62025517585952759282344067)
                ·
                  refine ⟨93038276378929138923516101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62025517585952759282344067 93038276378929138923516101)
                  ·
                    refine ⟨17444676821049213548159269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93038276378929138923516101 17444676821049213548159269)
                    ·
                      refine ⟨3270876903946727540279863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17444676821049213548159269 3270876903946727540279863)
                      ·
                        rfl

theorem cell23_6370010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_6370010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370010 prefixEnd_6370010 := by exact prefixLift 6370010
  have htrace : WordTrace (prefixWord ++ tailWord_6370010) baseStart_6370010 baseEnd_6370010 := by
    simpa [prefixWord, tailWord_6370010, baseEnd_6370010] using wordTrace_append hprefix tailTrace_6370010
  have hstable : (prefixWord ++ tailWord_6370010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370010).length < 2 ^ (prefixWord ++ tailWord_6370010).sum := by decide
  have hdescent : baseEnd_6370010 < baseStart_6370010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370057 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 5, 2]
def baseStart_6370057 : Nat := 118140960795 + 6370057 * 2 ^ 59
def prefixEnd_6370057 : Nat := 4983230072969 + 3 ^ 40 * 6370057 * 2
def baseEnd_6370057 : Nat := 3270901037537488856392147

theorem tailTrace_6370057 : CollatzResearch.WordTrace tailWord_6370057 prefixEnd_6370057 3270901037537488856392147 := by
  unfold tailWord_6370057
  simp only [CollatzResearch.WordTrace]
  refine ⟨232335065883378882967044425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154890043922252588644696283 232335065883378882967044425)
  ·
    refine ⟨174251299412534162225283319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232335065883378882967044425 174251299412534162225283319)
    ·
      refine ⟨261376949118801243337924979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174251299412534162225283319 261376949118801243337924979)
      ·
        refine ⟨392065423678201865006887469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261376949118801243337924979 392065423678201865006887469)
        ·
          refine ⟨147024533879325699377582801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392065423678201865006887469 147024533879325699377582801)
          ·
            refine ⟨110268400409494274533187101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147024533879325699377582801 110268400409494274533187101)
            ·
              refine ⟨41350650153560352949945163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110268400409494274533187101 41350650153560352949945163)
              ·
                refine ⟨62025975230340529424917745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41350650153560352949945163 62025975230340529424917745)
                ·
                  refine ⟨46519481422755397068688309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62025975230340529424917745 46519481422755397068688309)
                  ·
                    refine ⟨4361201383383318475189529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46519481422755397068688309 4361201383383318475189529)
                    ·
                      refine ⟨3270901037537488856392147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361201383383318475189529 3270901037537488856392147)
                      ·
                        rfl

theorem cell23_6370057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5, 2].length) (baseStart_6370057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370057 prefixEnd_6370057 := by exact prefixLift 6370057
  have htrace : WordTrace (prefixWord ++ tailWord_6370057) baseStart_6370057 baseEnd_6370057 := by
    simpa [prefixWord, tailWord_6370057, baseEnd_6370057] using wordTrace_append hprefix tailTrace_6370057
  have hstable : (prefixWord ++ tailWord_6370057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370057).length < 2 ^ (prefixWord ++ tailWord_6370057).sum := by decide
  have hdescent : baseEnd_6370057 < baseStart_6370057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370097 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_6370097 : Nat := 118140960795 + 6370097 * 2 ^ 59
def prefixEnd_6370097 : Nat := 4983230072969 + 3 ^ 40 * 6370097 * 2
def baseEnd_6370097 : Nat := 1090307192254556233297321

theorem tailTrace_6370097 : CollatzResearch.WordTrace tailWord_6370097 prefixEnd_6370097 1090307192254556233297321 := by
  unfold tailWord_6370097
  simp only [CollatzResearch.WordTrace]
  refine ⟨232336524803233969798500545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154891016535489313199000363 232336524803233969798500545)
  ·
    refine ⟨174252393602425477348875409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232336524803233969798500545 174252393602425477348875409)
    ·
      refine ⟨130689295201819108011656557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174252393602425477348875409 130689295201819108011656557)
      ·
        refine ⟨49008485700682165504371209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130689295201819108011656557 49008485700682165504371209)
        ·
          refine ⟨36756364275511624128278407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49008485700682165504371209 36756364275511624128278407)
          ·
            refine ⟨55134546413267436192417611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36756364275511624128278407 55134546413267436192417611)
            ·
              refine ⟨82701819619901154288626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55134546413267436192417611 82701819619901154288626417)
              ·
                refine ⟨62026364714925865716469813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82701819619901154288626417 62026364714925865716469813)
                ·
                  refine ⟨5814971692024299910919045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62026364714925865716469813 5814971692024299910919045)
                  ·
                    refine ⟨1090307192254556233297321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814971692024299910919045 1090307192254556233297321)
                    ·
                      rfl

theorem cell23_6370097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_6370097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370097 prefixEnd_6370097 := by exact prefixLift 6370097
  have htrace : WordTrace (prefixWord ++ tailWord_6370097) baseStart_6370097 baseEnd_6370097 := by
    simpa [prefixWord, tailWord_6370097, baseEnd_6370097] using wordTrace_append hprefix tailTrace_6370097
  have hstable : (prefixWord ++ tailWord_6370097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370097).length < 2 ^ (prefixWord ++ tailWord_6370097).sum := by decide
  have hdescent : baseEnd_6370097 < baseStart_6370097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370148 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_6370148 : Nat := 118140960795 + 6370148 * 2 ^ 59
def prefixEnd_6370148 : Nat := 4983230072969 + 3 ^ 40 * 6370148 * 2
def baseEnd_6370148 : Nat := 1090315921425682666784743

theorem tailTrace_6370148 : CollatzResearch.WordTrace tailWord_6370148 prefixEnd_6370148 1090315921425682666784743 := by
  unfold tailWord_6370148
  simp only [CollatzResearch.WordTrace]
  refine ⟨116169192463024602754303549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154892256617366137005738065 116169192463024602754303549)
  ·
    refine ⟨43563447173634226032863831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116169192463024602754303549 43563447173634226032863831)
    ·
      refine ⟨65345170760451339049295747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43563447173634226032863831 65345170760451339049295747)
      ·
        refine ⟨98017756140677008573943621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65345170760451339049295747 98017756140677008573943621)
        ·
          refine ⟨18378329276376939107614429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98017756140677008573943621 18378329276376939107614429)
          ·
            refine ⟨6891873478641352165355411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18378329276376939107614429 6891873478641352165355411)
            ·
              refine ⟨10337810217962028248033117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891873478641352165355411 10337810217962028248033117)
              ·
                refine ⟨3876678831735760593012419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10337810217962028248033117 3876678831735760593012419)
                ·
                  refine ⟨5815018247603640889518629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876678831735760593012419 5815018247603640889518629)
                  ·
                    refine ⟨1090315921425682666784743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815018247603640889518629 1090315921425682666784743)
                    ·
                      rfl

theorem cell23_6370148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_6370148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370148 prefixEnd_6370148 := by exact prefixLift 6370148
  have htrace : WordTrace (prefixWord ++ tailWord_6370148) baseStart_6370148 baseEnd_6370148 := by
    simpa [prefixWord, tailWord_6370148, baseEnd_6370148] using wordTrace_append hprefix tailTrace_6370148
  have hstable : (prefixWord ++ tailWord_6370148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370148).length < 2 ^ (prefixWord ++ tailWord_6370148).sum := by decide
  have hdescent : baseEnd_6370148 < baseStart_6370148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370157 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_6370157 : Nat := 118140960795 + 6370157 * 2 ^ 59
def prefixEnd_6370157 : Nat := 4983230072969 + 3 ^ 40 * 6370157 * 2
def baseEnd_6370157 : Nat := 1090317461867646155047229

theorem tailTrace_6370157 : CollatzResearch.WordTrace tailWord_6370157 prefixEnd_6370157 1090317461867646155047229 := by
  unfold tailWord_6370157
  simp only [CollatzResearch.WordTrace]
  refine ⟨232338713183016600045684725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154892475455344400030456483 232338713183016600045684725)
  ·
    refine ⟨21781754360907806254282943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232338713183016600045684725 21781754360907806254282943)
    ·
      refine ⟨32672631541361709381424415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781754360907806254282943 32672631541361709381424415)
      ·
        refine ⟨49008947312042564072136623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32672631541361709381424415 49008947312042564072136623)
        ·
          refine ⟨73513420968063846108204935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49008947312042564072136623 73513420968063846108204935)
          ·
            refine ⟨110270131452095769162307403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73513420968063846108204935 110270131452095769162307403)
            ·
              refine ⟨165405197178143653743461105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110270131452095769162307403 165405197178143653743461105)
              ·
                refine ⟨124053897883607740307595829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165405197178143653743461105 124053897883607740307595829)
                ·
                  refine ⟨11630052926588225653837109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124053897883607740307595829 11630052926588225653837109)
                  ·
                    refine ⟨1090317461867646155047229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11630052926588225653837109 1090317461867646155047229)
                    ·
                      rfl

theorem cell23_6370157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_6370157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370157 prefixEnd_6370157 := by exact prefixLift 6370157
  have htrace : WordTrace (prefixWord ++ tailWord_6370157) baseStart_6370157 baseEnd_6370157 := by
    simpa [prefixWord, tailWord_6370157, baseEnd_6370157] using wordTrace_append hprefix tailTrace_6370157
  have hstable : (prefixWord ++ tailWord_6370157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370157).length < 2 ^ (prefixWord ++ tailWord_6370157).sum := by decide
  have hdescent : baseEnd_6370157 < baseStart_6370157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370171 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 1, 1, 3]
def baseStart_6370171 : Nat := 118140960795 + 6370171 * 2 ^ 59
def prefixEnd_6370171 : Nat := 4983230072969 + 3 ^ 40 * 6370171 * 2
def baseEnd_6370171 : Nat := 3270959574332101410366623

theorem tailTrace_6370171 : CollatzResearch.WordTrace tailWord_6370171 prefixEnd_6370171 3270959574332101410366623 := by
  unfold tailWord_6370171
  simp only [CollatzResearch.WordTrace]
  refine ⟨232339223804965880436694367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154892815869977253624462911 232339223804965880436694367)
  ·
    refine ⟨348508835707448820655041551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232339223804965880436694367 348508835707448820655041551)
    ·
      refine ⟨522763253561173230982562327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348508835707448820655041551 522763253561173230982562327)
      ·
        refine ⟨784144880341759846473843491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522763253561173230982562327 784144880341759846473843491)
        ·
          refine ⟨1176217320512639769710765237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784144880341759846473843491 1176217320512639769710765237)
          ·
            refine ⟨110270373798059978410384241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1176217320512639769710765237 110270373798059978410384241)
            ·
              refine ⟨82702780348544983807788181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110270373798059978410384241 82702780348544983807788181)
              ·
                refine ⟨3876692828838046115990071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82702780348544983807788181 3876692828838046115990071)
                ·
                  refine ⟨5815039243257069173985107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876692828838046115990071 5815039243257069173985107)
                  ·
                    refine ⟨8722558864885603760977661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815039243257069173985107 8722558864885603760977661)
                    ·
                      refine ⟨3270959574332101410366623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8722558864885603760977661 3270959574332101410366623)
                      ·
                        rfl

theorem cell23_6370171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 1, 3].length) (baseStart_6370171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370171 prefixEnd_6370171 := by exact prefixLift 6370171
  have htrace : WordTrace (prefixWord ++ tailWord_6370171) baseStart_6370171 baseEnd_6370171 := by
    simpa [prefixWord, tailWord_6370171, baseEnd_6370171] using wordTrace_append hprefix tailTrace_6370171
  have hstable : (prefixWord ++ tailWord_6370171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370171).length < 2 ^ (prefixWord ++ tailWord_6370171).sum := by decide
  have hdescent : baseEnd_6370171 < baseStart_6370171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370178 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6370178 : Nat := 118140960795 + 6370178 * 2 ^ 59
def prefixEnd_6370178 : Nat := 4983230072969 + 3 ^ 40 * 6370178 * 2
def baseEnd_6370178 : Nat := 363440352077409209219899

theorem tailTrace_6370178 : CollatzResearch.WordTrace tailWord_6370178 prefixEnd_6370178 363440352077409209219899 := by
  unfold tailWord_6370178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58084869778985130158049797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154892986077293680421466125 58084869778985130158049797)
  ·
    refine ⟨10890913083559711904634337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58084869778985130158049797 10890913083559711904634337)
    ·
      refine ⟨8168184812669783928475753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10890913083559711904634337 8168184812669783928475753)
      ·
        refine ⟨6126138609502337946356815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168184812669783928475753 6126138609502337946356815)
        ·
          refine ⟨9189207914253506919535223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126138609502337946356815 9189207914253506919535223)
          ·
            refine ⟨13783811871380260379302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189207914253506919535223 13783811871380260379302835)
            ·
              refine ⟨20675717807070390568954253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13783811871380260379302835 20675717807070390568954253)
              ·
                refine ⟨7753394177651396463357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20675717807070390568954253 7753394177651396463357845)
                ·
                  refine ⟨363440352077409209219899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7753394177651396463357845 363440352077409209219899)
                  ·
                    rfl

theorem cell23_6370178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6370178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370178 prefixEnd_6370178 := by exact prefixLift 6370178
  have htrace : WordTrace (prefixWord ++ tailWord_6370178) baseStart_6370178 baseEnd_6370178 := by
    simpa [prefixWord, tailWord_6370178, baseEnd_6370178] using wordTrace_append hprefix tailTrace_6370178
  have hstable : (prefixWord ++ tailWord_6370178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370178).length < 2 ^ (prefixWord ++ tailWord_6370178).sum := by decide
  have hdescent : baseEnd_6370178 < baseStart_6370178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370257 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6370257 : Nat := 118140960795 + 6370257 * 2 ^ 59
def prefixEnd_6370257 : Nat := 4983230072969 + 3 ^ 40 * 6370257 * 2
def baseEnd_6370257 : Nat := 3271003733668388073891227

theorem tailTrace_6370257 : CollatzResearch.WordTrace tailWord_6370257 prefixEnd_6370257 3271003733668388073891227 := by
  unfold tailWord_6370257
  simp only [CollatzResearch.WordTrace]
  refine ⟨232342360482654317124325025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154894906988436211416216683 232342360482654317124325025)
  ·
    refine ⟨174256770361990737843243769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232342360482654317124325025 174256770361990737843243769)
    ·
      refine ⟨130692577771493053382432827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174256770361990737843243769 130692577771493053382432827)
      ·
        refine ⟨196038866657239580073649241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130692577771493053382432827 196038866657239580073649241)
        ·
          refine ⟨147029149992929685055236931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196038866657239580073649241 147029149992929685055236931)
          ·
            refine ⟨220543724989394527582855397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147029149992929685055236931 220543724989394527582855397)
            ·
              refine ⟨41351948435511473921785387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220543724989394527582855397 41351948435511473921785387)
              ·
                refine ⟨62027922653267210882678081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41351948435511473921785387 62027922653267210882678081)
                ·
                  refine ⟨46520941989950408162008561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62027922653267210882678081 46520941989950408162008561)
                  ·
                    refine ⟨34890706492462806121506421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46520941989950408162008561 34890706492462806121506421)
                    ·
                      refine ⟨3271003733668388073891227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34890706492462806121506421 3271003733668388073891227)
                      ·
                        rfl

theorem cell23_6370257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6370257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370257 prefixEnd_6370257 := by exact prefixLift 6370257
  have htrace : WordTrace (prefixWord ++ tailWord_6370257) baseStart_6370257 baseEnd_6370257 := by
    simpa [prefixWord, tailWord_6370257, baseEnd_6370257] using wordTrace_append hprefix tailTrace_6370257
  have hstable : (prefixWord ++ tailWord_6370257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370257).length < 2 ^ (prefixWord ++ tailWord_6370257).sum := by decide
  have hdescent : baseEnd_6370257 < baseStart_6370257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370262 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6370262 : Nat := 118140960795 + 6370262 * 2 ^ 59
def prefixEnd_6370262 : Nat := 4983230072969 + 3 ^ 40 * 6370262 * 2
def baseEnd_6370262 : Nat := 3271006301071660554328705

theorem tailTrace_6370262 : CollatzResearch.WordTrace tailWord_6370262 prefixEnd_6370262 3271006301071660554328705 := by
  unfold tailWord_6370262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521408927977262686141065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154895028565090801985504693 14521408927977262686141065)
  ·
    refine ⟨10891056695982947014605799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14521408927977262686141065 10891056695982947014605799)
    ·
      refine ⟨16336585043974420521908699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10891056695982947014605799 16336585043974420521908699)
      ·
        refine ⟨24504877565961630782863049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16336585043974420521908699 24504877565961630782863049)
        ·
          refine ⟨18378658174471223087147287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24504877565961630782863049 18378658174471223087147287)
          ·
            refine ⟨27567987261706834630720931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18378658174471223087147287 27567987261706834630720931)
            ·
              refine ⟨41351980892560251946081397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27567987261706834630720931 41351980892560251946081397)
              ·
                refine ⟨3876748208677523619945131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41351980892560251946081397 3876748208677523619945131)
                ·
                  refine ⟨5815122313016285429917697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876748208677523619945131 5815122313016285429917697)
                  ·
                    refine ⟨4361341734762214072438273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5815122313016285429917697 4361341734762214072438273)
                    ·
                      refine ⟨3271006301071660554328705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361341734762214072438273 3271006301071660554328705)
                      ·
                        rfl

theorem cell23_6370262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6370262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370262 prefixEnd_6370262 := by exact prefixLift 6370262
  have htrace : WordTrace (prefixWord ++ tailWord_6370262) baseStart_6370262 baseEnd_6370262 := by
    simpa [prefixWord, tailWord_6370262, baseEnd_6370262] using wordTrace_append hprefix tailTrace_6370262
  have hstable : (prefixWord ++ tailWord_6370262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370262).length < 2 ^ (prefixWord ++ tailWord_6370262).sum := by decide
  have hdescent : baseEnd_6370262 < baseStart_6370262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370284 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_6370284 : Nat := 118140960795 + 6370284 * 2 ^ 59
def prefixEnd_6370284 : Nat := 4983230072969 + 3 ^ 40 * 6370284 * 2
def baseEnd_6370284 : Nat := 3271017597646059468253603

theorem tailTrace_6370284 : CollatzResearch.WordTrace tailWord_6370284 prefixEnd_6370284 3271017597646059468253603 := by
  unfold tailWord_6370284
  simp only [CollatzResearch.WordTrace]
  refine ⟨116171672626778250367778953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154895563502371000490371937 116171672626778250367778953)
  ·
    refine ⟨87128754470083687775834215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116171672626778250367778953 87128754470083687775834215)
    ·
      refine ⟨130693131705125531663751323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87128754470083687775834215 130693131705125531663751323)
      ·
        refine ⟨196039697557688297495626985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130693131705125531663751323 196039697557688297495626985)
        ·
          refine ⟨147029773168266223121720239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196039697557688297495626985 147029773168266223121720239)
          ·
            refine ⟨220544659752399334682580359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147029773168266223121720239 220544659752399334682580359)
            ·
              refine ⟨330816989628599002023870539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220544659752399334682580359 330816989628599002023870539)
              ·
                refine ⟨496225484442898503035805809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330816989628599002023870539 496225484442898503035805809)
                ·
                  refine ⟨372169113332173877276854357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496225484442898503035805809 372169113332173877276854357)
                  ·
                    refine ⟨4361356796861412624338137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 372169113332173877276854357 4361356796861412624338137)
                    ·
                      refine ⟨3271017597646059468253603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361356796861412624338137 3271017597646059468253603)
                      ·
                        rfl

theorem cell23_6370284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_6370284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370284 prefixEnd_6370284 := by exact prefixLift 6370284
  have htrace : WordTrace (prefixWord ++ tailWord_6370284) baseStart_6370284 baseEnd_6370284 := by
    simpa [prefixWord, tailWord_6370284, baseEnd_6370284] using wordTrace_append hprefix tailTrace_6370284
  have hstable : (prefixWord ++ tailWord_6370284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370284).length < 2 ^ (prefixWord ++ tailWord_6370284).sum := by decide
  have hdescent : baseEnd_6370284 < baseStart_6370284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370318 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6370318 : Nat := 118140960795 + 6370318 * 2 ^ 59
def prefixEnd_6370318 : Nat := 4983230072969 + 3 ^ 40 * 6370318 * 2
def baseEnd_6370318 : Nat := 3271035055988312335228447

theorem tailTrace_6370318 : CollatzResearch.WordTrace tailWord_6370318 prefixEnd_6370318 3271035055988312335228447 := by
  unfold tailWord_6370318
  simp only [CollatzResearch.WordTrace]
  refine ⟨29043073166929165567786951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154896390223622216361530405 29043073166929165567786951)
  ·
    refine ⟨43564609750393748351680427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29043073166929165567786951 43564609750393748351680427)
    ·
      refine ⟨65346914625590622527520641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43564609750393748351680427 65346914625590622527520641)
      ·
        refine ⟨49010185969192966895640481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65346914625590622527520641 49010185969192966895640481)
        ·
          refine ⟨36757639476894725171730361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49010185969192966895640481 36757639476894725171730361)
          ·
            refine ⟨27568229607671043878797771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36757639476894725171730361 27568229607671043878797771)
            ·
              refine ⟨41352344411506565818196657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27568229607671043878797771 41352344411506565818196657)
              ·
                refine ⟨31014258308629924363647493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41352344411506565818196657 31014258308629924363647493)
                ·
                  refine ⟨5815173432868110818183905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31014258308629924363647493 5815173432868110818183905)
                  ·
                    refine ⟨4361380074651083113637929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5815173432868110818183905 4361380074651083113637929)
                    ·
                      refine ⟨3271035055988312335228447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361380074651083113637929 3271035055988312335228447)
                      ·
                        rfl

theorem cell23_6370318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6370318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370318 prefixEnd_6370318 := by exact prefixLift 6370318
  have htrace : WordTrace (prefixWord ++ tailWord_6370318) baseStart_6370318 baseEnd_6370318 := by
    simpa [prefixWord, tailWord_6370318, baseEnd_6370318] using wordTrace_append hprefix tailTrace_6370318
  have hstable : (prefixWord ++ tailWord_6370318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370318).length < 2 ^ (prefixWord ++ tailWord_6370318).sum := by decide
  have hdescent : baseEnd_6370318 < baseStart_6370318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370354 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_6370354 : Nat := 118140960795 + 6370354 * 2 ^ 59
def prefixEnd_6370354 : Nat := 4983230072969 + 3 ^ 40 * 6370354 * 2
def baseEnd_6370354 : Nat := 1090351180430624731459427

theorem tailTrace_6370354 : CollatzResearch.WordTrace tailWord_6370354 prefixEnd_6370354 1090351180430624731459427 := by
  unfold tailWord_6370354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58086474590825725672651529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154897265575535268460404077 58086474590825725672651529)
  ·
    refine ⟨43564855943119294254488647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58086474590825725672651529 43564855943119294254488647)
    ·
      refine ⟨65347283914678941381732971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43564855943119294254488647 65347283914678941381732971)
      ·
        refine ⟨98020925872018412072599457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65347283914678941381732971 98020925872018412072599457)
        ·
          refine ⟨73515694404013809054449593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98020925872018412072599457 73515694404013809054449593)
          ·
            refine ⟨55136770803010356790837195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73515694404013809054449593 55136770803010356790837195)
            ·
              refine ⟨82705156204515535186255793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55136770803010356790837195 82705156204515535186255793)
              ·
                refine ⟨62028867153386651389691845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82705156204515535186255793 62028867153386651389691845)
                ·
                  refine ⟨11630412591259997135567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62028867153386651389691845 11630412591259997135567221)
                  ·
                    refine ⟨1090351180430624731459427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11630412591259997135567221 1090351180430624731459427)
                    ·
                      rfl

theorem cell23_6370354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_6370354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370354 prefixEnd_6370354 := by exact prefixLift 6370354
  have htrace : WordTrace (prefixWord ++ tailWord_6370354) baseStart_6370354 baseEnd_6370354 := by
    simpa [prefixWord, tailWord_6370354, baseEnd_6370354] using wordTrace_append hprefix tailTrace_6370354
  have hstable : (prefixWord ++ tailWord_6370354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370354).length < 2 ^ (prefixWord ++ tailWord_6370354).sum := by decide
  have hdescent : baseEnd_6370354 < baseStart_6370354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370381 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6370381 : Nat := 118140960795 + 6370381 * 2 ^ 59
def prefixEnd_6370381 : Nat := 4983230072969 + 3 ^ 40 * 6370381 * 2
def baseEnd_6370381 : Nat := 3271067405269545588740657

theorem tailTrace_6370381 : CollatzResearch.WordTrace tailWord_6370381 prefixEnd_6370381 3271067405269545588740657 := by
  unfold tailWord_6370381
  simp only [CollatzResearch.WordTrace]
  refine ⟨232346883134205086301838997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154897922089470057534559331 232346883134205086301838997)
  ·
    refine ⟨10891260146915863420398703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232346883134205086301838997 10891260146915863420398703)
    ·
      refine ⟨16336890220373795130598055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10891260146915863420398703 16336890220373795130598055)
      ·
        refine ⟨24505335330560692695897083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16336890220373795130598055 24505335330560692695897083)
        ·
          refine ⟨36758002995841039043845625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24505335330560692695897083 36758002995841039043845625)
          ·
            refine ⟨27568502246880779282884219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36758002995841039043845625 27568502246880779282884219)
            ·
              refine ⟨41352753370321168924326329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27568502246880779282884219 41352753370321168924326329)
              ·
                refine ⟨31014565027740876693244747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41352753370321168924326329 31014565027740876693244747)
                ·
                  refine ⟨46521847541611315039867121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31014565027740876693244747 46521847541611315039867121)
                  ·
                    refine ⟨34891385656208486279900341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46521847541611315039867121 34891385656208486279900341)
                    ·
                      refine ⟨3271067405269545588740657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34891385656208486279900341 3271067405269545588740657)
                      ·
                        rfl

theorem cell23_6370381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6370381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370381 prefixEnd_6370381 := by exact prefixLift 6370381
  have htrace : WordTrace (prefixWord ++ tailWord_6370381) baseStart_6370381 baseEnd_6370381 := by
    simpa [prefixWord, tailWord_6370381, baseEnd_6370381] using wordTrace_append hprefix tailTrace_6370381
  have hstable : (prefixWord ++ tailWord_6370381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370381).length < 2 ^ (prefixWord ++ tailWord_6370381).sum := by decide
  have hdescent : baseEnd_6370381 < baseStart_6370381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370391 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_6370391 : Nat := 118140960795 + 6370391 * 2 ^ 59
def prefixEnd_6370391 : Nat := 4983230072969 + 3 ^ 40 * 6370391 * 2
def baseEnd_6370391 : Nat := 3271072540076090549615611

theorem tailTrace_6370391 : CollatzResearch.WordTrace tailWord_6370391 prefixEnd_6370391 3271072540076090549615611 := by
  unfold tailWord_6370391
  simp only [CollatzResearch.WordTrace]
  refine ⟨232347247864168858009703027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154898165242779238673135351 232347247864168858009703027)
  ·
    refine ⟨348520871796253287014554541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232347247864168858009703027 348520871796253287014554541)
    ·
      refine ⟨130695326923594982630457953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348520871796253287014554541 130695326923594982630457953)
      ·
        refine ⟨98021495192696236972843465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130695326923594982630457953 98021495192696236972843465)
        ·
          refine ⟨73516121394522177729632599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98021495192696236972843465 73516121394522177729632599)
          ·
            refine ⟨110274182091783266594448899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73516121394522177729632599 110274182091783266594448899)
            ·
              refine ⟨165411273137674899891673349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110274182091783266594448899 165411273137674899891673349)
              ·
                refine ⟨31014613713314043729688753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165411273137674899891673349 31014613713314043729688753)
                ·
                  refine ⟨23260960284985532797266565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31014613713314043729688753 23260960284985532797266565)
                  ·
                    refine ⟨4361430053434787399487481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23260960284985532797266565 4361430053434787399487481)
                    ·
                      refine ⟨3271072540076090549615611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361430053434787399487481 3271072540076090549615611)
                      ·
                        rfl

theorem cell23_6370391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_6370391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370391 prefixEnd_6370391 := by exact prefixLift 6370391
  have htrace : WordTrace (prefixWord ++ tailWord_6370391) baseStart_6370391 baseEnd_6370391 := by
    simpa [prefixWord, tailWord_6370391, baseEnd_6370391] using wordTrace_append hprefix tailTrace_6370391
  have hstable : (prefixWord ++ tailWord_6370391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370391).length < 2 ^ (prefixWord ++ tailWord_6370391).sum := by decide
  have hdescent : baseEnd_6370391 < baseStart_6370391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370404 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_6370404 : Nat := 118140960795 + 6370404 * 2 ^ 59
def prefixEnd_6370404 : Nat := 4983230072969 + 3 ^ 40 * 6370404 * 2
def baseEnd_6370404 : Nat := 3271079215324598998753051

theorem tailTrace_6370404 : CollatzResearch.WordTrace tailWord_6370404 prefixEnd_6370404 3271079215324598998753051 := by
  unfold tailWord_6370404
  simp only [CollatzResearch.WordTrace]
  refine ⟨116173861006560880614963133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154898481342081174153284177 116173861006560880614963133)
  ·
    refine ⟨43565197877460330230611175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116173861006560880614963133 43565197877460330230611175)
    ·
      refine ⟨65347796816190495345916763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43565197877460330230611175 65347796816190495345916763)
      ·
        refine ⟨98021695224285743018875145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65347796816190495345916763 98021695224285743018875145)
        ·
          refine ⟨73516271418214307264156359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98021695224285743018875145 73516271418214307264156359)
          ·
            refine ⟨110274407127321460896234539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73516271418214307264156359 110274407127321460896234539)
            ·
              refine ⟨165411610690982191344351809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110274407127321460896234539 165411610690982191344351809)
              ·
                refine ⟨124058708018236643508263857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165411610690982191344351809 124058708018236643508263857)
                ·
                  refine ⟨93044031013677482631197893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124058708018236643508263857 93044031013677482631197893)
                  ·
                    refine ⟨17445755815064527993349605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93044031013677482631197893 17445755815064527993349605)
                    ·
                      refine ⟨3271079215324598998753051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17445755815064527993349605 3271079215324598998753051)
                      ·
                        rfl

theorem cell23_6370404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_6370404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370404 prefixEnd_6370404 := by exact prefixLift 6370404
  have htrace : WordTrace (prefixWord ++ tailWord_6370404) baseStart_6370404 baseEnd_6370404 := by
    simpa [prefixWord, tailWord_6370404, baseEnd_6370404] using wordTrace_append hprefix tailTrace_6370404
  have hstable : (prefixWord ++ tailWord_6370404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370404).length < 2 ^ (prefixWord ++ tailWord_6370404).sum := by decide
  have hdescent : baseEnd_6370404 < baseStart_6370404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370425 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 2, 1, 4]
def baseStart_6370425 : Nat := 118140960795 + 6370425 * 2 ^ 59
def prefixEnd_6370425 : Nat := 4983230072969 + 3 ^ 40 * 6370425 * 2
def baseEnd_6370425 : Nat := 3271089998418343416590455

theorem tailTrace_6370425 : CollatzResearch.WordTrace tailWord_6370425 prefixEnd_6370425 3271089998418343416590455 := by
  unfold tailWord_6370425
  simp only [CollatzResearch.WordTrace]
  refine ⟨232348487946045681816440729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154898991964030454544293819 232348487946045681816440729)
  ·
    refine ⟨174261365959534261362330547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232348487946045681816440729 174261365959534261362330547)
    ·
      refine ⟨261392048939301392043495821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174261365959534261362330547 261392048939301392043495821)
      ·
        refine ⟨98022018352238022016310933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261392048939301392043495821 98022018352238022016310933)
        ·
          refine ⟨4594782110261157282014575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98022018352238022016310933 4594782110261157282014575)
          ·
            refine ⟨6892173165391735923021863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594782110261157282014575 6892173165391735923021863)
            ·
              refine ⟨10338259748087603884532795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892173165391735923021863 10338259748087603884532795)
              ·
                refine ⟨15507389622131405826799193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338259748087603884532795 15507389622131405826799193)
                ·
                  refine ⟨11630542216598554370099395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15507389622131405826799193 11630542216598554370099395)
                  ·
                    refine ⟨17445813324897831555149093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11630542216598554370099395 17445813324897831555149093)
                    ·
                      refine ⟨3271089998418343416590455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17445813324897831555149093 3271089998418343416590455)
                      ·
                        rfl

theorem cell23_6370425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_6370425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370425 prefixEnd_6370425 := by exact prefixLift 6370425
  have htrace : WordTrace (prefixWord ++ tailWord_6370425) baseStart_6370425 baseEnd_6370425 := by
    simpa [prefixWord, tailWord_6370425, baseEnd_6370425] using wordTrace_append hprefix tailTrace_6370425
  have hstable : (prefixWord ++ tailWord_6370425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370425).length < 2 ^ (prefixWord ++ tailWord_6370425).sum := by decide
  have hdescent : baseEnd_6370425 < baseStart_6370425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370468 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_6370468 : Nat := 118140960795 + 6370468 * 2 ^ 59
def prefixEnd_6370468 : Nat := 4983230072969 + 3 ^ 40 * 6370468 * 2
def baseEnd_6370468 : Nat := 3271112078086486748352757

theorem tailTrace_6370468 : CollatzResearch.WordTrace tailWord_6370468 prefixEnd_6370468 3271112078086486748352757 := by
  unfold tailWord_6370468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116175028142444950080128029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154900037523259933440170705 116175028142444950080128029)
  ·
    refine ⟨43565635553416856280048011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116175028142444950080128029 43565635553416856280048011)
    ·
      refine ⟨65348453330125284420072017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43565635553416856280048011 65348453330125284420072017)
      ·
        refine ⟨49011339997593963315054013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65348453330125284420072017 49011339997593963315054013)
        ·
          refine ⟨18379252499097736243145255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49011339997593963315054013 18379252499097736243145255)
          ·
            refine ⟨27568878748646604364717883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18379252499097736243145255 27568878748646604364717883)
            ·
              refine ⟨41353318122969906547076825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27568878748646604364717883 41353318122969906547076825)
              ·
                refine ⟨31014988592227429910307619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41353318122969906547076825 31014988592227429910307619)
                ·
                  refine ⟨46522482888341144865461429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31014988592227429910307619 46522482888341144865461429)
                  ·
                    refine ⟨4361482770781982331137009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46522482888341144865461429 4361482770781982331137009)
                    ·
                      refine ⟨3271112078086486748352757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361482770781982331137009 3271112078086486748352757)
                      ·
                        rfl

theorem cell23_6370468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_6370468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370468 prefixEnd_6370468 := by exact prefixLift 6370468
  have htrace : WordTrace (prefixWord ++ tailWord_6370468) baseStart_6370468 baseEnd_6370468 := by
    simpa [prefixWord, tailWord_6370468, baseEnd_6370468] using wordTrace_append hprefix tailTrace_6370468
  have hstable : (prefixWord ++ tailWord_6370468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370468).length < 2 ^ (prefixWord ++ tailWord_6370468).sum := by decide
  have hdescent : baseEnd_6370468 < baseStart_6370468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370486 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6370486 : Nat := 118140960795 + 6370486 * 2 ^ 59
def prefixEnd_6370486 : Nat := 4983230072969 + 3 ^ 40 * 6370486 * 2
def baseEnd_6370486 : Nat := 1090373773579422559309225

theorem tailTrace_6370486 : CollatzResearch.WordTrace tailWord_6370486 prefixEnd_6370486 1090373773579422559309225 := by
  unfold tailWord_6370486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521919549926543077150707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154900475199216459489607541 14521919549926543077150707)
  ·
    refine ⟨21782879324889814615726061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521919549926543077150707 21782879324889814615726061)
    ·
      refine ⟨8168579746833680480897273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21782879324889814615726061 8168579746833680480897273)
      ·
        refine ⟨6126434810125260360672955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168579746833680480897273 6126434810125260360672955)
        ·
          refine ⟨9189652215187890541009433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126434810125260360672955 9189652215187890541009433)
          ·
            refine ⟨6892239161390917905757075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9189652215187890541009433 6892239161390917905757075)
            ·
              refine ⟨10338358742086376858635613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892239161390917905757075 10338358742086376858635613)
              ·
                refine ⟨3876884528282391321988355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10338358742086376858635613 3876884528282391321988355)
                ·
                  refine ⟨5815326792423586982982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876884528282391321988355 5815326792423586982982533)
                  ·
                    refine ⟨1090373773579422559309225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815326792423586982982533 1090373773579422559309225)
                    ·
                      rfl

theorem cell23_6370486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6370486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370486 prefixEnd_6370486 := by exact prefixLift 6370486
  have htrace : WordTrace (prefixWord ++ tailWord_6370486) baseStart_6370486 baseEnd_6370486 := by
    simpa [prefixWord, tailWord_6370486, baseEnd_6370486] using wordTrace_append hprefix tailTrace_6370486
  have hstable : (prefixWord ++ tailWord_6370486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370486).length < 2 ^ (prefixWord ++ tailWord_6370486).sum := by decide
  have hdescent : baseEnd_6370486 < baseStart_6370486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370492 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_6370492 : Nat := 118140960795 + 6370492 * 2 ^ 59
def prefixEnd_6370492 : Nat := 4983230072969 + 3 ^ 40 * 6370492 * 2
def baseEnd_6370492 : Nat := 3271124401622194654452647

theorem tailTrace_6370492 : CollatzResearch.WordTrace tailWord_6370492 prefixEnd_6370492 3271124401622194654452647 := by
  unfold tailWord_6370492
  simp only [CollatzResearch.WordTrace]
  refine ⟨116175465818401476129564865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154900621091201968172753153 116175465818401476129564865)
  ·
    refine ⟨87131599363801107097173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116175465818401476129564865 87131599363801107097173649)
    ·
      refine ⟨65348699522850830322880237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87131599363801107097173649 65348699522850830322880237)
      ·
        refine ⟨24505762321069061371080089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65348699522850830322880237 24505762321069061371080089)
        ·
          refine ⟨18379321740801796028310067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24505762321069061371080089 18379321740801796028310067)
          ·
            refine ⟨27568982611202694042465101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18379321740801796028310067 27568982611202694042465101)
            ·
              refine ⟨10338368479201010265924413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27568982611202694042465101 10338368479201010265924413)
              ·
                refine ⟨3876888179700378849721655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10338368479201010265924413 3876888179700378849721655)
                ·
                  refine ⟨5815332269550568274582483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876888179700378849721655 5815332269550568274582483)
                  ·
                    refine ⟨8722998404325852411873725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815332269550568274582483 8722998404325852411873725)
                    ·
                      refine ⟨3271124401622194654452647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8722998404325852411873725 3271124401622194654452647)
                      ·
                        rfl

theorem cell23_6370492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_6370492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370492 prefixEnd_6370492 := by exact prefixLift 6370492
  have htrace : WordTrace (prefixWord ++ tailWord_6370492) baseStart_6370492 baseEnd_6370492 := by
    simpa [prefixWord, tailWord_6370492, baseEnd_6370492] using wordTrace_append hprefix tailTrace_6370492
  have hstable : (prefixWord ++ tailWord_6370492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370492).length < 2 ^ (prefixWord ++ tailWord_6370492).sum := by decide
  have hdescent : baseEnd_6370492 < baseStart_6370492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370501 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_6370501 : Nat := 118140960795 + 6370501 * 2 ^ 59
def prefixEnd_6370501 : Nat := 4983230072969 + 3 ^ 40 * 6370501 * 2
def baseEnd_6370501 : Nat := 3271129022948085119240105

theorem tailTrace_6370501 : CollatzResearch.WordTrace tailWord_6370501 prefixEnd_6370501 3271129022948085119240105 := by
  unfold tailWord_6370501
  simp only [CollatzResearch.WordTrace]
  refine ⟨232351259893770346796207357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154900839929180231197471571 232351259893770346796207357)
  ·
    refine ⟨87131722460163880048577759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232351259893770346796207357 87131722460163880048577759)
    ·
      refine ⟨130697583690245820072866639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87131722460163880048577759 130697583690245820072866639)
      ·
        refine ⟨196046375535368730109299959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130697583690245820072866639 196046375535368730109299959)
        ·
          refine ⟨294069563303053095163949939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196046375535368730109299959 294069563303053095163949939)
          ·
            refine ⟨441104344954579642745924909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294069563303053095163949939 441104344954579642745924909)
            ·
              refine ⟨165414129357967366029721841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441104344954579642745924909 165414129357967366029721841)
              ·
                refine ⟨124060597018475524522291381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165414129357967366029721841 124060597018475524522291381)
                ·
                  refine ⟨11630680970482080423964817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124060597018475524522291381 11630680970482080423964817)
                  ·
                    refine ⟨8723010727861560317973613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11630680970482080423964817 8723010727861560317973613)
                    ·
                      refine ⟨3271129022948085119240105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723010727861560317973613 3271129022948085119240105)
                      ·
                        rfl

theorem cell23_6370501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_6370501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370501 prefixEnd_6370501 := by exact prefixLift 6370501
  have htrace : WordTrace (prefixWord ++ tailWord_6370501) baseStart_6370501 baseEnd_6370501 := by
    simpa [prefixWord, tailWord_6370501, baseEnd_6370501] using wordTrace_append hprefix tailTrace_6370501
  have hstable : (prefixWord ++ tailWord_6370501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370501).length < 2 ^ (prefixWord ++ tailWord_6370501).sum := by decide
  have hdescent : baseEnd_6370501 < baseStart_6370501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370504 : List Nat := [2, 1, 3, 1, 2, 1, 13]
def baseStart_6370504 : Nat := 118140960795 + 6370504 * 2 ^ 59
def prefixEnd_6370504 : Nat := 4983230072969 + 3 ^ 40 * 6370504 * 2
def baseEnd_6370504 : Nat := 40384327943087019845711

theorem tailTrace_6370504 : CollatzResearch.WordTrace tailWord_6370504 prefixEnd_6370504 40384327943087019845711 := by
  unfold tailWord_6370504
  simp only [CollatzResearch.WordTrace]
  refine ⟨116175684656379739154283283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154900912875172985539044377 116175684656379739154283283)
  ·
    refine ⟨174263526984569608731424925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116175684656379739154283283 174263526984569608731424925)
    ·
      refine ⟨65348822619213603274284347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174263526984569608731424925 65348822619213603274284347)
      ·
        refine ⟨98023233928820404911426521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65348822619213603274284347 98023233928820404911426521)
        ·
          refine ⟨73517425446615303683569891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98023233928820404911426521 73517425446615303683569891)
          ·
            refine ⟨110276138169922955525354837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73517425446615303683569891 110276138169922955525354837)
            ·
              refine ⟨40384327943087019845711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 110276138169922955525354837 40384327943087019845711)
              ·
                rfl

theorem cell23_6370504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 13].length) (baseStart_6370504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370504 prefixEnd_6370504 := by exact prefixLift 6370504
  have htrace : WordTrace (prefixWord ++ tailWord_6370504) baseStart_6370504 baseEnd_6370504 := by
    simpa [prefixWord, tailWord_6370504, baseEnd_6370504] using wordTrace_append hprefix tailTrace_6370504
  have hstable : (prefixWord ++ tailWord_6370504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370504).length < 2 ^ (prefixWord ++ tailWord_6370504).sum := by decide
  have hdescent : baseEnd_6370504 < baseStart_6370504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370535 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6370535 : Nat := 118140960795 + 6370535 * 2 ^ 59
def prefixEnd_6370535 : Nat := 4983230072969 + 3 ^ 40 * 6370535 * 2
def baseEnd_6370535 : Nat := 3271146481290337986214949

theorem tailTrace_6370535 : CollatzResearch.WordTrace tailWord_6370535 prefixEnd_6370535 3271146481290337986214949 := by
  unfold tailWord_6370535
  simp only [CollatzResearch.WordTrace]
  refine ⟨232352499975647170602945059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154901666650431447068630039 232352499975647170602945059)
  ·
    refine ⟨348528749963470755904417589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232352499975647170602945059 348528749963470755904417589)
    ·
      refine ⟨32674570309075383366039149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 348528749963470755904417589 32674570309075383366039149)
      ·
        refine ⟨12252963865903268762264681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32674570309075383366039149 12252963865903268762264681)
        ·
          refine ⟨9189722899427451571698511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12252963865903268762264681 9189722899427451571698511)
          ·
            refine ⟨13784584349141177357547767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189722899427451571698511 13784584349141177357547767)
            ·
              refine ⟨20676876523711766036321651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13784584349141177357547767 20676876523711766036321651)
              ·
                refine ⟨31015314785567649054482477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20676876523711766036321651 31015314785567649054482477)
                ·
                  refine ⟨11630743044587868395430929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31015314785567649054482477 11630743044587868395430929)
                  ·
                    refine ⟨8723057283440901296573197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11630743044587868395430929 8723057283440901296573197)
                    ·
                      refine ⟨3271146481290337986214949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723057283440901296573197 3271146481290337986214949)
                      ·
                        rfl

theorem cell23_6370535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6370535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370535 prefixEnd_6370535 := by exact prefixLift 6370535
  have htrace : WordTrace (prefixWord ++ tailWord_6370535) baseStart_6370535 baseEnd_6370535 := by
    simpa [prefixWord, tailWord_6370535, baseEnd_6370535] using wordTrace_append hprefix tailTrace_6370535
  have hstable : (prefixWord ++ tailWord_6370535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370535).length < 2 ^ (prefixWord ++ tailWord_6370535).sum := by decide
  have hdescent : baseEnd_6370535 < baseStart_6370535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
