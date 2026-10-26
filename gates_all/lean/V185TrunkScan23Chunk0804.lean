import V185TrunkScan23Chunk0803

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4755485 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4755485 : Nat := 118140960795 + 4755485 * 2 ^ 59
def prefixEnd_4755485 : Nat := 4983230072969 + 3 ^ 40 * 4755485 * 2
def baseEnd_4755485 : Nat := 2441849550246431876767429

theorem tailTrace_4755485 : CollatzResearch.WordTrace tailWord_4755485 prefixEnd_4755485 2441849550246431876767429 := by
  unfold tailWord_4755485
  simp only [CollatzResearch.WordTrace]
  refine ⟨173446787176697492022779909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115631191451131661348519939 173446787176697492022779909)
  ·
    refine ⟨32521272595630779754271233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173446787176697492022779909 32521272595630779754271233)
    ·
      refine ⟨24390954446723084815703425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32521272595630779754271233 24390954446723084815703425)
      ·
        refine ⟨18293215835042313611777569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24390954446723084815703425 18293215835042313611777569)
        ·
          refine ⟨13719911876281735208833177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18293215835042313611777569 13719911876281735208833177)
          ·
            refine ⟨10289933907211301406624883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13719911876281735208833177 10289933907211301406624883)
            ·
              refine ⟨15434900860816952109937325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10289933907211301406624883 15434900860816952109937325)
              ·
                refine ⟨5788087822806357041226497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15434900860816952109937325 5788087822806357041226497)
                ·
                  refine ⟨4341065867104767780919873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788087822806357041226497 4341065867104767780919873)
                  ·
                    refine ⟨3255799400328575835689905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341065867104767780919873 3255799400328575835689905)
                    ·
                      refine ⟨2441849550246431876767429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255799400328575835689905 2441849550246431876767429)
                      ·
                        rfl

theorem cell23_4755485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4755485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755485 prefixEnd_4755485 := by exact prefixLift 4755485
  have htrace : WordTrace (prefixWord ++ tailWord_4755485) baseStart_4755485 baseEnd_4755485 := by
    simpa [prefixWord, tailWord_4755485, baseEnd_4755485] using wordTrace_append hprefix tailTrace_4755485
  have hstable : (prefixWord ++ tailWord_4755485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755485).length < 2 ^ (prefixWord ++ tailWord_4755485).sum := by decide
  have hdescent : baseEnd_4755485 < baseStart_4755485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755504 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_4755504 : Nat := 118140960795 + 4755504 * 2 ^ 59
def prefixEnd_4755504 : Nat := 4983230072969 + 3 ^ 40 * 4755504 * 2
def baseEnd_4755504 : Nat := 813953102126289100809947

theorem tailTrace_4755504 : CollatzResearch.WordTrace tailWord_4755504 prefixEnd_4755504 813953102126289100809947 := by
  unfold tailWord_4755504
  simp only [CollatzResearch.WordTrace]
  refine ⟨86723740081814329133860783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115631653442419105511814377 86723740081814329133860783)
  ·
    refine ⟨130085610122721493700791175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86723740081814329133860783 130085610122721493700791175)
    ·
      refine ⟨195128415184082240551186763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130085610122721493700791175 195128415184082240551186763)
      ·
        refine ⟨292692622776123360826780145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195128415184082240551186763 292692622776123360826780145)
        ·
          refine ⟨219519467082092520620085109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292692622776123360826780145 219519467082092520620085109)
          ·
            refine ⟨20579950038946173808132979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219519467082092520620085109 20579950038946173808132979)
            ·
              refine ⟨30869925058419260712199469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20579950038946173808132979 30869925058419260712199469)
              ·
                refine ⟨11576221896907222767074801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30869925058419260712199469 11576221896907222767074801)
                ·
                  refine ⟨8682166422680417075306101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11576221896907222767074801 8682166422680417075306101)
                  ·
                    refine ⟨813953102126289100809947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8682166422680417075306101 813953102126289100809947)
                    ·
                      rfl

theorem cell23_4755504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_4755504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755504 prefixEnd_4755504 := by exact prefixLift 4755504
  have htrace : WordTrace (prefixWord ++ tailWord_4755504) baseStart_4755504 baseEnd_4755504 := by
    simpa [prefixWord, tailWord_4755504, baseEnd_4755504] using wordTrace_append hprefix tailTrace_4755504
  have hstable : (prefixWord ++ tailWord_4755504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755504).length < 2 ^ (prefixWord ++ tailWord_4755504).sum := by decide
  have hdescent : baseEnd_4755504 < baseStart_4755504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755521 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4755521 : Nat := 118140960795 + 4755521 * 2 ^ 59
def prefixEnd_4755521 : Nat := 4983230072969 + 3 ^ 40 * 4755521 * 2
def baseEnd_4755521 : Nat := 813956011849997911972421

theorem tailTrace_4755521 : CollatzResearch.WordTrace tailWord_4755521 prefixEnd_4755521 813956011849997911972421 := by
  unfold tailWord_4755521
  simp only [CollatzResearch.WordTrace]
  refine ⟨173448100204567070171090417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115632066803044713447393611 173448100204567070171090417)
  ·
    refine ⟨130086075153425302628317813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173448100204567070171090417 130086075153425302628317813)
    ·
      refine ⟨12195569545633622121404795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130086075153425302628317813 12195569545633622121404795)
      ·
        refine ⟨18293354318450433182107193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12195569545633622121404795 18293354318450433182107193)
        ·
          refine ⟨13720015738837824886580395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18293354318450433182107193 13720015738837824886580395)
          ·
            refine ⟨20580023608256737329870593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13720015738837824886580395 20580023608256737329870593)
            ·
              refine ⟨15435017706192552997402945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20580023608256737329870593 15435017706192552997402945)
              ·
                refine ⟨11576263279644414748052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15435017706192552997402945 11576263279644414748052209)
                ·
                  refine ⟨8682197459733311061039157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11576263279644414748052209 8682197459733311061039157)
                  ·
                    refine ⟨813956011849997911972421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8682197459733311061039157 813956011849997911972421)
                    ·
                      rfl

theorem cell23_4755521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4755521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755521 prefixEnd_4755521 := by exact prefixLift 4755521
  have htrace : WordTrace (prefixWord ++ tailWord_4755521) baseStart_4755521 baseEnd_4755521 := by
    simpa [prefixWord, tailWord_4755521, baseEnd_4755521] using wordTrace_append hprefix tailTrace_4755521
  have hstable : (prefixWord ++ tailWord_4755521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755521).length < 2 ^ (prefixWord ++ tailWord_4755521).sum := by decide
  have hdescent : baseEnd_4755521 < baseStart_4755521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755541 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4755541 : Nat := 118140960795 + 4755541 * 2 ^ 59
def prefixEnd_4755541 : Nat := 4983230072969 + 3 ^ 40 * 4755541 * 2
def baseEnd_4755541 : Nat := 2441878305163083657667171

theorem tailTrace_4755541 : CollatzResearch.WordTrace tailWord_4755541 prefixEnd_4755541 2441878305163083657667171 := by
  unfold tailWord_4755541
  simp only [CollatzResearch.WordTrace]
  refine ⟨173448829664494613586818477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115632553109663075724545651 173448829664494613586818477)
  ·
    refine ⟨65043311124185480095056929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173448829664494613586818477 65043311124185480095056929)
    ·
      refine ⟨48782483343139110071292697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65043311124185480095056929 48782483343139110071292697)
      ·
        refine ⟨36586862507354332553469523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48782483343139110071292697 36586862507354332553469523)
        ·
          refine ⟨54880293761031498830204285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36586862507354332553469523 54880293761031498830204285)
          ·
            refine ⟨20580110160386812061326607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54880293761031498830204285 20580110160386812061326607)
            ·
              refine ⟨30870165240580218091989911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20580110160386812061326607 30870165240580218091989911)
              ·
                refine ⟨46305247860870327137984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30870165240580218091989911 46305247860870327137984867)
                ·
                  refine ⟨69457871791305490706977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46305247860870327137984867 69457871791305490706977301)
                  ·
                    refine ⟨3255837740217444876889561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69457871791305490706977301 3255837740217444876889561)
                    ·
                      refine ⟨2441878305163083657667171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255837740217444876889561 2441878305163083657667171)
                      ·
                        rfl

theorem cell23_4755541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4755541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755541 prefixEnd_4755541 := by exact prefixLift 4755541
  have htrace : WordTrace (prefixWord ++ tailWord_4755541) baseStart_4755541 baseEnd_4755541 := by
    simpa [prefixWord, tailWord_4755541, baseEnd_4755541] using wordTrace_append hprefix tailTrace_4755541
  have hstable : (prefixWord ++ tailWord_4755541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755541).length < 2 ^ (prefixWord ++ tailWord_4755541).sum := by decide
  have hdescent : baseEnd_4755541 < baseStart_4755541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755568 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 1, 4]
def baseStart_4755568 : Nat := 118140960795 + 4755568 * 2 ^ 59
def prefixEnd_4755568 : Nat := 4983230072969 + 3 ^ 40 * 4755568 * 2
def baseEnd_4755568 : Nat := 813964056380251684009849

theorem tailTrace_4755568 : CollatzResearch.WordTrace tailWord_4755568 prefixEnd_4755568 813964056380251684009849 := by
  unfold tailWord_4755568
  simp only [CollatzResearch.WordTrace]
  refine ⟨86724907217698398599025679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115633209623597864798700905 86724907217698398599025679)
  ·
    refine ⟨130087360826547597898538519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86724907217698398599025679 130087360826547597898538519)
    ·
      refine ⟨195131041239821396847807779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130087360826547597898538519 195131041239821396847807779)
      ·
        refine ⟨292696561859732095271711669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195131041239821396847807779 292696561859732095271711669)
        ·
          refine ⟨27440302674349883931722969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292696561859732095271711669 27440302674349883931722969)
          ·
            refine ⟨20580227005762412948792227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27440302674349883931722969 20580227005762412948792227)
            ·
              refine ⟨30870340508643619423188341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20580227005762412948792227 30870340508643619423188341)
              ·
                refine ⟨2894094422685339320923907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30870340508643619423188341 2894094422685339320923907)
                ·
                  refine ⟨4341141634028008981385861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894094422685339320923907 4341141634028008981385861)
                  ·
                    refine ⟨813964056380251684009849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341141634028008981385861 813964056380251684009849)
                    ·
                      rfl

theorem cell23_4755568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_4755568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755568 prefixEnd_4755568 := by exact prefixLift 4755568
  have htrace : WordTrace (prefixWord ++ tailWord_4755568) baseStart_4755568 baseEnd_4755568 := by
    simpa [prefixWord, tailWord_4755568, baseEnd_4755568] using wordTrace_append hprefix tailTrace_4755568
  have hstable : (prefixWord ++ tailWord_4755568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755568).length < 2 ^ (prefixWord ++ tailWord_4755568).sum := by decide
  have hdescent : baseEnd_4755568 < baseStart_4755568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755581 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 6]
def baseStart_4755581 : Nat := 118140960795 + 4755581 * 2 ^ 59
def prefixEnd_4755581 : Nat := 4983230072969 + 3 ^ 40 * 4755581 * 2
def baseEnd_4755581 : Nat := 271322093821029277907443

theorem tailTrace_4755581 : CollatzResearch.WordTrace tailWord_4755581 prefixEnd_4755581 271322093821029277907443 := by
  unfold tailWord_4755581
  simp only [CollatzResearch.WordTrace]
  refine ⟨173450288584349700418274597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115633525722899800278849731 173450288584349700418274597)
  ·
    refine ⟨32521929109565568828426487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173450288584349700418274597 32521929109565568828426487)
    ·
      refine ⟨48782893664348353242639731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32521929109565568828426487 48782893664348353242639731)
      ·
        refine ⟨73174340496522529863959597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48782893664348353242639731 73174340496522529863959597)
        ·
          refine ⟨27440377686195948698984849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73174340496522529863959597 27440377686195948698984849)
          ·
            refine ⟨20580283264646961524238637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27440377686195948698984849 20580283264646961524238637)
            ·
              refine ⟨7717606224242610571589489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20580283264646961524238637 7717606224242610571589489)
              ·
                refine ⟨5788204668181957928692117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7717606224242610571589489 5788204668181957928692117)
                ·
                  refine ⟨271322093821029277907443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5788204668181957928692117 271322093821029277907443)
                  ·
                    rfl

theorem cell23_4755581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_4755581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755581 prefixEnd_4755581 := by exact prefixLift 4755581
  have htrace : WordTrace (prefixWord ++ tailWord_4755581) baseStart_4755581 baseEnd_4755581 := by
    simpa [prefixWord, tailWord_4755581, baseEnd_4755581] using wordTrace_append hprefix tailTrace_4755581
  have hstable : (prefixWord ++ tailWord_4755581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755581).length < 2 ^ (prefixWord ++ tailWord_4755581).sum := by decide
  have hdescent : baseEnd_4755581 < baseStart_4755581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755636 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4755636 : Nat := 118140960795 + 4755636 * 2 ^ 59
def prefixEnd_4755636 : Nat := 4983230072969 + 3 ^ 40 * 4755636 * 2
def baseEnd_4755636 : Nat := 813975695275086928659745

theorem tailTrace_4755636 : CollatzResearch.WordTrace tailWord_4755636 prefixEnd_4755636 813975695275086928659745 := by
  unfold tailWord_4755636
  simp only [CollatzResearch.WordTrace]
  refine ⟨86726147299575222405763381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115634863066100296541017841 86726147299575222405763381)
  ·
    refine ⟨8130576309335177100540317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86726147299575222405763381 8130576309335177100540317)
    ·
      refine ⟨3048966116000691412702619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8130576309335177100540317 3048966116000691412702619)
      ·
        refine ⟨4573449174001037119053929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048966116000691412702619 4573449174001037119053929)
        ·
          refine ⟨3430086880500777839290447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573449174001037119053929 3430086880500777839290447)
          ·
            refine ⟨5145130320751166758935671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430086880500777839290447 5145130320751166758935671)
            ·
              refine ⟨7717695481126750138403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145130320751166758935671 7717695481126750138403507)
              ·
                refine ⟨11576543221690125207605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7717695481126750138403507 11576543221690125207605261)
                ·
                  refine ⟨4341203708133796952851973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11576543221690125207605261 4341203708133796952851973)
                  ·
                    refine ⟨813975695275086928659745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341203708133796952851973 813975695275086928659745)
                    ·
                      rfl

theorem cell23_4755636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4755636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755636 prefixEnd_4755636 := by exact prefixLift 4755636
  have htrace : WordTrace (prefixWord ++ tailWord_4755636) baseStart_4755636 baseEnd_4755636 := by
    simpa [prefixWord, tailWord_4755636, baseEnd_4755636] using wordTrace_append hprefix tailTrace_4755636
  have hstable : (prefixWord ++ tailWord_4755636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755636).length < 2 ^ (prefixWord ++ tailWord_4755636).sum := by decide
  have hdescent : baseEnd_4755636 < baseStart_4755636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755641 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_4755641 : Nat := 118140960795 + 4755641 * 2 ^ 59
def prefixEnd_4755641 : Nat := 4983230072969 + 3 ^ 40 * 4755641 * 2
def baseEnd_4755641 : Nat := 813976551076177755472237

theorem tailTrace_4755641 : CollatzResearch.WordTrace tailWord_4755641 prefixEnd_4755641 813976551076177755472237 := by
  unfold tailWord_4755641
  simp only [CollatzResearch.WordTrace]
  refine ⟨173452476964132330665458777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115634984642754887110305851 173452476964132330665458777)
  ·
    refine ⟨130089357723099247999094083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173452476964132330665458777 130089357723099247999094083)
    ·
      refine ⟨195134036584648871998641125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130089357723099247999094083 195134036584648871998641125)
      ·
        refine ⟨36587631859621663499745211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195134036584648871998641125 36587631859621663499745211)
        ·
          refine ⟨54881447789432495249617817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36587631859621663499745211 54881447789432495249617817)
          ·
            refine ⟨41161085842074371437213363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54881447789432495249617817 41161085842074371437213363)
            ·
              refine ⟨61741628763111557155820045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41161085842074371437213363 61741628763111557155820045)
              ·
                refine ⟨23153110786166833933432517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61741628763111557155820045 23153110786166833933432517)
                ·
                  refine ⟨4341208272406281362518597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23153110786166833933432517 4341208272406281362518597)
                  ·
                    refine ⟨813976551076177755472237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341208272406281362518597 813976551076177755472237)
                    ·
                      rfl

theorem cell23_4755641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_4755641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755641 prefixEnd_4755641 := by exact prefixLift 4755641
  have htrace : WordTrace (prefixWord ++ tailWord_4755641) baseStart_4755641 baseEnd_4755641 := by
    simpa [prefixWord, tailWord_4755641, baseEnd_4755641] using wordTrace_append hprefix tailTrace_4755641
  have hstable : (prefixWord ++ tailWord_4755641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755641).length < 2 ^ (prefixWord ++ tailWord_4755641).sum := by decide
  have hdescent : baseEnd_4755641 < baseStart_4755641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755658 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_4755658 : Nat := 118140960795 + 4755658 * 2 ^ 59
def prefixEnd_4755658 : Nat := 4983230072969 + 3 ^ 40 * 4755658 * 2
def baseEnd_4755658 : Nat := 813979460799886566634711

theorem tailTrace_4755658 : CollatzResearch.WordTrace tailWord_4755658 prefixEnd_4755658 813979460799886566634711 := by
  unfold tailWord_4755658
  simp only [CollatzResearch.WordTrace]
  refine ⟨43363274251267685642206907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115635398003380495045885085 43363274251267685642206907)
  ·
    refine ⟨65044911376901528463310361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43363274251267685642206907 65044911376901528463310361)
    ·
      refine ⟨48783683532676146347482771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65044911376901528463310361 48783683532676146347482771)
      ·
        refine ⟨73175525299014219521224157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48783683532676146347482771 73175525299014219521224157)
        ·
          refine ⟨27440821987130332320459059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73175525299014219521224157 27440821987130332320459059)
          ·
            refine ⟨41161232980695498480688589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27440821987130332320459059 41161232980695498480688589)
            ·
              refine ⟨15435462367760811930258221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41161232980695498480688589 15435462367760811930258221)
              ·
                refine ⟨5788298387910304473846833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15435462367760811930258221 5788298387910304473846833)
                ·
                  refine ⟨4341223790932728355385125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788298387910304473846833 4341223790932728355385125)
                  ·
                    refine ⟨813979460799886566634711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341223790932728355385125 813979460799886566634711)
                    ·
                      rfl

theorem cell23_4755658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_4755658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755658 prefixEnd_4755658 := by exact prefixLift 4755658
  have htrace : WordTrace (prefixWord ++ tailWord_4755658) baseStart_4755658 baseEnd_4755658 := by
    simpa [prefixWord, tailWord_4755658, baseEnd_4755658] using wordTrace_append hprefix tailTrace_4755658
  have hstable : (prefixWord ++ tailWord_4755658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755658).length < 2 ^ (prefixWord ++ tailWord_4755658).sum := by decide
  have hdescent : baseEnd_4755658 < baseStart_4755658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755749 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_4755749 : Nat := 118140960795 + 4755749 * 2 ^ 59
def prefixEnd_4755749 : Nat := 4983230072969 + 3 ^ 40 * 4755749 * 2
def baseEnd_4755749 : Nat := 2441985109139218843866215

theorem tailTrace_4755749 : CollatzResearch.WordTrace tailWord_4755749 prefixEnd_4755749 2441985109139218843866215 := by
  unfold tailWord_4755749
  simp only [CollatzResearch.WordTrace]
  refine ⟨173456416047741065110390301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115637610698494043406926867 173456416047741065110390301)
  ·
    refine ⟨65046156017902899416396363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173456416047741065110390301 65046156017902899416396363)
    ·
      refine ⟨97569234026854349124594545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65046156017902899416396363 97569234026854349124594545)
      ·
        refine ⟨73176925520140761843445909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97569234026854349124594545 73176925520140761843445909)
        ·
          refine ⟨3430168383756598211411527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73176925520140761843445909 3430168383756598211411527)
          ·
            refine ⟨5145252575634897317117291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430168383756598211411527 5145252575634897317117291)
            ·
              refine ⟨7717878863452345975675937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145252575634897317117291 7717878863452345975675937)
              ·
                refine ⟨5788409147589259481756953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7717878863452345975675937 5788409147589259481756953)
                ·
                  refine ⟨4341306860691944611317715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788409147589259481756953 4341306860691944611317715)
                  ·
                    refine ⟨6511960291037916916976573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341306860691944611317715 6511960291037916916976573)
                    ·
                      refine ⟨2441985109139218843866215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6511960291037916916976573 2441985109139218843866215)
                      ·
                        rfl

theorem cell23_4755749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_4755749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755749 prefixEnd_4755749 := by exact prefixLift 4755749
  have htrace : WordTrace (prefixWord ++ tailWord_4755749) baseStart_4755749 baseEnd_4755749 := by
    simpa [prefixWord, tailWord_4755749, baseEnd_4755749] using wordTrace_append hprefix tailTrace_4755749
  have hstable : (prefixWord ++ tailWord_4755749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755749).length < 2 ^ (prefixWord ++ tailWord_4755749).sum := by decide
  have hdescent : baseEnd_4755749 < baseStart_4755749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755801 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_4755801 : Nat := 118140960795 + 4755801 * 2 ^ 59
def prefixEnd_4755801 : Nat := 4983230072969 + 3 ^ 40 * 4755801 * 2
def baseEnd_4755801 : Nat := 2442011810133252640415975

theorem tailTrace_4755801 : CollatzResearch.WordTrace tailWord_4755801 prefixEnd_4755801 2442011810133252640415975 := by
  unfold tailWord_4755801
  simp only [CollatzResearch.WordTrace]
  refine ⟨173458312643552677991283257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115638875095701785327522171 173458312643552677991283257)
  ·
    refine ⟨130093734482664508493462443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173458312643552677991283257 130093734482664508493462443)
    ·
      refine ⟨195140601723996762740193665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130093734482664508493462443 195140601723996762740193665)
      ·
        refine ⟨146355451292997572055145249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195140601723996762740193665 146355451292997572055145249)
        ·
          refine ⟨109766588469748179041358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146355451292997572055145249 109766588469748179041358937)
          ·
            refine ⟨82324941352311134281019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109766588469748179041358937 82324941352311134281019203)
            ·
              refine ⟨123487412028466701421528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82324941352311134281019203 123487412028466701421528805)
              ·
                refine ⟨23153889755337506516536651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123487412028466701421528805 23153889755337506516536651)
                ·
                  refine ⟨34730834633006259774804977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23153889755337506516536651 34730834633006259774804977)
                  ·
                    refine ⟨26048125974754694831103733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34730834633006259774804977 26048125974754694831103733)
                    ·
                      refine ⟨2442011810133252640415975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26048125974754694831103733 2442011810133252640415975)
                      ·
                        rfl

theorem cell23_4755801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_4755801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755801 prefixEnd_4755801 := by exact prefixLift 4755801
  have htrace : WordTrace (prefixWord ++ tailWord_4755801) baseStart_4755801 baseEnd_4755801 := by
    simpa [prefixWord, tailWord_4755801, baseEnd_4755801] using wordTrace_append hprefix tailTrace_4755801
  have hstable : (prefixWord ++ tailWord_4755801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755801).length < 2 ^ (prefixWord ++ tailWord_4755801).sum := by decide
  have hdescent : baseEnd_4755801 < baseStart_4755801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755818 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4755818 : Nat := 118140960795 + 4755818 * 2 ^ 59
def prefixEnd_4755818 : Nat := 4983230072969 + 3 ^ 40 * 4755818 * 2
def baseEnd_4755818 : Nat := 2442020539304379073903397

theorem tailTrace_4755818 : CollatzResearch.WordTrace tailWord_4755818 prefixEnd_4755818 2442020539304379073903397 := by
  unfold tailWord_4755818
  simp only [CollatzResearch.WordTrace]
  refine ⟨43364733171122772473663027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115639288456327393263101405 43364733171122772473663027)
  ·
    refine ⟨65047099756684158710494541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43364733171122772473663027 65047099756684158710494541)
    ·
      refine ⟨24392662408756559516435453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65047099756684158710494541 24392662408756559516435453)
      ·
        refine ⟨9147248403283709818663295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24392662408756559516435453 9147248403283709818663295)
        ·
          refine ⟨13720872604925564727994943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147248403283709818663295 13720872604925564727994943)
          ·
            refine ⟨20581308907388347091992415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13720872604925564727994943 20581308907388347091992415)
            ·
              refine ⟨30871963361082520637988623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20581308907388347091992415 30871963361082520637988623)
              ·
                refine ⟨46307945041623780956982935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30871963361082520637988623 46307945041623780956982935)
                ·
                  refine ⟨69461917562435671435474403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46307945041623780956982935 69461917562435671435474403)
                  ·
                    refine ⟨104192876343653507153211605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69461917562435671435474403 104192876343653507153211605)
                    ·
                      refine ⟨2442020539304379073903397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104192876343653507153211605 2442020539304379073903397)
                      ·
                        rfl

theorem cell23_4755818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4755818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755818 prefixEnd_4755818 := by exact prefixLift 4755818
  have htrace : WordTrace (prefixWord ++ tailWord_4755818) baseStart_4755818 baseEnd_4755818 := by
    simpa [prefixWord, tailWord_4755818, baseEnd_4755818] using wordTrace_append hprefix tailTrace_4755818
  have hstable : (prefixWord ++ tailWord_4755818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755818).length < 2 ^ (prefixWord ++ tailWord_4755818).sum := by decide
  have hdescent : baseEnd_4755818 < baseStart_4755818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755872 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 1, 4]
def baseStart_4755872 : Nat := 118140960795 + 4755872 * 2 ^ 59
def prefixEnd_4755872 : Nat := 4983230072969 + 3 ^ 40 * 4755872 * 2
def baseEnd_4755872 : Nat := 814016089086573954209383

theorem tailTrace_4755872 : CollatzResearch.WordTrace tailWord_4755872 prefixEnd_4755872 814016089086573954209383 := by
  unfold tailWord_4755872
  simp only [CollatzResearch.WordTrace]
  refine ⟨86730451113147728558558935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115640601484196971411411913 86730451113147728558558935)
  ·
    refine ⟨130095676669721592837838403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86730451113147728558558935 130095676669721592837838403)
    ·
      refine ⟨195143515004582389256757605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130095676669721592837838403 195143515004582389256757605)
      ·
        refine ⟨36589409063359197985642051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195143515004582389256757605 36589409063359197985642051)
        ·
          refine ⟨54884113595038796978463077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36589409063359197985642051 54884113595038796978463077)
          ·
            refine ⟨10290771299069774433461827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54884113595038796978463077 10290771299069774433461827)
            ·
              refine ⟨15436156948604661650192741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10290771299069774433461827 15436156948604661650192741)
              ·
                refine ⟨2894279427863374059411139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15436156948604661650192741 2894279427863374059411139)
                ·
                  refine ⟨4341419141795061089116709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894279427863374059411139 4341419141795061089116709)
                  ·
                    refine ⟨814016089086573954209383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341419141795061089116709 814016089086573954209383)
                    ·
                      rfl

theorem cell23_4755872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_4755872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755872 prefixEnd_4755872 := by exact prefixLift 4755872
  have htrace : WordTrace (prefixWord ++ tailWord_4755872) baseStart_4755872 baseEnd_4755872 := by
    simpa [prefixWord, tailWord_4755872, baseEnd_4755872] using wordTrace_append hprefix tailTrace_4755872
  have hstable : (prefixWord ++ tailWord_4755872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755872).length < 2 ^ (prefixWord ++ tailWord_4755872).sum := by decide
  have hdescent : baseEnd_4755872 < baseStart_4755872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755895 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_4755895 : Nat := 118140960795 + 4755895 * 2 ^ 59
def prefixEnd_4755895 : Nat := 4983230072969 + 3 ^ 40 * 4755895 * 2
def baseEnd_4755895 : Nat := 2442060077314775272640543

theorem tailTrace_4755895 : CollatzResearch.WordTrace tailWord_4755895 prefixEnd_4755895 2442060077314775272640543 := by
  unfold tailWord_4755895
  simp only [CollatzResearch.WordTrace]
  refine ⟨173461741105212132045205139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115641160736808088030136759 173461741105212132045205139)
  ·
    refine ⟨260192611657818198067807709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173461741105212132045205139 260192611657818198067807709)
    ·
      refine ⟨97572229371681824275427891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260192611657818198067807709 97572229371681824275427891)
      ·
        refine ⟨146358344057522736413141837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97572229371681824275427891 146358344057522736413141837)
        ·
          refine ⟨54884379021571026154928189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146358344057522736413141837 54884379021571026154928189)
          ·
            refine ⟨20581642133089134808098071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54884379021571026154928189 20581642133089134808098071)
            ·
              refine ⟨30872463199633702212147107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20581642133089134808098071 30872463199633702212147107)
              ·
                refine ⟨46308694799450553318220661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30872463199633702212147107 46308694799450553318220661)
                ·
                  refine ⟨4341440137448489373583187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46308694799450553318220661 4341440137448489373583187)
                  ·
                    refine ⟨6512160206172734060374781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341440137448489373583187 6512160206172734060374781)
                    ·
                      refine ⟨2442060077314775272640543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6512160206172734060374781 2442060077314775272640543)
                      ·
                        rfl

theorem cell23_4755895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_4755895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755895 prefixEnd_4755895 := by exact prefixLift 4755895
  have htrace : WordTrace (prefixWord ++ tailWord_4755895) baseStart_4755895 baseEnd_4755895 := by
    simpa [prefixWord, tailWord_4755895, baseEnd_4755895] using wordTrace_append hprefix tailTrace_4755895
  have hstable : (prefixWord ++ tailWord_4755895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755895).length < 2 ^ (prefixWord ++ tailWord_4755895).sum := by decide
  have hdescent : baseEnd_4755895 < baseStart_4755895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755948 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_4755948 : Nat := 118140960795 + 4755948 * 2 ^ 59
def prefixEnd_4755948 : Nat := 4983230072969 + 3 ^ 40 * 4755948 * 2
def baseEnd_4755948 : Nat := 2442087291789463565277799

theorem tailTrace_4755948 : CollatzResearch.WordTrace tailWord_4755948 prefixEnd_4755948 2442087291789463565277799 := by
  unfold tailWord_4755948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86731837087010061048442249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115642449449346748064589665 86731837087010061048442249)
  ·
    refine ⟨65048877815257545786331687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86731837087010061048442249 65048877815257545786331687)
    ·
      refine ⟨97573316722886318679497531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65048877815257545786331687 97573316722886318679497531)
      ·
        refine ⟨146359975084329478019246297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97573316722886318679497531 146359975084329478019246297)
        ·
          refine ⟨109769981313247108514434723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146359975084329478019246297 109769981313247108514434723)
          ·
            refine ⟨164654971969870662771652085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109769981313247108514434723 164654971969870662771652085)
            ·
              refine ⟨15436403622175374634842383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164654971969870662771652085 15436403622175374634842383)
              ·
                refine ⟨23154605433263061952263575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15436403622175374634842383 23154605433263061952263575)
                ·
                  refine ⟨34731908149894592928395363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23154605433263061952263575 34731908149894592928395363)
                  ·
                    refine ⟨52097862224841889392593045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34731908149894592928395363 52097862224841889392593045)
                    ·
                      refine ⟨2442087291789463565277799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52097862224841889392593045 2442087291789463565277799)
                      ·
                        rfl

theorem cell23_4755948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_4755948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755948 prefixEnd_4755948 := by exact prefixLift 4755948
  have htrace : WordTrace (prefixWord ++ tailWord_4755948) baseStart_4755948 baseEnd_4755948 := by
    simpa [prefixWord, tailWord_4755948, baseEnd_4755948] using wordTrace_append hprefix tailTrace_4755948
  have hstable : (prefixWord ++ tailWord_4755948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755948).length < 2 ^ (prefixWord ++ tailWord_4755948).sum := by decide
  have hdescent : baseEnd_4755948 < baseStart_4755948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755952 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2]
def baseStart_4755952 : Nat := 118140960795 + 4755952 * 2 ^ 59
def prefixEnd_4755952 : Nat := 4983230072969 + 3 ^ 40 * 4755952 * 2
def baseEnd_4755952 : Nat := 2442089345712081549627781

theorem tailTrace_4755952 : CollatzResearch.WordTrace tailWord_4755952 prefixEnd_4755952 2442089345712081549627781 := by
  unfold tailWord_4755952
  simp only [CollatzResearch.WordTrace]
  refine ⟨86731910033002815390015055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115642546710670420520020073 86731910033002815390015055)
  ·
    refine ⟨130097865049504223085022583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86731910033002815390015055 130097865049504223085022583)
    ·
      refine ⟨195146797574256334627533875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130097865049504223085022583 195146797574256334627533875)
      ·
        refine ⟨292720196361384501941300813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195146797574256334627533875 292720196361384501941300813)
        ·
          refine ⟨109770073635519188227987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292720196361384501941300813 109770073635519188227987805)
          ·
            refine ⟨41163777613319695585495427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109770073635519188227987805 41163777613319695585495427)
            ·
              refine ⟨61745666419979543378243141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41163777613319695585495427 61745666419979543378243141)
              ·
                refine ⟨11577312453746164383420589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61745666419979543378243141 11577312453746164383420589)
                ·
                  refine ⟨4341492170154811643782721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11577312453746164383420589 4341492170154811643782721)
                  ·
                    refine ⟨3256119127616108732837041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341492170154811643782721 3256119127616108732837041)
                    ·
                      refine ⟨2442089345712081549627781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256119127616108732837041 2442089345712081549627781)
                      ·
                        rfl

theorem cell23_4755952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2].length) (baseStart_4755952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755952 prefixEnd_4755952 := by exact prefixLift 4755952
  have htrace : WordTrace (prefixWord ++ tailWord_4755952) baseStart_4755952 baseEnd_4755952 := by
    simpa [prefixWord, tailWord_4755952, baseEnd_4755952] using wordTrace_append hprefix tailTrace_4755952
  have hstable : (prefixWord ++ tailWord_4755952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755952).length < 2 ^ (prefixWord ++ tailWord_4755952).sum := by decide
  have hdescent : baseEnd_4755952 < baseStart_4755952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755972 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4755972 : Nat := 118140960795 + 4755972 * 2 ^ 59
def prefixEnd_4755972 : Nat := 4983230072969 + 3 ^ 40 * 4755972 * 2
def baseEnd_4755972 : Nat := 2442099615325171471377689

theorem tailTrace_4755972 : CollatzResearch.WordTrace tailWord_4755972 prefixEnd_4755972 2442099615325171471377689 := by
  unfold tailWord_4755972
  simp only [CollatzResearch.WordTrace]
  refine ⟨86732274762966587097879085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115643033017288782797172113 86732274762966587097879085)
  ·
    refine ⟨32524603036112470161704657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86732274762966587097879085 32524603036112470161704657)
    ·
      refine ⟨24393452277084352621278493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32524603036112470161704657 24393452277084352621278493)
      ·
        refine ⟨9147544603906632232979435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24393452277084352621278493 9147544603906632232979435)
        ·
          refine ⟨13721316905859948349469153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147544603906632232979435 13721316905859948349469153)
          ·
            refine ⟨10290987679394961262101865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13721316905859948349469153 10290987679394961262101865)
            ·
              refine ⟨7718240759546220946576399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10290987679394961262101865 7718240759546220946576399)
              ·
                refine ⟨11577361139319331419864599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7718240759546220946576399 11577361139319331419864599)
                ·
                  refine ⟨17366041708978997129796899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11577361139319331419864599 17366041708978997129796899)
                  ·
                    refine ⟨26049062563468495694695349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17366041708978997129796899 26049062563468495694695349)
                    ·
                      refine ⟨2442099615325171471377689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26049062563468495694695349 2442099615325171471377689)
                      ·
                        rfl

theorem cell23_4755972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4755972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755972 prefixEnd_4755972 := by exact prefixLift 4755972
  have htrace : WordTrace (prefixWord ++ tailWord_4755972) baseStart_4755972 baseEnd_4755972 := by
    simpa [prefixWord, tailWord_4755972, baseEnd_4755972] using wordTrace_append hprefix tailTrace_4755972
  have hstable : (prefixWord ++ tailWord_4755972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755972).length < 2 ^ (prefixWord ++ tailWord_4755972).sum := by decide
  have hdescent : baseEnd_4755972 < baseStart_4755972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755975 : List Nat := [1, 1, 4, 3, 3, 2, 9]
def baseStart_4755975 : Nat := 118140960795 + 4755975 * 2 ^ 59
def prefixEnd_4755975 : Nat := 4983230072969 + 3 ^ 40 * 4755975 * 2
def baseEnd_4755975 : Nat := 30149396984779443946175

theorem tailTrace_4755975 : CollatzResearch.WordTrace tailWord_4755975 prefixEnd_4755975 30149396984779443946175 := by
  unfold tailWord_4755975
  simp only [CollatzResearch.WordTrace]
  refine ⟨173464658944922305708117379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115643105963281537138744919 173464658944922305708117379)
  ·
    refine ⟨260196988417383458562176069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173464658944922305708117379 260196988417383458562176069)
    ·
      refine ⟨48786935328259398480408013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260196988417383458562176069 48786935328259398480408013)
      ·
        refine ⟨18295100748097274430153005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48786935328259398480408013 18295100748097274430153005)
        ·
          refine ⟨6860662780536477911307377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18295100748097274430153005 6860662780536477911307377)
          ·
            refine ⟨5145497085402358433480533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860662780536477911307377 5145497085402358433480533)
            ·
              refine ⟨30149396984779443946175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5145497085402358433480533 30149396984779443946175)
              ·
                rfl

theorem cell23_4755975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 9].length) (baseStart_4755975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755975 prefixEnd_4755975 := by exact prefixLift 4755975
  have htrace : WordTrace (prefixWord ++ tailWord_4755975) baseStart_4755975 baseEnd_4755975 := by
    simpa [prefixWord, tailWord_4755975, baseEnd_4755975] using wordTrace_append hprefix tailTrace_4755975
  have hstable : (prefixWord ++ tailWord_4755975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755975).length < 2 ^ (prefixWord ++ tailWord_4755975).sum := by decide
  have hdescent : baseEnd_4755975 < baseStart_4755975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756055 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4756055 : Nat := 118140960795 + 4756055 * 2 ^ 59
def prefixEnd_4756055 : Nat := 4983230072969 + 3 ^ 40 * 4756055 * 2
def baseEnd_4756055 : Nat := 2442142234219494646639807

theorem tailTrace_4756055 : CollatzResearch.WordTrace tailWord_4756055 prefixEnd_4756055 2442142234219494646639807 := by
  unfold tailWord_4756055
  simp only [CollatzResearch.WordTrace]
  refine ⟨173467576784632479371029619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115645051189754986247353079 173467576784632479371029619)
  ·
    refine ⟨260201365176948719056544429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173467576784632479371029619 260201365176948719056544429)
    ·
      refine ⟨97575511941355769646204161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260201365176948719056544429 97575511941355769646204161)
      ·
        refine ⟨73181633956016827234653121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97575511941355769646204161 73181633956016827234653121)
        ·
          refine ⟨54886225467012620425989841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73181633956016827234653121 54886225467012620425989841)
          ·
            refine ⟨41164669100259465319492381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54886225467012620425989841 41164669100259465319492381)
            ·
              refine ⟨15436750912597299494809643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41164669100259465319492381 15436750912597299494809643)
              ·
                refine ⟨23155126368895949242214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15436750912597299494809643 23155126368895949242214465)
                ·
                  refine ⟨17366344776671961931660849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23155126368895949242214465 17366344776671961931660849)
                  ·
                    refine ⟨13024758582503971448745637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17366344776671961931660849 13024758582503971448745637)
                    ·
                      refine ⟨2442142234219494646639807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13024758582503971448745637 2442142234219494646639807)
                      ·
                        rfl

theorem cell23_4756055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4756055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756055 prefixEnd_4756055 := by exact prefixLift 4756055
  have htrace : WordTrace (prefixWord ++ tailWord_4756055) baseStart_4756055 baseEnd_4756055 := by
    simpa [prefixWord, tailWord_4756055, baseEnd_4756055] using wordTrace_append hprefix tailTrace_4756055
  have hstable : (prefixWord ++ tailWord_4756055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756055).length < 2 ^ (prefixWord ++ tailWord_4756055).sum := by decide
  have hdescent : baseEnd_4756055 < baseStart_4756055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756065 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 7]
def baseStart_4756065 : Nat := 118140960795 + 4756065 * 2 ^ 59
def prefixEnd_4756065 : Nat := 4983230072969 + 3 ^ 40 * 4756065 * 2
def baseEnd_4756065 : Nat := 271349707669559956390529

theorem tailTrace_4756065 : CollatzResearch.WordTrace tailWord_4756065 prefixEnd_4756065 271349707669559956390529 := by
  unfold tailWord_4756065
  simp only [CollatzResearch.WordTrace]
  refine ⟨173467941514596251078893649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115645294343064167385929099 173467941514596251078893649)
  ·
    refine ⟨130100956135947188309170237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173467941514596251078893649 130100956135947188309170237)
    ·
      refine ⟨48787858550980195615938839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130100956135947188309170237 48787858550980195615938839)
      ·
        refine ⟨73181787826470293423908259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48787858550980195615938839 73181787826470293423908259)
        ·
          refine ⟨109772681739705440135862389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73181787826470293423908259 109772681739705440135862389)
          ·
            refine ⟨10291188913097385012737099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109772681739705440135862389 10291188913097385012737099)
            ·
              refine ⟨15436783369646077519105649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291188913097385012737099 15436783369646077519105649)
              ·
                refine ⟨11577587527234558139329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15436783369646077519105649 11577587527234558139329237)
                ·
                  refine ⟨271349707669559956390529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11577587527234558139329237 271349707669559956390529)
                  ·
                    rfl

theorem cell23_4756065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_4756065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756065 prefixEnd_4756065 := by exact prefixLift 4756065
  have htrace : WordTrace (prefixWord ++ tailWord_4756065) baseStart_4756065 baseEnd_4756065 := by
    simpa [prefixWord, tailWord_4756065, baseEnd_4756065] using wordTrace_append hprefix tailTrace_4756065
  have hstable : (prefixWord ++ tailWord_4756065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756065).length < 2 ^ (prefixWord ++ tailWord_4756065).sum := by decide
  have hdescent : baseEnd_4756065 < baseStart_4756065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756093 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_4756093 : Nat := 118140960795 + 4756093 * 2 ^ 59
def prefixEnd_4756093 : Nat := 4983230072969 + 3 ^ 40 * 4756093 * 2
def baseEnd_4756093 : Nat := 2442161746484365497964633

theorem tailTrace_4756093 : CollatzResearch.WordTrace tailWord_4756093 prefixEnd_4756093 2442161746484365497964633 := by
  unfold tailWord_4756093
  simp only [CollatzResearch.WordTrace]
  refine ⟨173468962758494811860912933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115645975172329874573941955 173468962758494811860912933)
  ·
    refine ⟨32525430517217777223921175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173468962758494811860912933 32525430517217777223921175)
    ·
      refine ⟨48788145775826665835881763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32525430517217777223921175 48788145775826665835881763)
      ·
        refine ⟨73182218663739998753822645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48788145775826665835881763 73182218663739998753822645)
        ·
          refine ⟨6860832999725624883170873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73182218663739998753822645 6860832999725624883170873)
          ·
            refine ⟨5145624749794218662378155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860832999725624883170873 5145624749794218662378155)
            ·
              refine ⟨7718437124691327993567233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145624749794218662378155 7718437124691327993567233)
              ·
                refine ⟨5788827843518495995175425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7718437124691327993567233 5788827843518495995175425)
                ·
                  refine ⟨4341620882638871996381569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788827843518495995175425 4341620882638871996381569)
                  ·
                    refine ⟨3256215661979153997286177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341620882638871996381569 3256215661979153997286177)
                    ·
                      refine ⟨2442161746484365497964633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256215661979153997286177 2442161746484365497964633)
                      ·
                        rfl

theorem cell23_4756093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_4756093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756093 prefixEnd_4756093 := by exact prefixLift 4756093
  have htrace : WordTrace (prefixWord ++ tailWord_4756093) baseStart_4756093 baseEnd_4756093 := by
    simpa [prefixWord, tailWord_4756093, baseEnd_4756093] using wordTrace_append hprefix tailTrace_4756093
  have hstable : (prefixWord ++ tailWord_4756093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756093).length < 2 ^ (prefixWord ++ tailWord_4756093).sum := by decide
  have hdescent : baseEnd_4756093 < baseStart_4756093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756115 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4]
def baseStart_4756115 : Nat := 118140960795 + 4756115 * 2 ^ 59
def prefixEnd_4756115 : Nat := 4983230072969 + 3 ^ 40 * 4756115 * 2
def baseEnd_4756115 : Nat := 2442173043058764411889531

theorem tailTrace_4756115 : CollatzResearch.WordTrace tailWord_4756115 prefixEnd_4756115 2442173043058764411889531 := by
  unfold tailWord_4756115
  simp only [CollatzResearch.WordTrace]
  refine ⟨173469765164415109618213799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115646510109610073078809199 173469765164415109618213799)
  ·
    refine ⟨260204647746622664427320699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173469765164415109618213799 260204647746622664427320699)
    ·
      refine ⟨390306971619933996640981049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260204647746622664427320699 390306971619933996640981049)
      ·
        refine ⟨292730228714950497480735787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390306971619933996640981049 292730228714950497480735787)
        ·
          refine ⟨439095343072425746221103681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292730228714950497480735787 439095343072425746221103681)
          ·
            refine ⟨329321507304319309665827761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439095343072425746221103681 329321507304319309665827761)
            ·
              refine ⟨246991130478239482249370821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329321507304319309665827761 246991130478239482249370821)
              ·
                refine ⟨46310836964669902921757029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246991130478239482249370821 46310836964669902921757029)
                ·
                  refine ⟨8683281930875606797829443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46310836964669902921757029 8683281930875606797829443)
                  ·
                    refine ⟨13024922896313410196744165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8683281930875606797829443 13024922896313410196744165)
                    ·
                      refine ⟨2442173043058764411889531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13024922896313410196744165 2442173043058764411889531)
                      ·
                        rfl

theorem cell23_4756115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_4756115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756115 prefixEnd_4756115 := by exact prefixLift 4756115
  have htrace : WordTrace (prefixWord ++ tailWord_4756115) baseStart_4756115 baseEnd_4756115 := by
    simpa [prefixWord, tailWord_4756115, baseEnd_4756115] using wordTrace_append hprefix tailTrace_4756115
  have hstable : (prefixWord ++ tailWord_4756115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756115).length < 2 ^ (prefixWord ++ tailWord_4756115).sum := by decide
  have hdescent : baseEnd_4756115 < baseStart_4756115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756132 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_4756132 : Nat := 118140960795 + 4756132 * 2 ^ 59
def prefixEnd_4756132 : Nat := 4983230072969 + 3 ^ 40 * 4756132 * 2
def baseEnd_4756132 : Nat := 2442181772229890845376953

theorem tailTrace_4756132 : CollatzResearch.WordTrace tailWord_4756132 prefixEnd_4756132 2442181772229890845376953 := by
  unfold tailWord_4756132
  simp only [CollatzResearch.WordTrace]
  refine ⟨86735192602676760760791325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115646923470235681014388433 86735192602676760760791325)
  ·
    refine ⟨32525697226003785285296747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86735192602676760760791325 32525697226003785285296747)
    ·
      refine ⟨48788545839005677927945121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32525697226003785285296747 48788545839005677927945121)
      ·
        refine ⟨36591409379254258445958841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48788545839005677927945121 36591409379254258445958841)
        ·
          refine ⟨27443557034440693834469131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36591409379254258445958841 27443557034440693834469131)
          ·
            refine ⟨41165335551661040751703697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27443557034440693834469131 41165335551661040751703697)
            ·
              refine ⟨30874001663745780563777773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41165335551661040751703697 30874001663745780563777773)
              ·
                refine ⟨11577750623904667711416665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30874001663745780563777773 11577750623904667711416665)
                ·
                  refine ⟨8683312967928500783562499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11577750623904667711416665 8683312967928500783562499)
                  ·
                    refine ⟨13024969451892751175343749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8683312967928500783562499 13024969451892751175343749)
                    ·
                      refine ⟨2442181772229890845376953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13024969451892751175343749 2442181772229890845376953)
                      ·
                        rfl

theorem cell23_4756132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_4756132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756132 prefixEnd_4756132 := by exact prefixLift 4756132
  have htrace : WordTrace (prefixWord ++ tailWord_4756132) baseStart_4756132 baseEnd_4756132 := by
    simpa [prefixWord, tailWord_4756132, baseEnd_4756132] using wordTrace_append hprefix tailTrace_4756132
  have hstable : (prefixWord ++ tailWord_4756132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756132).length < 2 ^ (prefixWord ++ tailWord_4756132).sum := by decide
  have hdescent : baseEnd_4756132 < baseStart_4756132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756149 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4756149 : Nat := 118140960795 + 4756149 * 2 ^ 59
def prefixEnd_4756149 : Nat := 4983230072969 + 3 ^ 40 * 4756149 * 2
def baseEnd_4756149 : Nat := 2442190501401017278864375

theorem tailTrace_4756149 : CollatzResearch.WordTrace tailWord_4756149 prefixEnd_4756149 2442190501401017278864375 := by
  unfold tailWord_4756149
  simp only [CollatzResearch.WordTrace]
  refine ⟨173471005246291933424951501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115647336830861288949967667 173471005246291933424951501)
  ·
    refine ⟨65051626967359475034356813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173471005246291933424951501 65051626967359475034356813)
    ·
      refine ⟨24394360112759803137883805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65051626967359475034356813 24394360112759803137883805)
      ·
        refine ⟨9147885042284926176706427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24394360112759803137883805 9147885042284926176706427)
        ·
          refine ⟨13721827563427389265059641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147885042284926176706427 13721827563427389265059641)
          ·
            refine ⟨10291370672570541948794731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13721827563427389265059641 10291370672570541948794731)
            ·
              refine ⟨15437056008855812923192097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291370672570541948794731 15437056008855812923192097)
              ·
                refine ⟨11577792006641859692394073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15437056008855812923192097 11577792006641859692394073)
                ·
                  refine ⟨8683344004981394769295555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11577792006641859692394073 8683344004981394769295555)
                  ·
                    refine ⟨13025016007472092153943333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8683344004981394769295555 13025016007472092153943333)
                    ·
                      refine ⟨2442190501401017278864375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13025016007472092153943333 2442190501401017278864375)
                      ·
                        rfl

theorem cell23_4756149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4756149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756149 prefixEnd_4756149 := by exact prefixLift 4756149
  have htrace : WordTrace (prefixWord ++ tailWord_4756149) baseStart_4756149 baseEnd_4756149 := by
    simpa [prefixWord, tailWord_4756149, baseEnd_4756149] using wordTrace_append hprefix tailTrace_4756149
  have hstable : (prefixWord ++ tailWord_4756149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756149).length < 2 ^ (prefixWord ++ tailWord_4756149).sum := by decide
  have hdescent : baseEnd_4756149 < baseStart_4756149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756159 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 3, 4]
def baseStart_4756159 : Nat := 118140960795 + 4756159 * 2 ^ 59
def prefixEnd_4756159 : Nat := 4983230072969 + 3 ^ 40 * 4756159 * 2
def baseEnd_4756159 : Nat := 814065212069187413246443

theorem tailTrace_4756159 : CollatzResearch.WordTrace tailWord_4756159 prefixEnd_4756159 814065212069187413246443 := by
  unfold tailWord_4756159
  simp only [CollatzResearch.WordTrace]
  refine ⟨173471369976255705132815531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115647579984170470088543687 173471369976255705132815531)
  ·
    refine ⟨260207054964383557699223297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173471369976255705132815531 260207054964383557699223297)
    ·
      refine ⟨195155291223287668274417473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260207054964383557699223297 195155291223287668274417473)
      ·
        refine ⟨146366468417465751205813105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195155291223287668274417473 146366468417465751205813105)
        ·
          refine ⟨109774851313099313404359829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146366468417465751205813105 109774851313099313404359829)
          ·
            refine ⟨5145696155301530315829367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109774851313099313404359829 5145696155301530315829367)
            ·
              refine ⟨7718544232952295473744051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145696155301530315829367 7718544232952295473744051)
              ·
                refine ⟨11577816349428443210616077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7718544232952295473744051 11577816349428443210616077)
                ·
                  refine ⟨4341681131035666203981029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11577816349428443210616077 4341681131035666203981029)
                  ·
                    refine ⟨814065212069187413246443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341681131035666203981029 814065212069187413246443)
                    ·
                      rfl

theorem cell23_4756159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_4756159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756159 prefixEnd_4756159 := by exact prefixLift 4756159
  have htrace : WordTrace (prefixWord ++ tailWord_4756159) baseStart_4756159 baseEnd_4756159 := by
    simpa [prefixWord, tailWord_4756159, baseEnd_4756159] using wordTrace_append hprefix tailTrace_4756159
  have hstable : (prefixWord ++ tailWord_4756159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756159).length < 2 ^ (prefixWord ++ tailWord_4756159).sum := by decide
  have hdescent : baseEnd_4756159 < baseStart_4756159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756209 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_4756209 : Nat := 118140960795 + 4756209 * 2 ^ 59
def prefixEnd_4756209 : Nat := 4983230072969 + 3 ^ 40 * 4756209 * 2
def baseEnd_4756209 : Nat := 2442221310240287044114099

theorem tailTrace_4756209 : CollatzResearch.WordTrace tailWord_4756209 prefixEnd_4756209 2442221310240287044114099 := by
  unfold tailWord_4756209
  simp only [CollatzResearch.WordTrace]
  refine ⟨173473193626074563672135681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115648795750716375781423787 173473193626074563672135681)
  ·
    refine ⟨130104895219555922754101761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173473193626074563672135681 130104895219555922754101761)
    ·
      refine ⟨97578671414666942065576321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130104895219555922754101761 97578671414666942065576321)
      ·
        refine ⟨73184003561000206549182241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97578671414666942065576321 73184003561000206549182241)
        ·
          refine ⟨54888002670750154911886681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73184003561000206549182241 54888002670750154911886681)
          ·
            refine ⟨41166002003062616183915011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54888002670750154911886681 41166002003062616183915011)
            ·
              refine ⟨61749003004593924275872517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41166002003062616183915011 61749003004593924275872517)
              ·
                refine ⟨11577938063361360801726097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61749003004593924275872517 11577938063361360801726097)
                ·
                  refine ⟨8683453547521020601294573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11577938063361360801726097 8683453547521020601294573)
                  ·
                    refine ⟨3256295080320382725485465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8683453547521020601294573 3256295080320382725485465)
                    ·
                      refine ⟨2442221310240287044114099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256295080320382725485465 2442221310240287044114099)
                      ·
                        rfl

theorem cell23_4756209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_4756209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756209 prefixEnd_4756209 := by exact prefixLift 4756209
  have htrace : WordTrace (prefixWord ++ tailWord_4756209) baseStart_4756209 baseEnd_4756209 := by
    simpa [prefixWord, tailWord_4756209, baseEnd_4756209] using wordTrace_append hprefix tailTrace_4756209
  have hstable : (prefixWord ++ tailWord_4756209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756209).length < 2 ^ (prefixWord ++ tailWord_4756209).sum := by decide
  have hdescent : baseEnd_4756209 < baseStart_4756209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756215 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 6]
def baseStart_4756215 : Nat := 118140960795 + 4756215 * 2 ^ 59
def prefixEnd_4756215 : Nat := 4983230072969 + 3 ^ 40 * 4756215 * 2
def baseEnd_4756215 : Nat := 814074797041404673546357

theorem tailTrace_4756215 : CollatzResearch.WordTrace tailWord_4756215 prefixEnd_4756215 814074797041404673546357 := by
  unfold tailWord_4756215
  simp only [CollatzResearch.WordTrace]
  refine ⟨173473412464052826696854099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115648941642701884464569399 173473412464052826696854099)
  ·
    refine ⟨260210118696079240045281149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173473412464052826696854099 260210118696079240045281149)
    ·
      refine ⟨97578794511029715016980431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260210118696079240045281149 97578794511029715016980431)
      ·
        refine ⟨146368191766544572525470647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97578794511029715016980431 146368191766544572525470647)
        ·
          refine ⟨219552287649816858788205971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146368191766544572525470647 219552287649816858788205971)
          ·
            refine ⟨329328431474725288182308957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219552287649816858788205971 329328431474725288182308957)
            ·
              refine ⟨123498161803021983068365859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329328431474725288182308957 123498161803021983068365859)
              ·
                refine ⟨185247242704532974602548789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123498161803021983068365859 185247242704532974602548789)
                ·
                  refine ⟨17366929003549966368988949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185247242704532974602548789 17366929003549966368988949)
                  ·
                    refine ⟨814074797041404673546357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17366929003549966368988949 814074797041404673546357)
                    ·
                      rfl

theorem cell23_4756215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_4756215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756215 prefixEnd_4756215 := by exact prefixLift 4756215
  have htrace : WordTrace (prefixWord ++ tailWord_4756215) baseStart_4756215 baseEnd_4756215 := by
    simpa [prefixWord, tailWord_4756215, baseEnd_4756215] using wordTrace_append hprefix tailTrace_4756215
  have hstable : (prefixWord ++ tailWord_4756215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756215).length < 2 ^ (prefixWord ++ tailWord_4756215).sum := by decide
  have hdescent : baseEnd_4756215 < baseStart_4756215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756216 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_4756216 : Nat := 118140960795 + 4756216 * 2 ^ 59
def prefixEnd_4756216 : Nat := 4983230072969 + 3 ^ 40 * 4756216 * 2
def baseEnd_4756216 : Nat := 2442224904604868516726567

theorem tailTrace_4756216 : CollatzResearch.WordTrace tailWord_4756216 prefixEnd_4756216 2442224904604868516726567 := by
  unfold tailWord_4756216
  simp only [CollatzResearch.WordTrace]
  refine ⟨86736724468524601933820251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115648965958032802578427001 86736724468524601933820251)
  ·
    refine ⟨130105086702786902900730377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86736724468524601933820251 130105086702786902900730377)
    ·
      refine ⟨97578815027090177175547783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130105086702786902900730377 97578815027090177175547783)
      ·
        refine ⟨146368222540635265763321675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97578815027090177175547783 146368222540635265763321675)
        ·
          refine ⟨219552333810952898644982513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146368222540635265763321675 219552333810952898644982513)
          ·
            refine ⟨164664250358214673983736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219552333810952898644982513 164664250358214673983736885)
            ·
              refine ⟨15437273471082625685975333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164664250358214673983736885 15437273471082625685975333)
              ·
                refine ⟨2894488775827992316120375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15437273471082625685975333 2894488775827992316120375)
                ·
                  refine ⟨4341733163741988474180563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894488775827992316120375 4341733163741988474180563)
                  ·
                    refine ⟨6512599745612982711270845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341733163741988474180563 6512599745612982711270845)
                    ·
                      refine ⟨2442224904604868516726567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6512599745612982711270845 2442224904604868516726567)
                      ·
                        rfl

theorem cell23_4756216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_4756216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756216 prefixEnd_4756216 := by exact prefixLift 4756216
  have htrace : WordTrace (prefixWord ++ tailWord_4756216) baseStart_4756216 baseEnd_4756216 := by
    simpa [prefixWord, tailWord_4756216, baseEnd_4756216] using wordTrace_append hprefix tailTrace_4756216
  have hstable : (prefixWord ++ tailWord_4756216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756216).length < 2 ^ (prefixWord ++ tailWord_4756216).sum := by decide
  have hdescent : baseEnd_4756216 < baseStart_4756216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756232 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_4756232 : Nat := 118140960795 + 4756232 * 2 ^ 59
def prefixEnd_4756232 : Nat := 4983230072969 + 3 ^ 40 * 4756232 * 2
def baseEnd_4756232 : Nat := 814077706765113484708831

theorem tailTrace_4756232 : CollatzResearch.WordTrace tailWord_4756232 prefixEnd_4756232 814077706765113484708831 := by
  unfold tailWord_4756232
  simp only [CollatzResearch.WordTrace]
  refine ⟨86737016252495619300111475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115649355003327492400148633 86737016252495619300111475)
  ·
    refine ⟨130105524378743428950167213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86737016252495619300111475 130105524378743428950167213)
    ·
      refine ⟨48789571642028785856312705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130105524378743428950167213 48789571642028785856312705)
      ·
        refine ⟨36592178731521589392234529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48789571642028785856312705 36592178731521589392234529)
        ·
          refine ⟨27444134048641192044175897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36592178731521589392234529 27444134048641192044175897)
          ·
            refine ⟨20583100536480894033131923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27444134048641192044175897 20583100536480894033131923)
            ·
              refine ⟨30874650804721341049697885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20583100536480894033131923 30874650804721341049697885)
              ·
                refine ⟨11577994051770502893636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30874650804721341049697885 11577994051770502893636707)
                ·
                  refine ⟨17366991077655754340455061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11577994051770502893636707 17366991077655754340455061)
                  ·
                    refine ⟨814077706765113484708831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17366991077655754340455061 814077706765113484708831)
                    ·
                      rfl

theorem cell23_4756232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_4756232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756232 prefixEnd_4756232 := by exact prefixLift 4756232
  have htrace : WordTrace (prefixWord ++ tailWord_4756232) baseStart_4756232 baseEnd_4756232 := by
    simpa [prefixWord, tailWord_4756232, baseEnd_4756232] using wordTrace_append hprefix tailTrace_4756232
  have hstable : (prefixWord ++ tailWord_4756232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756232).length < 2 ^ (prefixWord ++ tailWord_4756232).sum := by decide
  have hdescent : baseEnd_4756232 < baseStart_4756232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756256 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4756256 : Nat := 118140960795 + 4756256 * 2 ^ 59
def prefixEnd_4756256 : Nat := 4983230072969 + 3 ^ 40 * 4756256 * 2
def baseEnd_4756256 : Nat := 2442245443831048360226383

theorem tailTrace_4756256 : CollatzResearch.WordTrace tailWord_4756256 prefixEnd_4756256 2442245443831048360226383 := by
  unfold tailWord_4756256
  simp only [CollatzResearch.WordTrace]
  refine ⟨86737453928452145349548311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115649938571269527132731081 86737453928452145349548311)
  ·
    refine ⟨130106180892678218024322467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86737453928452145349548311 130106180892678218024322467)
    ·
      refine ⟨195159271339017327036483701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130106180892678218024322467 195159271339017327036483701)
      ·
        refine ⟨18296181688032874409670347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195159271339017327036483701 18296181688032874409670347)
        ·
          refine ⟨27444272532049311614505521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18296181688032874409670347 27444272532049311614505521)
          ·
            refine ⟨20583204399036983710879141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27444272532049311614505521 20583204399036983710879141)
            ·
              refine ⟨3859350824819434445789839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20583204399036983710879141 3859350824819434445789839)
              ·
                refine ⟨5789026237229151668684759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859350824819434445789839 5789026237229151668684759)
                ·
                  refine ⟨8683539355843727503027139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5789026237229151668684759 8683539355843727503027139)
                  ·
                    refine ⟨13025309033765591254540709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8683539355843727503027139 13025309033765591254540709)
                    ·
                      refine ⟨2442245443831048360226383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13025309033765591254540709 2442245443831048360226383)
                      ·
                        rfl

theorem cell23_4756256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4756256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756256 prefixEnd_4756256 := by exact prefixLift 4756256
  have htrace : WordTrace (prefixWord ++ tailWord_4756256) baseStart_4756256 baseEnd_4756256 := by
    simpa [prefixWord, tailWord_4756256, baseEnd_4756256] using wordTrace_append hprefix tailTrace_4756256
  have hstable : (prefixWord ++ tailWord_4756256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756256).length < 2 ^ (prefixWord ++ tailWord_4756256).sum := by decide
  have hdescent : baseEnd_4756256 < baseStart_4756256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756272 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_4756272 : Nat := 118140960795 + 4756272 * 2 ^ 59
def prefixEnd_4756272 : Nat := 4983230072969 + 3 ^ 40 * 4756272 * 2
def baseEnd_4756272 : Nat := 2442253659521520297626309

theorem tailTrace_4756272 : CollatzResearch.WordTrace tailWord_4756272 prefixEnd_4756272 2442253659521520297626309 := by
  unfold tailWord_4756272
  simp only [CollatzResearch.WordTrace]
  refine ⟨86737745712423162715839535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115650327616564216954452713 86737745712423162715839535)
  ·
    refine ⟨130106618568634744073759303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86737745712423162715839535 130106618568634744073759303)
    ·
      refine ⟨195159927852952116110638955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130106618568634744073759303 195159927852952116110638955)
      ·
        refine ⟨292739891779428174165958433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195159927852952116110638955 292739891779428174165958433)
        ·
          refine ⟨219554918834571130624468825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292739891779428174165958433 219554918834571130624468825)
          ·
            refine ⟨164666189125928347968351619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219554918834571130624468825 164666189125928347968351619)
            ·
              refine ⟨246999283688892521952527429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164666189125928347968351619 246999283688892521952527429)
              ·
                refine ⟨46312365691667347866098893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246999283688892521952527429 46312365691667347866098893)
                ·
                  refine ⟨17367137134375255449787085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46312365691667347866098893 17367137134375255449787085)
                  ·
                    refine ⟨6512676425390720793670157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17367137134375255449787085 6512676425390720793670157)
                    ·
                      refine ⟨2442253659521520297626309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6512676425390720793670157 2442253659521520297626309)
                      ·
                        rfl

theorem cell23_4756272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_4756272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756272 prefixEnd_4756272 := by exact prefixLift 4756272
  have htrace : WordTrace (prefixWord ++ tailWord_4756272) baseStart_4756272 baseEnd_4756272 := by
    simpa [prefixWord, tailWord_4756272, baseEnd_4756272] using wordTrace_append hprefix tailTrace_4756272
  have hstable : (prefixWord ++ tailWord_4756272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756272).length < 2 ^ (prefixWord ++ tailWord_4756272).sum := by decide
  have hdescent : baseEnd_4756272 < baseStart_4756272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756273 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_4756273 : Nat := 118140960795 + 4756273 * 2 ^ 59
def prefixEnd_4756273 : Nat := 4983230072969 + 3 ^ 40 * 4756273 * 2
def baseEnd_4756273 : Nat := 2442254173002174793713805

theorem tailTrace_4756273 : CollatzResearch.WordTrace tailWord_4756273 prefixEnd_4756273 2442254173002174793713805 := by
  unfold tailWord_4756273
  simp only [CollatzResearch.WordTrace]
  refine ⟨173475527897842702602465473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115650351931895135068310315 173475527897842702602465473)
  ·
    refine ⟨130106645923382026951849105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173475527897842702602465473 130106645923382026951849105)
    ·
      refine ⟨97579984442536520213886829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130106645923382026951849105 97579984442536520213886829)
      ·
        refine ⟨36592494165951195080207561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97579984442536520213886829 36592494165951195080207561)
        ·
          refine ⟨27444370624463396310155671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36592494165951195080207561 27444370624463396310155671)
          ·
            refine ⟨41166555936695094465233507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27444370624463396310155671 41166555936695094465233507)
            ·
              refine ⟨61749833905042641697850261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41166555936695094465233507 61749833905042641697850261)
              ·
                refine ⟨2894523464298873829586731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61749833905042641697850261 2894523464298873829586731)
                ·
                  refine ⟨4341785196448310744380097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894523464298873829586731 4341785196448310744380097)
                  ·
                    refine ⟨3256338897336233058285073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341785196448310744380097 3256338897336233058285073)
                    ·
                      refine ⟨2442254173002174793713805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256338897336233058285073 2442254173002174793713805)
                      ·
                        rfl

theorem cell23_4756273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_4756273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756273 prefixEnd_4756273 := by exact prefixLift 4756273
  have htrace : WordTrace (prefixWord ++ tailWord_4756273) baseStart_4756273 baseEnd_4756273 := by
    simpa [prefixWord, tailWord_4756273, baseEnd_4756273] using wordTrace_append hprefix tailTrace_4756273
  have hstable : (prefixWord ++ tailWord_4756273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756273).length < 2 ^ (prefixWord ++ tailWord_4756273).sum := by decide
  have hdescent : baseEnd_4756273 < baseStart_4756273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756276 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_4756276 : Nat := 118140960795 + 4756276 * 2 ^ 59
def prefixEnd_4756276 : Nat := 4983230072969 + 3 ^ 40 * 4756276 * 2
def baseEnd_4756276 : Nat := 2442255713444138281976291

theorem tailTrace_4756276 : CollatzResearch.WordTrace tailWord_4756276 prefixEnd_4756276 2442255713444138281976291 := by
  unfold tailWord_4756276
  simp only [CollatzResearch.WordTrace]
  refine ⟨86737818658415917057412341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115650424877887889409883121 86737818658415917057412341)
  ·
    refine ⟨8131670499226492224132407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86737818658415917057412341 8131670499226492224132407)
    ·
      refine ⟨12197505748839738336198611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131670499226492224132407 12197505748839738336198611)
      ·
        refine ⟨18296258623259607504297917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12197505748839738336198611 18296258623259607504297917)
        ·
          refine ⟨6861096983722352814111719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18296258623259607504297917 6861096983722352814111719)
          ·
            refine ⟨10291645475583529221167579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861096983722352814111719 10291645475583529221167579)
            ·
              refine ⟨15437468213375293831751369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291645475583529221167579 15437468213375293831751369)
              ·
                refine ⟨11578101160031470373813527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15437468213375293831751369 11578101160031470373813527)
                ·
                  refine ⟨17367151740047205560720291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11578101160031470373813527 17367151740047205560720291)
                  ·
                    refine ⟨26050727610070808341080437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17367151740047205560720291 26050727610070808341080437)
                    ·
                      refine ⟨2442255713444138281976291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26050727610070808341080437 2442255713444138281976291)
                      ·
                        rfl

theorem cell23_4756276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_4756276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756276 prefixEnd_4756276 := by exact prefixLift 4756276
  have htrace : WordTrace (prefixWord ++ tailWord_4756276) baseStart_4756276 baseEnd_4756276 := by
    simpa [prefixWord, tailWord_4756276, baseEnd_4756276] using wordTrace_append hprefix tailTrace_4756276
  have hstable : (prefixWord ++ tailWord_4756276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756276).length < 2 ^ (prefixWord ++ tailWord_4756276).sum := by decide
  have hdescent : baseEnd_4756276 < baseStart_4756276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756332 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_4756332 : Nat := 118140960795 + 4756332 * 2 ^ 59
def prefixEnd_4756332 : Nat := 4983230072969 + 3 ^ 40 * 4756332 * 2
def baseEnd_4756332 : Nat := 2442284468360790062876033

theorem tailTrace_4756332 : CollatzResearch.WordTrace tailWord_4756332 prefixEnd_4756332 2442284468360790062876033 := by
  unfold tailWord_4756332
  simp only [CollatzResearch.WordTrace]
  refine ⟨86738839902314477839431625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115651786536419303785908833 86738839902314477839431625)
  ·
    refine ⟨65054129926735858379573719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86738839902314477839431625 65054129926735858379573719)
    ·
      refine ⟨97581194890103787569360579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65054129926735858379573719 97581194890103787569360579)
      ·
        refine ⟨146371792335155681354040869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97581194890103787569360579 146371792335155681354040869)
        ·
          refine ⟨27444711062841690253882663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146371792335155681354040869 27444711062841690253882663)
          ·
            refine ⟨41167066594262535380823995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27444711062841690253882663 41167066594262535380823995)
            ·
              refine ⟨61750599891393803071235993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41167066594262535380823995 61750599891393803071235993)
              ·
                refine ⟨46312949918545352303426995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61750599891393803071235993 46312949918545352303426995)
                ·
                  refine ⟨69469424877818028455140493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46312949918545352303426995 69469424877818028455140493)
                  ·
                    refine ⟨26051034329181760670677685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69469424877818028455140493 26051034329181760670677685)
                    ·
                      refine ⟨2442284468360790062876033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26051034329181760670677685 2442284468360790062876033)
                      ·
                        rfl

theorem cell23_4756332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_4756332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756332 prefixEnd_4756332 := by exact prefixLift 4756332
  have htrace : WordTrace (prefixWord ++ tailWord_4756332) baseStart_4756332 baseEnd_4756332 := by
    simpa [prefixWord, tailWord_4756332, baseEnd_4756332] using wordTrace_append hprefix tailTrace_4756332
  have hstable : (prefixWord ++ tailWord_4756332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756332).length < 2 ^ (prefixWord ++ tailWord_4756332).sum := by decide
  have hdescent : baseEnd_4756332 < baseStart_4756332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756350 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4756350 : Nat := 118140960795 + 4756350 * 2 ^ 59
def prefixEnd_4756350 : Nat := 4983230072969 + 3 ^ 40 * 4756350 * 2
def baseEnd_4756350 : Nat := 2442293711012570992450951

theorem tailTrace_4756350 : CollatzResearch.WordTrace tailWord_4756350 prefixEnd_4756350 2442293711012570992450951 := by
  unfold tailWord_4756350
  simp only [CollatzResearch.WordTrace]
  refine ⟨21684792039820468094127313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115652224212375829835345669 21684792039820468094127313)
  ·
    refine ⟨16263594029865351070595485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21684792039820468094127313 16263594029865351070595485)
    ·
      refine ⟨6098847761199506651473307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16263594029865351070595485 6098847761199506651473307)
      ·
        refine ⟨9148271641799259977209961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098847761199506651473307 9148271641799259977209961)
        ·
          refine ⟨6861203731349444982907471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9148271641799259977209961 6861203731349444982907471)
          ·
            refine ⟨10291805597024167474361207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861203731349444982907471 10291805597024167474361207)
            ·
              refine ⟨15437708395536251211541811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291805597024167474361207 15437708395536251211541811)
              ·
                refine ⟨23156562593304376817312717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15437708395536251211541811 23156562593304376817312717)
                ·
                  refine ⟨8683710972489141306492269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23156562593304376817312717 8683710972489141306492269)
                  ·
                    refine ⟨3256391614683427989934601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8683710972489141306492269 3256391614683427989934601)
                    ·
                      refine ⟨2442293711012570992450951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256391614683427989934601 2442293711012570992450951)
                      ·
                        rfl

theorem cell23_4756350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4756350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756350 prefixEnd_4756350 := by exact prefixLift 4756350
  have htrace : WordTrace (prefixWord ++ tailWord_4756350) baseStart_4756350 baseEnd_4756350 := by
    simpa [prefixWord, tailWord_4756350, baseEnd_4756350] using wordTrace_append hprefix tailTrace_4756350
  have hstable : (prefixWord ++ tailWord_4756350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756350).length < 2 ^ (prefixWord ++ tailWord_4756350).sum := by decide
  have hdescent : baseEnd_4756350 < baseStart_4756350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756369 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 5]
def baseStart_4756369 : Nat := 118140960795 + 4756369 * 2 ^ 59
def prefixEnd_4756369 : Nat := 4983230072969 + 3 ^ 40 * 4756369 * 2
def baseEnd_4756369 : Nat := 271367051905000713123707

theorem tailTrace_4756369 : CollatzResearch.WordTrace tailWord_4756369 prefixEnd_4756369 271367051905000713123707 := by
  unfold tailWord_4756369
  simp only [CollatzResearch.WordTrace]
  refine ⟨173479029305494910997960161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115652686203663273998640107 173479029305494910997960161)
  ·
    refine ⟨130109271979121183248470121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173479029305494910997960161 130109271979121183248470121)
    ·
      refine ⟨97581953984340887436352591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130109271979121183248470121 97581953984340887436352591)
      ·
        refine ⟨146372930976511331154528887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97581953984340887436352591 146372930976511331154528887)
        ·
          refine ⟨219559396464766996731793331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146372930976511331154528887 219559396464766996731793331)
          ·
            refine ⟨329339094697150495097689997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219559396464766996731793331 329339094697150495097689997)
            ·
              refine ⟨123502160511431435661633749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329339094697150495097689997 123502160511431435661633749)
              ·
                refine ⟨2894581886986674273319541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123502160511431435661633749 2894581886986674273319541)
                ·
                  refine ⟨271367051905000713123707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2894581886986674273319541 271367051905000713123707)
                  ·
                    rfl

theorem cell23_4756369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 5].length) (baseStart_4756369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756369 prefixEnd_4756369 := by exact prefixLift 4756369
  have htrace : WordTrace (prefixWord ++ tailWord_4756369) baseStart_4756369 baseEnd_4756369 := by
    simpa [prefixWord, tailWord_4756369, baseEnd_4756369] using wordTrace_append hprefix tailTrace_4756369
  have hstable : (prefixWord ++ tailWord_4756369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756369).length < 2 ^ (prefixWord ++ tailWord_4756369).sum := by decide
  have hdescent : baseEnd_4756369 < baseStart_4756369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756416 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_4756416 : Nat := 118140960795 + 4756416 * 2 ^ 59
def prefixEnd_4756416 : Nat := 4983230072969 + 3 ^ 40 * 4756416 * 2
def baseEnd_4756416 : Nat := 814109200245255911408549

theorem tailTrace_4756416 : CollatzResearch.WordTrace tailWord_4756416 prefixEnd_4756416 814109200245255911408549 := by
  unfold tailWord_4756416
  simp only [CollatzResearch.WordTrace]
  refine ⟨86740371768162319012460551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115653829024216425349947401 86740371768162319012460551)
  ·
    refine ⟨130110557652243478518690827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86740371768162319012460551 130110557652243478518690827)
    ·
      refine ⟨195165836478365217778036241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130110557652243478518690827 195165836478365217778036241)
      ·
        refine ⟨146374377358773913333527181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195165836478365217778036241 146374377358773913333527181)
        ·
          refine ⟨54890391509540217500072693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146374377358773913333527181 54890391509540217500072693)
          ·
            refine ⟨5145974204019395390631815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54890391509540217500072693 5145974204019395390631815)
            ·
              refine ⟨7718961306029093085947723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145974204019395390631815 7718961306029093085947723)
              ·
                refine ⟨11578441959043639628921585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7718961306029093085947723 11578441959043639628921585)
                ·
                  refine ⟨8683831469282729721691189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11578441959043639628921585 8683831469282729721691189)
                  ·
                    refine ⟨814109200245255911408549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8683831469282729721691189 814109200245255911408549)
                    ·
                      rfl

theorem cell23_4756416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_4756416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756416 prefixEnd_4756416 := by exact prefixLift 4756416
  have htrace : WordTrace (prefixWord ++ tailWord_4756416) baseStart_4756416 baseEnd_4756416 := by
    simpa [prefixWord, tailWord_4756416, baseEnd_4756416] using wordTrace_append hprefix tailTrace_4756416
  have hstable : (prefixWord ++ tailWord_4756416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756416).length < 2 ^ (prefixWord ++ tailWord_4756416).sum := by decide
  have hdescent : baseEnd_4756416 < baseStart_4756416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756420 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 5]
def baseStart_4756420 : Nat := 118140960795 + 4756420 * 2 ^ 59
def prefixEnd_4756420 : Nat := 4983230072969 + 3 ^ 40 * 4756420 * 2
def baseEnd_4756420 : Nat := 271369961628709524286181

theorem tailTrace_4756420 : CollatzResearch.WordTrace tailWord_4756420 prefixEnd_4756420 271369961628709524286181 := by
  unfold tailWord_4756420
  simp only [CollatzResearch.WordTrace]
  refine ⟨86740444714155073354033357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115653926285540097805377809 86740444714155073354033357)
  ·
    refine ⟨32527666767808152507762509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86740444714155073354033357 32527666767808152507762509)
    ·
      refine ⟨12197875037928057190410941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32527666767808152507762509 12197875037928057190410941)
      ·
        refine ⟨4574203139223021446404103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12197875037928057190410941 4574203139223021446404103)
        ·
          refine ⟨6861304708834532169606155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574203139223021446404103 6861304708834532169606155)
          ·
            refine ⟨10291957063251798254409233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861304708834532169606155 10291957063251798254409233)
            ·
              refine ⟨7718967797438848690806925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10291957063251798254409233 7718967797438848690806925)
              ·
                refine ⟨2894612924039568259052597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7718967797438848690806925 2894612924039568259052597)
                ·
                  refine ⟨271369961628709524286181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2894612924039568259052597 271369961628709524286181)
                  ·
                    rfl

theorem cell23_4756420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_4756420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756420 prefixEnd_4756420 := by exact prefixLift 4756420
  have htrace : WordTrace (prefixWord ++ tailWord_4756420) baseStart_4756420 baseEnd_4756420 := by
    simpa [prefixWord, tailWord_4756420, baseEnd_4756420] using wordTrace_append hprefix tailTrace_4756420
  have hstable : (prefixWord ++ tailWord_4756420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756420).length < 2 ^ (prefixWord ++ tailWord_4756420).sum := by decide
  have hdescent : baseEnd_4756420 < baseStart_4756420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756536 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_4756536 : Nat := 118140960795 + 4756536 * 2 ^ 59
def prefixEnd_4756536 : Nat := 4983230072969 + 3 ^ 40 * 4756536 * 2
def baseEnd_4756536 : Nat := 814129739471435754908365

theorem tailTrace_4756536 : CollatzResearch.WordTrace tailWord_4756536 prefixEnd_4756536 814129739471435754908365 := by
  unfold tailWord_4756536
  simp only [CollatzResearch.WordTrace]
  refine ⟨86742560147944949259644731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115656746863926599012859641 86742560147944949259644731)
  ·
    refine ⟨130113840221917423889467097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86742560147944949259644731 130113840221917423889467097)
    ·
      refine ⟨97585380166438067917100323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130113840221917423889467097 97585380166438067917100323)
      ·
        refine ⟨146378070249657101875650485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97585380166438067917100323 146378070249657101875650485)
        ·
          refine ⟨13722944085905353300842233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146378070249657101875650485 13722944085905353300842233)
          ·
            refine ⟨10292208064429014975631675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13722944085905353300842233 10292208064429014975631675)
            ·
              refine ⟨15438312096643522463447513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10292208064429014975631675 15438312096643522463447513)
              ·
                refine ⟨11578734072482641847585635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15438312096643522463447513 11578734072482641847585635)
                ·
                  refine ⟨17368101108723962771378453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11578734072482641847585635 17368101108723962771378453)
                  ·
                    refine ⟨814129739471435754908365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17368101108723962771378453 814129739471435754908365)
                    ·
                      rfl

theorem cell23_4756536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_4756536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756536 prefixEnd_4756536 := by exact prefixLift 4756536
  have htrace : WordTrace (prefixWord ++ tailWord_4756536) baseStart_4756536 baseEnd_4756536 := by
    simpa [prefixWord, tailWord_4756536, baseEnd_4756536] using wordTrace_append hprefix tailTrace_4756536
  have hstable : (prefixWord ++ tailWord_4756536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756536).length < 2 ^ (prefixWord ++ tailWord_4756536).sum := by decide
  have hdescent : baseEnd_4756536 < baseStart_4756536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756579 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 7]
def baseStart_4756579 : Nat := 118140960795 + 4756579 * 2 ^ 59
def prefixEnd_4756579 : Nat := 4983230072969 + 3 ^ 40 * 4756579 * 2
def baseEnd_4756579 : Nat := 814137099360816865495799

theorem tailTrace_4756579 : CollatzResearch.WordTrace tailWord_4756579 prefixEnd_4756579 814137099360816865495799 := by
  unfold tailWord_4756579
  simp only [CollatzResearch.WordTrace]
  refine ⟨173486688634734116863104791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115657792423156077908736527 173486688634734116863104791)
  ·
    refine ⟨260230032952101175294657187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173486688634734116863104791 260230032952101175294657187)
    ·
      refine ⟨390345049428151762941985781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260230032952101175294657187 390345049428151762941985781)
      ·
        refine ⟨36594848383889227775811167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 390345049428151762941985781 36594848383889227775811167)
        ·
          refine ⟨54892272575833841663716751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36594848383889227775811167 54892272575833841663716751)
          ·
            refine ⟨82338408863750762495575127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54892272575833841663716751 82338408863750762495575127)
            ·
              refine ⟨123507613295626143743362691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82338408863750762495575127 123507613295626143743362691)
              ·
                refine ⟨185261419943439215615044037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123507613295626143743362691 185261419943439215615044037)
                ·
                  refine ⟨34736516239394852927820757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185261419943439215615044037 34736516239394852927820757)
                  ·
                    refine ⟨814137099360816865495799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34736516239394852927820757 814137099360816865495799)
                    ·
                      rfl

theorem cell23_4756579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_4756579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756579 prefixEnd_4756579 := by exact prefixLift 4756579
  have htrace : WordTrace (prefixWord ++ tailWord_4756579) baseStart_4756579 baseEnd_4756579 := by
    simpa [prefixWord, tailWord_4756579, baseEnd_4756579] using wordTrace_append hprefix tailTrace_4756579
  have hstable : (prefixWord ++ tailWord_4756579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756579).length < 2 ^ (prefixWord ++ tailWord_4756579).sum := by decide
  have hdescent : baseEnd_4756579 < baseStart_4756579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756597 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4756597 : Nat := 118140960795 + 4756597 * 2 ^ 59
def prefixEnd_4756597 : Nat := 4983230072969 + 3 ^ 40 * 4756597 * 2
def baseEnd_4756597 : Nat := 2442420540734231526062315

theorem tailTrace_4756597 : CollatzResearch.WordTrace tailWord_4756597 prefixEnd_4756597 2442420540734231526062315 := by
  unfold tailWord_4756597
  simp only [CollatzResearch.WordTrace]
  refine ⟨173487345148668905937260045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115658230099112603958173363 173487345148668905937260045)
  ·
    refine ⟨65057754430750839726472517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173487345148668905937260045 65057754430750839726472517)
    ·
      refine ⟨12198328955765782448713597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65057754430750839726472517 12198328955765782448713597)
      ·
        refine ⟨4574373358412168418267599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12198328955765782448713597 4574373358412168418267599)
        ·
          refine ⟨6861560037618252627401399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574373358412168418267599 6861560037618252627401399)
          ·
            refine ⟨10292340056427378941102099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861560037618252627401399 10292340056427378941102099)
            ·
              refine ⟨15438510084641068411653149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10292340056427378941102099 15438510084641068411653149)
              ·
                refine ⟨5789441281740400654369931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15438510084641068411653149 5789441281740400654369931)
                ·
                  refine ⟨8684161922610600981554897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5789441281740400654369931 8684161922610600981554897)
                  ·
                    refine ⟨6513121441957950736166173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684161922610600981554897 6513121441957950736166173)
                    ·
                      refine ⟨2442420540734231526062315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513121441957950736166173 2442420540734231526062315)
                      ·
                        rfl

theorem cell23_4756597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4756597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756597 prefixEnd_4756597 := by exact prefixLift 4756597
  have htrace : WordTrace (prefixWord ++ tailWord_4756597) baseStart_4756597 baseEnd_4756597 := by
    simpa [prefixWord, tailWord_4756597, baseEnd_4756597] using wordTrace_append hprefix tailTrace_4756597
  have hstable : (prefixWord ++ tailWord_4756597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756597).length < 2 ^ (prefixWord ++ tailWord_4756597).sum := by decide
  have hdescent : baseEnd_4756597 < baseStart_4756597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756723 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4]
def baseStart_4756723 : Nat := 118140960795 + 4756723 * 2 ^ 59
def prefixEnd_4756723 : Nat := 4983230072969 + 3 ^ 40 * 4756723 * 2
def baseEnd_4756723 : Nat := 2442485239296698033086735

theorem tailTrace_4756723 : CollatzResearch.WordTrace tailWord_4756723 prefixEnd_4756723 2442485239296698033086735 := by
  unfold tailWord_4756723
  simp only [CollatzResearch.WordTrace]
  refine ⟨173491940746212429456346823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115661293830808286304231215 173491940746212429456346823)
  ·
    refine ⟨260237911119318644184520235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173491940746212429456346823 260237911119318644184520235)
    ·
      refine ⟨390356866678977966276780353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260237911119318644184520235 390356866678977966276780353)
      ·
        refine ⟨292767650009233474707585265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390356866678977966276780353 292767650009233474707585265)
        ·
          refine ⟨219575737506925106030688949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292767650009233474707585265 219575737506925106030688949)
          ·
            refine ⟨20585225391274228690377089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219575737506925106030688949 20585225391274228690377089)
            ·
              refine ⟨15438919043455671517782817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20585225391274228690377089 15438919043455671517782817)
              ·
                refine ⟨11579189282591753638337113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15438919043455671517782817 11579189282591753638337113)
                ·
                  refine ⟨8684391961943815228752835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579189282591753638337113 8684391961943815228752835)
                  ·
                    refine ⟨13026587942915722843129253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8684391961943815228752835 13026587942915722843129253)
                    ·
                      refine ⟨2442485239296698033086735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13026587942915722843129253 2442485239296698033086735)
                      ·
                        rfl

theorem cell23_4756723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_4756723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756723 prefixEnd_4756723 := by exact prefixLift 4756723
  have htrace : WordTrace (prefixWord ++ tailWord_4756723) baseStart_4756723 baseEnd_4756723 := by
    simpa [prefixWord, tailWord_4756723, baseEnd_4756723] using wordTrace_append hprefix tailTrace_4756723
  have hstable : (prefixWord ++ tailWord_4756723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756723).length < 2 ^ (prefixWord ++ tailWord_4756723).sum := by decide
  have hdescent : baseEnd_4756723 < baseStart_4756723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756736 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_4756736 : Nat := 118140960795 + 4756736 * 2 ^ 59
def prefixEnd_4756736 : Nat := 4983230072969 + 3 ^ 40 * 4756736 * 2
def baseEnd_4756736 : Nat := 2442491914545206482224175

theorem tailTrace_4756736 : CollatzResearch.WordTrace tailWord_4756736 prefixEnd_4756736 2442491914545206482224175 := by
  unfold tailWord_4756736
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746207447582666338285031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115661609930110221784380041 86746207447582666338285031)
  ·
    refine ⟨130119311171373999507427547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86746207447582666338285031 130119311171373999507427547)
    ·
      refine ⟨195178966757060999261141321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130119311171373999507427547 195178966757060999261141321)
      ·
        refine ⟨146384225067795749445855991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195178966757060999261141321 146384225067795749445855991)
        ·
          refine ⟨219576337601693624168783987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146384225067795749445855991 219576337601693624168783987)
          ·
            refine ⟨329364506402540436253175981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219576337601693624168783987 329364506402540436253175981)
            ·
              refine ⟨123511689900952663594940993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329364506402540436253175981 123511689900952663594940993)
              ·
                refine ⟨92633767425714497696205745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123511689900952663594940993 92633767425714497696205745)
                ·
                  refine ⟨69475325569285873272154309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92633767425714497696205745 69475325569285873272154309)
                  ·
                    refine ⟨13026623544241101238528933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69475325569285873272154309 13026623544241101238528933)
                    ·
                      refine ⟨2442491914545206482224175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13026623544241101238528933 2442491914545206482224175)
                      ·
                        rfl

theorem cell23_4756736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_4756736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756736 prefixEnd_4756736 := by exact prefixLift 4756736
  have htrace : WordTrace (prefixWord ++ tailWord_4756736) baseStart_4756736 baseEnd_4756736 := by
    simpa [prefixWord, tailWord_4756736, baseEnd_4756736] using wordTrace_append hprefix tailTrace_4756736
  have hstable : (prefixWord ++ tailWord_4756736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756736).length < 2 ^ (prefixWord ++ tailWord_4756736).sum := by decide
  have hdescent : baseEnd_4756736 < baseStart_4756736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756740 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4756740 : Nat := 118140960795 + 4756740 * 2 ^ 59
def prefixEnd_4756740 : Nat := 4983230072969 + 3 ^ 40 * 4756740 * 2
def baseEnd_4756740 : Nat := 2442493968467824466574157

theorem tailTrace_4756740 : CollatzResearch.WordTrace tailWord_4756740 prefixEnd_4756740 2442493968467824466574157 := by
  unfold tailWord_4756740
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746280393575420679857837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115661707191433894239810449 86746280393575420679857837)
  ·
    refine ⟨32529855147590782754946689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86746280393575420679857837 32529855147590782754946689)
    ·
      refine ⟨24397391360693087066210017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32529855147590782754946689 24397391360693087066210017)
      ·
        refine ⟨18298043520519815299657513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24397391360693087066210017 18298043520519815299657513)
        ·
          refine ⟨13723532640389861474743135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18298043520519815299657513 13723532640389861474743135)
          ·
            refine ⟨20585298960584792212114703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13723532640389861474743135 20585298960584792212114703)
            ·
              refine ⟨30877948440877188318172055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20585298960584792212114703 30877948440877188318172055)
              ·
                refine ⟨46316922661315782477258083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30877948440877188318172055 46316922661315782477258083)
                ·
                  refine ⟨69475383991973673715887125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46316922661315782477258083 69475383991973673715887125)
                  ·
                    refine ⟨3256658624623765955432209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69475383991973673715887125 3256658624623765955432209)
                    ·
                      refine ⟨2442493968467824466574157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256658624623765955432209 2442493968467824466574157)
                      ·
                        rfl

theorem cell23_4756740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4756740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756740 prefixEnd_4756740 := by exact prefixLift 4756740
  have htrace : WordTrace (prefixWord ++ tailWord_4756740) baseStart_4756740 baseEnd_4756740 := by
    simpa [prefixWord, tailWord_4756740, baseEnd_4756740] using wordTrace_append hprefix tailTrace_4756740
  have hstable : (prefixWord ++ tailWord_4756740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756740).length < 2 ^ (prefixWord ++ tailWord_4756740).sum := by decide
  have hdescent : baseEnd_4756740 < baseStart_4756740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756746 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_4756746 : Nat := 118140960795 + 4756746 * 2 ^ 59
def prefixEnd_4756746 : Nat := 4983230072969 + 3 ^ 40 * 4756746 * 2
def baseEnd_4756746 : Nat := 271388561039083493677681

theorem tailTrace_4756746 : CollatzResearch.WordTrace tailWord_4756746 prefixEnd_4756746 271388561039083493677681 := by
  unfold tailWord_4756746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43373194906282276096108523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115661853083419402922956061 43373194906282276096108523)
  ·
    refine ⟨65059792359423414144162785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43373194906282276096108523 65059792359423414144162785)
    ·
      refine ⟨48794844269567560608122089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65059792359423414144162785 48794844269567560608122089)
      ·
        refine ⟨36596133202175670456091567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48794844269567560608122089 36596133202175670456091567)
        ·
          refine ⟨54894199803263505684137351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36596133202175670456091567 54894199803263505684137351)
          ·
            refine ⟨82341299704895258526206027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54894199803263505684137351 82341299704895258526206027)
            ·
              refine ⟨123511949557342887789309041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82341299704895258526206027 123511949557342887789309041)
              ·
                refine ⟨92633962168007165841981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123511949557342887789309041 92633962168007165841981781)
                ·
                  refine ⟨271388561039083493677681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92633962168007165841981781 271388561039083493677681)
                  ·
                    rfl

theorem cell23_4756746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_4756746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756746 prefixEnd_4756746 := by exact prefixLift 4756746
  have htrace : WordTrace (prefixWord ++ tailWord_4756746) baseStart_4756746 baseEnd_4756746 := by
    simpa [prefixWord, tailWord_4756746, baseEnd_4756746] using wordTrace_append hprefix tailTrace_4756746
  have hstable : (prefixWord ++ tailWord_4756746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756746).length < 2 ^ (prefixWord ++ tailWord_4756746).sum := by decide
  have hdescent : baseEnd_4756746 < baseStart_4756746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756750 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_4756750 : Nat := 118140960795 + 4756750 * 2 ^ 59
def prefixEnd_4756750 : Nat := 4983230072969 + 3 ^ 40 * 4756750 * 2
def baseEnd_4756750 : Nat := 814166367758123142483037

theorem tailTrace_4756750 : CollatzResearch.WordTrace tailWord_4756750 prefixEnd_4756750 814166367758123142483037 := by
  unfold tailWord_4756750
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686615689639326633447463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115661950344743075378386469 21686615689639326633447463)
  ·
    refine ⟨32529923534458989950171195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686615689639326633447463 32529923534458989950171195)
    ·
      refine ⟨48794885301688484925256793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32529923534458989950171195 48794885301688484925256793)
      ·
        refine ⟨36596163976266363693942595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48794885301688484925256793 36596163976266363693942595)
        ·
          refine ⟨54894245964399545540913893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36596163976266363693942595 54894245964399545540913893)
          ·
            refine ⟨10292671118324914788921355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54894245964399545540913893 10292671118324914788921355)
            ·
              refine ⟨15439006677487372183382033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10292671118324914788921355 15439006677487372183382033)
              ·
                refine ⟨11579255008115529137536525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15439006677487372183382033 11579255008115529137536525)
                ·
                  refine ⟨4342220628043323426576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11579255008115529137536525 4342220628043323426576197)
                  ·
                    refine ⟨814166367758123142483037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342220628043323426576197 814166367758123142483037)
                    ·
                      rfl

theorem cell23_4756750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_4756750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756750 prefixEnd_4756750 := by exact prefixLift 4756750
  have htrace : WordTrace (prefixWord ++ tailWord_4756750) baseStart_4756750 baseEnd_4756750 := by
    simpa [prefixWord, tailWord_4756750, baseEnd_4756750] using wordTrace_append hprefix tailTrace_4756750
  have hstable : (prefixWord ++ tailWord_4756750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756750).length < 2 ^ (prefixWord ++ tailWord_4756750).sum := by decide
  have hdescent : baseEnd_4756750 < baseStart_4756750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756754 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4756754 : Nat := 118140960795 + 4756754 * 2 ^ 59
def prefixEnd_4756754 : Nat := 4983230072969 + 3 ^ 40 * 4756754 * 2
def baseEnd_4756754 : Nat := 814167052398995803933031

theorem tailTrace_4756754 : CollatzResearch.WordTrace tailWord_4756754 prefixEnd_4756754 814167052398995803933031 := by
  unfold tailWord_4756754
  simp only [CollatzResearch.WordTrace]
  refine ⟨43373267852275030437681329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115662047606066747833816877 43373267852275030437681329)
  ·
    refine ⟨32529950889206272828260997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43373267852275030437681329 32529950889206272828260997)
    ·
      refine ⟨6099365791726176155298937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32529950889206272828260997 6099365791726176155298937)
      ·
        refine ⟨4574524343794632116474203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6099365791726176155298937 4574524343794632116474203)
        ·
          refine ⟨6861786515691948174711305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574524343794632116474203 6861786515691948174711305)
          ·
            refine ⟨5146339886768961131033479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6861786515691948174711305 5146339886768961131033479)
            ·
              refine ⟨7719509830153441696550219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146339886768961131033479 7719509830153441696550219)
              ·
                refine ⟨11579264745230162544825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7719509830153441696550219 11579264745230162544825329)
                ·
                  refine ⟨8684448558922621908618997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579264745230162544825329 8684448558922621908618997)
                  ·
                    refine ⟨814167052398995803933031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8684448558922621908618997 814167052398995803933031)
                    ·
                      rfl

theorem cell23_4756754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4756754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756754 prefixEnd_4756754 := by exact prefixLift 4756754
  have htrace : WordTrace (prefixWord ++ tailWord_4756754) baseStart_4756754 baseEnd_4756754 := by
    simpa [prefixWord, tailWord_4756754, baseEnd_4756754] using wordTrace_append hprefix tailTrace_4756754
  have hstable : (prefixWord ++ tailWord_4756754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756754).length < 2 ^ (prefixWord ++ tailWord_4756754).sum := by decide
  have hdescent : baseEnd_4756754 < baseStart_4756754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756760 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4756760 : Nat := 118140960795 + 4756760 * 2 ^ 59
def prefixEnd_4756760 : Nat := 4983230072969 + 3 ^ 40 * 4756760 * 2
def baseEnd_4756760 : Nat := 2442504238080914388324065

theorem tailTrace_4756760 : CollatzResearch.WordTrace tailWord_4756760 prefixEnd_4756760 2442504238080914388324065 := by
  unfold tailWord_4756760
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746645123539192387721867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115662193498052256516962489 86746645123539192387721867)
  ·
    refine ⟨130119967685308788581582801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86746645123539192387721867 130119967685308788581582801)
    ·
      refine ⟨97589975763981591436187101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130119967685308788581582801 97589975763981591436187101)
      ·
        refine ⟨36596240911493096788570163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97589975763981591436187101 36596240911493096788570163)
        ·
          refine ⟨54894361367239645182855245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36596240911493096788570163 54894361367239645182855245)
          ·
            refine ⟨20585385512714866943570717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54894361367239645182855245 20585385512714866943570717)
            ·
              refine ⟨7719519567268075103839019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20585385512714866943570717 7719519567268075103839019)
              ·
                refine ⟨11579279350902112655758529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7719519567268075103839019 11579279350902112655758529)
                ·
                  refine ⟨8684459513176584491818897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579279350902112655758529 8684459513176584491818897)
                  ·
                    refine ⟨6513344634882438368864173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684459513176584491818897 6513344634882438368864173)
                    ·
                      refine ⟨2442504238080914388324065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513344634882438368864173 2442504238080914388324065)
                      ·
                        rfl

theorem cell23_4756760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4756760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756760 prefixEnd_4756760 := by exact prefixLift 4756760
  have htrace : WordTrace (prefixWord ++ tailWord_4756760) baseStart_4756760 baseEnd_4756760 := by
    simpa [prefixWord, tailWord_4756760, baseEnd_4756760] using wordTrace_append hprefix tailTrace_4756760
  have hstable : (prefixWord ++ tailWord_4756760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756760).length < 2 ^ (prefixWord ++ tailWord_4756760).sum := by decide
  have hdescent : baseEnd_4756760 < baseStart_4756760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756850 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_4756850 : Nat := 118140960795 + 4756850 * 2 ^ 59
def prefixEnd_4756850 : Nat := 4983230072969 + 3 ^ 40 * 4756850 * 2
def baseEnd_4756850 : Nat := 2442550451339819036198651

theorem tailTrace_4756850 : CollatzResearch.WordTrace tailWord_4756850 prefixEnd_4756850 2442550451339819036198651 := by
  unfold tailWord_4756850
  simp only [CollatzResearch.WordTrace]
  refine ⟨43374143204188082536555001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115664381877834886764146669 43374143204188082536555001)
  ·
    refine ⟨32530607403141061902416251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43374143204188082536555001 32530607403141061902416251)
    ·
      refine ⟨48795911104711592853624377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32530607403141061902416251 48795911104711592853624377)
      ·
        refine ⟨36596933328533694640218283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48795911104711592853624377 36596933328533694640218283)
        ·
          refine ⟨54895399992800541960327425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36596933328533694640218283 54895399992800541960327425)
          ·
            refine ⟨41171549994600406470245569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54895399992800541960327425 41171549994600406470245569)
            ·
              refine ⟨30878662495950304852684177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41171549994600406470245569 30878662495950304852684177)
              ·
                refine ⟨23158996871962728639513133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30878662495950304852684177 23158996871962728639513133)
                ·
                  refine ⟨8684623826986023239817425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23158996871962728639513133 8684623826986023239817425)
                  ·
                    refine ⟨6513467870239517429863069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684623826986023239817425 6513467870239517429863069)
                    ·
                      refine ⟨2442550451339819036198651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513467870239517429863069 2442550451339819036198651)
                      ·
                        rfl

theorem cell23_4756850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_4756850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756850 prefixEnd_4756850 := by exact prefixLift 4756850
  have htrace : WordTrace (prefixWord ++ tailWord_4756850) baseStart_4756850 baseEnd_4756850 := by
    simpa [prefixWord, tailWord_4756850, baseEnd_4756850] using wordTrace_append hprefix tailTrace_4756850
  have hstable : (prefixWord ++ tailWord_4756850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756850).length < 2 ^ (prefixWord ++ tailWord_4756850).sum := by decide
  have hdescent : baseEnd_4756850 < baseStart_4756850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756857 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_4756857 : Nat := 118140960795 + 4756857 * 2 ^ 59
def prefixEnd_4756857 : Nat := 4983230072969 + 3 ^ 40 * 4756857 * 2
def baseEnd_4756857 : Nat := 814184681901466836270373

theorem tailTrace_4756857 : CollatzResearch.WordTrace tailWord_4756857 prefixEnd_4756857 814184681901466836270373 := by
  unfold tailWord_4756857
  simp only [CollatzResearch.WordTrace]
  refine ⟨173496828127726970341724825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115664552085151313561149883 173496828127726970341724825)
  ·
    refine ⟨130122621095795227756293619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173496828127726970341724825 130122621095795227756293619)
    ·
      refine ⟨195183931643692841634440429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130122621095795227756293619 195183931643692841634440429)
      ·
        refine ⟨73193974366384815612915161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195183931643692841634440429 73193974366384815612915161)
        ·
          refine ⟨54895480774788611709686371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73193974366384815612915161 54895480774788611709686371)
          ·
            refine ⟨82343221162182917564529557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54895480774788611709686371 82343221162182917564529557)
            ·
              refine ⟨3859838491977324260837323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82343221162182917564529557 3859838491977324260837323)
              ·
                refine ⟨5789757737965986391255985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859838491977324260837323 5789757737965986391255985)
                ·
                  refine ⟨4342318303474489793441989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5789757737965986391255985 4342318303474489793441989)
                  ·
                    refine ⟨814184681901466836270373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342318303474489793441989 814184681901466836270373)
                    ·
                      rfl

theorem cell23_4756857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_4756857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756857 prefixEnd_4756857 := by exact prefixLift 4756857
  have htrace : WordTrace (prefixWord ++ tailWord_4756857) baseStart_4756857 baseEnd_4756857 := by
    simpa [prefixWord, tailWord_4756857, baseEnd_4756857] using wordTrace_append hprefix tailTrace_4756857
  have hstable : (prefixWord ++ tailWord_4756857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756857).length < 2 ^ (prefixWord ++ tailWord_4756857).sum := by decide
  have hdescent : baseEnd_4756857 < baseStart_4756857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756867 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 3]
def baseStart_4756867 : Nat := 118140960795 + 4756867 * 2 ^ 59
def prefixEnd_4756867 : Nat := 4983230072969 + 3 ^ 40 * 4756867 * 2
def baseEnd_4756867 : Nat := 2442559180510945469686073

theorem tailTrace_4756867 : CollatzResearch.WordTrace tailWord_4756867 prefixEnd_4756867 2442559180510945469686073 := by
  unfold tailWord_4756867
  simp only [CollatzResearch.WordTrace]
  refine ⟨173497192857690742049588855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115664795238460494699725903 173497192857690742049588855)
  ·
    refine ⟨260245789286536113074383283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173497192857690742049588855 260245789286536113074383283)
    ·
      refine ⟨390368683929804169611574925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260245789286536113074383283 390368683929804169611574925)
      ·
        refine ⟨146388256473676563604340597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390368683929804169611574925 146388256473676563604340597)
        ·
          refine ⟨13723899044407177837906931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146388256473676563604340597 13723899044407177837906931)
          ·
            refine ⟨20585848566610766756860397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13723899044407177837906931 20585848566610766756860397)
            ·
              refine ⟨7719693212479037533822649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20585848566610766756860397 7719693212479037533822649)
              ·
                refine ⟨5789769909359278150366987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7719693212479037533822649 5789769909359278150366987)
                ·
                  refine ⟨8684654864038917225550481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5789769909359278150366987 8684654864038917225550481)
                  ·
                    refine ⟨6513491148029187919162861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684654864038917225550481 6513491148029187919162861)
                    ·
                      refine ⟨2442559180510945469686073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513491148029187919162861 2442559180510945469686073)
                      ·
                        rfl

theorem cell23_4756867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_4756867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756867 prefixEnd_4756867 := by exact prefixLift 4756867
  have htrace : WordTrace (prefixWord ++ tailWord_4756867) baseStart_4756867 baseEnd_4756867 := by
    simpa [prefixWord, tailWord_4756867, baseEnd_4756867] using wordTrace_append hprefix tailTrace_4756867
  have hstable : (prefixWord ++ tailWord_4756867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756867).length < 2 ^ (prefixWord ++ tailWord_4756867).sum := by decide
  have hdescent : baseEnd_4756867 < baseStart_4756867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756898 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4756898 : Nat := 118140960795 + 4756898 * 2 ^ 59
def prefixEnd_4756898 : Nat := 4983230072969 + 3 ^ 40 * 4756898 * 2
def baseEnd_4756898 : Nat := 2442575098411234848398431

theorem tailTrace_4756898 : CollatzResearch.WordTrace tailWord_4756898 prefixEnd_4756898 2442575098411234848398431 := by
  unfold tailWord_4756898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43374580880144608585991837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115665549013718956229311565 43374580880144608585991837)
  ·
    refine ⟨16265467830054228219746939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43374580880144608585991837 16265467830054228219746939)
    ·
      refine ⟨24398201745081342329620409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265467830054228219746939 24398201745081342329620409)
      ·
        refine ⟨18298651308811006747215307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24398201745081342329620409 18298651308811006747215307)
        ·
          refine ⟨27447976963216510120822961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18298651308811006747215307 27447976963216510120822961)
          ·
            refine ⟨20585982722412382590617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27447976963216510120822961 20585982722412382590617221)
            ·
              refine ⟨3859871760452321735740729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20585982722412382590617221 3859871760452321735740729)
              ·
                refine ⟨2894903820339241301805547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859871760452321735740729 2894903820339241301805547)
                ·
                  refine ⟨4342355730508861952708321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894903820339241301805547 4342355730508861952708321)
                  ·
                    refine ⟨3256766797881646464531241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342355730508861952708321 3256766797881646464531241)
                    ·
                      refine ⟨2442575098411234848398431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256766797881646464531241 2442575098411234848398431)
                      ·
                        rfl

theorem cell23_4756898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4756898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756898 prefixEnd_4756898 := by exact prefixLift 4756898
  have htrace : WordTrace (prefixWord ++ tailWord_4756898) baseStart_4756898 baseEnd_4756898 := by
    simpa [prefixWord, tailWord_4756898, baseEnd_4756898] using wordTrace_append hprefix tailTrace_4756898
  have hstable : (prefixWord ++ tailWord_4756898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756898).length < 2 ^ (prefixWord ++ tailWord_4756898).sum := by decide
  have hdescent : baseEnd_4756898 < baseStart_4756898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756904 : List Nat := [2, 1, 6, 1, 3, 1, 1, 8]
def baseStart_4756904 : Nat := 118140960795 + 4756904 * 2 ^ 59
def prefixEnd_4756904 : Nat := 4983230072969 + 3 ^ 40 * 4756904 * 2
def baseEnd_4756904 : Nat := 90465858492413400923089

theorem tailTrace_4756904 : CollatzResearch.WordTrace tailWord_4756904 prefixEnd_4756904 90465858492413400923089 := by
  unfold tailWord_4756904
  simp only [CollatzResearch.WordTrace]
  refine ⟨86749271179278348684342883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115665694905704464912457177 86749271179278348684342883)
  ·
    refine ⟨130123906768917523026514325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86749271179278348684342883 130123906768917523026514325)
    ·
      refine ⟨6099558129793008891867859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130123906768917523026514325 6099558129793008891867859)
      ·
        refine ⟨9149337194689513337801789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6099558129793008891867859 9149337194689513337801789)
        ·
          refine ⟨3431001448008567501675671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9149337194689513337801789 3431001448008567501675671)
          ·
            refine ⟨5146502172012851252513507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431001448008567501675671 5146502172012851252513507)
            ·
              refine ⟨7719753258019276878770261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146502172012851252513507 7719753258019276878770261)
              ·
                refine ⟨90465858492413400923089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7719753258019276878770261 90465858492413400923089)
                ·
                  rfl

theorem cell23_4756904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 8].length) (baseStart_4756904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756904 prefixEnd_4756904 := by exact prefixLift 4756904
  have htrace : WordTrace (prefixWord ++ tailWord_4756904) baseStart_4756904 baseEnd_4756904 := by
    simpa [prefixWord, tailWord_4756904, baseEnd_4756904] using wordTrace_append hprefix tailTrace_4756904
  have hstable : (prefixWord ++ tailWord_4756904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756904).length < 2 ^ (prefixWord ++ tailWord_4756904).sum := by decide
  have hdescent : baseEnd_4756904 < baseStart_4756904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756937 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 4, 2, 2]
def baseStart_4756937 : Nat := 118140960795 + 4756937 * 2 ^ 59
def prefixEnd_4756937 : Nat := 4983230072969 + 3 ^ 40 * 4756937 * 2
def baseEnd_4756937 : Nat := 2442595124156760195810751

theorem tailTrace_4756937 : CollatzResearch.WordTrace tailWord_4756937 prefixEnd_4756937 2442595124156760195810751 := by
  unfold tailWord_4756937
  simp only [CollatzResearch.WordTrace]
  refine ⟨173499745967437144004637065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115666497311624762669758043 173499745967437144004637065)
  ·
    refine ⟨130124809475577858003477799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173499745967437144004637065 130124809475577858003477799)
    ·
      refine ⟨195187214213366787005216699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130124809475577858003477799 195187214213366787005216699)
      ·
        refine ⟨292780821320050180507825049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195187214213366787005216699 292780821320050180507825049)
        ·
          refine ⟨219585615990037635380868787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292780821320050180507825049 219585615990037635380868787)
          ·
            refine ⟨329378423985056453071303181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219585615990037635380868787 329378423985056453071303181)
            ·
              refine ⟨123516908994396169901738693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329378423985056453071303181 123516908994396169901738693)
              ·
                refine ⟨23159420436449281856576005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123516908994396169901738693 23159420436449281856576005)
                ·
                  refine ⟨4342391331834240348108001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23159420436449281856576005 4342391331834240348108001)
                  ·
                    refine ⟨3256793498875680261081001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342391331834240348108001 3256793498875680261081001)
                    ·
                      refine ⟨2442595124156760195810751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256793498875680261081001 2442595124156760195810751)
                      ·
                        rfl

theorem cell23_4756937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2, 2].length) (baseStart_4756937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756937 prefixEnd_4756937 := by exact prefixLift 4756937
  have htrace : WordTrace (prefixWord ++ tailWord_4756937) baseStart_4756937 baseEnd_4756937 := by
    simpa [prefixWord, tailWord_4756937, baseEnd_4756937] using wordTrace_append hprefix tailTrace_4756937
  have hstable : (prefixWord ++ tailWord_4756937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756937).length < 2 ^ (prefixWord ++ tailWord_4756937).sum := by decide
  have hdescent : baseEnd_4756937 < baseStart_4756937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756948 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_4756948 : Nat := 118140960795 + 4756948 * 2 ^ 59
def prefixEnd_4756948 : Nat := 4983230072969 + 3 ^ 40 * 4756948 * 2
def baseEnd_4756948 : Nat := 2442600772443959652773201

theorem tailTrace_4756948 : CollatzResearch.WordTrace tailWord_4756948 prefixEnd_4756948 2442600772443959652773201 := by
  unfold tailWord_4756948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86750073585198646441643749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115666764780264861922191665 86750073585198646441643749)
  ·
    refine ⟨16265638797224746207808203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86750073585198646441643749 16265638797224746207808203)
    ·
      refine ⟨24398458195837119311712305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265638797224746207808203 24398458195837119311712305)
      ·
        refine ⟨18298843646877839483784229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24398458195837119311712305 18298843646877839483784229)
        ·
          refine ⟨3431033183789594903209543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18298843646877839483784229 3431033183789594903209543)
          ·
            refine ⟨5146549775684392354814315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431033183789594903209543 5146549775684392354814315)
            ·
              refine ⟨7719824663526588532221473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146549775684392354814315 7719824663526588532221473)
              ·
                refine ⟨5789868497644941399166105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7719824663526588532221473 5789868497644941399166105)
                ·
                  refine ⟨4342401373233706049374579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5789868497644941399166105 4342401373233706049374579)
                  ·
                    refine ⟨6513602059850559074061869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342401373233706049374579 6513602059850559074061869)
                    ·
                      refine ⟨2442600772443959652773201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513602059850559074061869 2442600772443959652773201)
                      ·
                        rfl

theorem cell23_4756948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_4756948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756948 prefixEnd_4756948 := by exact prefixLift 4756948
  have htrace : WordTrace (prefixWord ++ tailWord_4756948) baseStart_4756948 baseEnd_4756948 := by
    simpa [prefixWord, tailWord_4756948, baseEnd_4756948] using wordTrace_append hprefix tailTrace_4756948
  have hstable : (prefixWord ++ tailWord_4756948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756948).length < 2 ^ (prefixWord ++ tailWord_4756948).sum := by decide
  have hdescent : baseEnd_4756948 < baseStart_4756948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756954 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_4756954 : Nat := 118140960795 + 4756954 * 2 ^ 59
def prefixEnd_4756954 : Nat := 4983230072969 + 3 ^ 40 * 4756954 * 2
def baseEnd_4756954 : Nat := 2442603853327886629298173

theorem tailTrace_4756954 : CollatzResearch.WordTrace tailWord_4756954 prefixEnd_4756954 2442603853327886629298173 := by
  unfold tailWord_4756954
  simp only [CollatzResearch.WordTrace]
  refine ⟨43375091502093888977001479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115666910672250370605337277 43375091502093888977001479)
  ·
    refine ⟨65062637253140833465502219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43375091502093888977001479 65062637253140833465502219)
    ·
      refine ⟨97593955879711250198253329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65062637253140833465502219 97593955879711250198253329)
      ·
        refine ⟨73195466909783437648689997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97593955879711250198253329 73195466909783437648689997)
        ·
          refine ⟨27448300091168789118258749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73195466909783437648689997 27448300091168789118258749)
          ·
            refine ⟨10293112534188295919347031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27448300091168789118258749 10293112534188295919347031)
            ·
              refine ⟨15439668801282443879020547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293112534188295919347031 15439668801282443879020547)
              ·
                refine ⟨23159503201923665818530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15439668801282443879020547 23159503201923665818530821)
                ·
                  refine ⟨4342406850360687340974529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23159503201923665818530821 4342406850360687340974529)
                  ·
                    refine ⟨3256805137770515505730897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342406850360687340974529 3256805137770515505730897)
                    ·
                      refine ⟨2442603853327886629298173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256805137770515505730897 2442603853327886629298173)
                      ·
                        rfl

theorem cell23_4756954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_4756954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756954 prefixEnd_4756954 := by exact prefixLift 4756954
  have htrace : WordTrace (prefixWord ++ tailWord_4756954) baseStart_4756954 baseEnd_4756954 := by
    simpa [prefixWord, tailWord_4756954, baseEnd_4756954] using wordTrace_append hprefix tailTrace_4756954
  have hstable : (prefixWord ++ tailWord_4756954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756954).length < 2 ^ (prefixWord ++ tailWord_4756954).sum := by decide
  have hdescent : baseEnd_4756954 < baseStart_4756954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4756983 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4756983 : Nat := 118140960795 + 4756983 * 2 ^ 59
def prefixEnd_4756983 : Nat := 4983230072969 + 3 ^ 40 * 4756983 * 2
def baseEnd_4756983 : Nat := 2442618744266867015835539

theorem tailTrace_4756983 : CollatzResearch.WordTrace tailWord_4756983 prefixEnd_4756983 2442618744266867015835539 := by
  unfold tailWord_4756983
  simp only [CollatzResearch.WordTrace]
  refine ⟨173501423725270493860811603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115667615816846995907207735 173501423725270493860811603)
  ·
    refine ⟨260252135587905740791217405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173501423725270493860811603 260252135587905740791217405)
    ·
      refine ⟨97594550845464652796706527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260252135587905740791217405 97594550845464652796706527)
      ·
        refine ⟨146391826268196979195059791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97594550845464652796706527 146391826268196979195059791)
        ·
          refine ⟨219587739402295468792589687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146391826268196979195059791 219587739402295468792589687)
          ·
            refine ⟨329381609103443203188884531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219587739402295468792589687 329381609103443203188884531)
            ·
              refine ⟨494072413655164804783326797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329381609103443203188884531 494072413655164804783326797)
              ·
                refine ⟨185277155120686801793747549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494072413655164804783326797 185277155120686801793747549)
                ·
                  refine ⟨69478933170257550672655331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185277155120686801793747549 69478933170257550672655331)
                  ·
                    refine ⟨104218399755386326008982997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69478933170257550672655331 104218399755386326008982997)
                    ·
                      refine ⟨2442618744266867015835539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104218399755386326008982997 2442618744266867015835539)
                      ·
                        rfl

theorem cell23_4756983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4756983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4756983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4756983 prefixEnd_4756983 := by exact prefixLift 4756983
  have htrace : WordTrace (prefixWord ++ tailWord_4756983) baseStart_4756983 baseEnd_4756983 := by
    simpa [prefixWord, tailWord_4756983, baseEnd_4756983] using wordTrace_append hprefix tailTrace_4756983
  have hstable : (prefixWord ++ tailWord_4756983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4756983).length < 2 ^ (prefixWord ++ tailWord_4756983).sum := by decide
  have hdescent : baseEnd_4756983 < baseStart_4756983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4756983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757022 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4757022 : Nat := 118140960795 + 4757022 * 2 ^ 59
def prefixEnd_4757022 : Nat := 4983230072969 + 3 ^ 40 * 4757022 * 2
def baseEnd_4757022 : Nat := 2442638770012392363247861

theorem tailTrace_4757022 : CollatzResearch.WordTrace tailWord_4757022 prefixEnd_4757022 2442638770012392363247861 := by
  unfold tailWord_4757022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687855771516150440185165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115668564114752802347654213 21687855771516150440185165)
  ·
    refine ⟨8132945914318556415069437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21687855771516150440185165 8132945914318556415069437)
    ·
      refine ⟨3049854717869458655651039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8132945914318556415069437 3049854717869458655651039)
      ·
        refine ⟨4574782076804187983476559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049854717869458655651039 4574782076804187983476559)
        ·
          refine ⟨6862173115206281975214839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574782076804187983476559 6862173115206281975214839)
          ·
            refine ⟨10293259672809422962822259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862173115206281975214839 10293259672809422962822259)
            ·
              refine ⟨15439889509214134444233389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293259672809422962822259 15439889509214134444233389)
              ·
                refine ⟨5789958565955300416587521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15439889509214134444233389 5789958565955300416587521)
                ·
                  refine ⟨4342468924466475312440641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5789958565955300416587521 4342468924466475312440641)
                  ·
                    refine ⟨3256851693349856484330481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342468924466475312440641 3256851693349856484330481)
                    ·
                      refine ⟨2442638770012392363247861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256851693349856484330481 2442638770012392363247861)
                      ·
                        rfl

theorem cell23_4757022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4757022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757022 prefixEnd_4757022 := by exact prefixLift 4757022
  have htrace : WordTrace (prefixWord ++ tailWord_4757022) baseStart_4757022 baseEnd_4757022 := by
    simpa [prefixWord, tailWord_4757022, baseEnd_4757022] using wordTrace_append hprefix tailTrace_4757022
  have hstable : (prefixWord ++ tailWord_4757022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757022).length < 2 ^ (prefixWord ++ tailWord_4757022).sum := by decide
  have hdescent : baseEnd_4757022 < baseStart_4757022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757047 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_4757047 : Nat := 118140960795 + 4757047 * 2 ^ 59
def prefixEnd_4757047 : Nat := 4983230072969 + 3 ^ 40 * 4757047 * 2
def baseEnd_4757047 : Nat := 2442651607028754765435245

theorem tailTrace_4757047 : CollatzResearch.WordTrace tailWord_4757047 prefixEnd_4757047 2442651607028754765435245 := by
  unfold tailWord_4757047
  simp only [CollatzResearch.WordTrace]
  refine ⟨173503757997038632791141395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115669171998025755194094263 173503757997038632791141395)
  ·
    refine ⟨260255636995557949186712093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173503757997038632791141395 260255636995557949186712093)
    ·
      refine ⟨97595863873334230945017035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260255636995557949186712093 97595863873334230945017035)
      ·
        refine ⟨146393795810001346417525553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97595863873334230945017035 146393795810001346417525553)
        ·
          refine ⟨109795346857501009813144165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146393795810001346417525553 109795346857501009813144165)
          ·
            refine ⟨20586627535781439339964531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109795346857501009813144165 20586627535781439339964531)
            ·
              refine ⟨30879941303672159009946797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20586627535781439339964531 30879941303672159009946797)
              ·
                refine ⟨11579977988877059628730049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30879941303672159009946797 11579977988877059628730049)
                ·
                  refine ⟨8684983491657794721547537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579977988877059628730049 8684983491657794721547537)
                  ·
                    refine ⟨6513737618743346041160653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684983491657794721547537 6513737618743346041160653)
                    ·
                      refine ⟨2442651607028754765435245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513737618743346041160653 2442651607028754765435245)
                      ·
                        rfl

theorem cell23_4757047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_4757047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757047 prefixEnd_4757047 := by exact prefixLift 4757047
  have htrace : WordTrace (prefixWord ++ tailWord_4757047) baseStart_4757047 baseEnd_4757047 := by
    simpa [prefixWord, tailWord_4757047, baseEnd_4757047] using wordTrace_append hprefix tailTrace_4757047
  have hstable : (prefixWord ++ tailWord_4757047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757047).length < 2 ^ (prefixWord ++ tailWord_4757047).sum := by decide
  have hdescent : baseEnd_4757047 < baseStart_4757047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757070 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4757070 : Nat := 118140960795 + 4757070 * 2 ^ 59
def prefixEnd_4757070 : Nat := 4983230072969 + 3 ^ 40 * 4757070 * 2
def baseEnd_4757070 : Nat := 2442663417083808175447639

theorem tailTrace_4757070 : CollatzResearch.WordTrace tailWord_4757070 prefixEnd_4757070 2442663417083808175447639 := by
  unfold tailWord_4757070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21688074609494413464903583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115669731250636871812819109 21688074609494413464903583)
  ·
    refine ⟨32532111914241620197355375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21688074609494413464903583 32532111914241620197355375)
    ·
      refine ⟨48798167871362430296033063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32532111914241620197355375 48798167871362430296033063)
      ·
        refine ⟨73197251807043645444049595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48798167871362430296033063 73197251807043645444049595)
        ·
          refine ⟨109795877710565468166074393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73197251807043645444049595 109795877710565468166074393)
          ·
            refine ⟨82346908282924101124555795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109795877710565468166074393 82346908282924101124555795)
            ·
              refine ⟨123520362424386151686833693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82346908282924101124555795 123520362424386151686833693)
              ·
                refine ⟨46320135909144806882562635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123520362424386151686833693 46320135909144806882562635)
                ·
                  refine ⟨69480203863717210323843953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46320135909144806882562635 69480203863717210323843953)
                  ·
                    refine ⟨52110152897787907742882965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69480203863717210323843953 52110152897787907742882965)
                    ·
                      refine ⟨2442663417083808175447639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52110152897787907742882965 2442663417083808175447639)
                      ·
                        rfl

theorem cell23_4757070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4757070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757070 prefixEnd_4757070 := by exact prefixLift 4757070
  have htrace : WordTrace (prefixWord ++ tailWord_4757070) baseStart_4757070 baseEnd_4757070 := by
    simpa [prefixWord, tailWord_4757070, baseEnd_4757070] using wordTrace_append hprefix tailTrace_4757070
  have hstable : (prefixWord ++ tailWord_4757070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757070).length < 2 ^ (prefixWord ++ tailWord_4757070).sum := by decide
  have hdescent : baseEnd_4757070 < baseStart_4757070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757104 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2]
def baseStart_4757104 : Nat := 118140960795 + 4757104 * 2 ^ 59
def prefixEnd_4757104 : Nat := 4983230072969 + 3 ^ 40 * 4757104 * 2
def baseEnd_4757104 : Nat := 2442680875426061042422483

theorem tailTrace_4757104 : CollatzResearch.WordTrace tailWord_4757104 prefixEnd_4757104 2442680875426061042422483 := by
  unfold tailWord_4757104
  simp only [CollatzResearch.WordTrace]
  refine ⟨86752918478916065762983183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115670557971888087683977577 86752918478916065762983183)
  ·
    refine ⟨130129377718374098644474775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86752918478916065762983183 130129377718374098644474775)
    ·
      refine ⟨195194066577561147966712163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130129377718374098644474775 195194066577561147966712163)
      ·
        refine ⟨292791099866341721950068245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195194066577561147966712163 292791099866341721950068245)
        ·
          refine ⟨13724582806234768216409449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 292791099866341721950068245 13724582806234768216409449)
          ·
            refine ⟨10293437104676076162307087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13724582806234768216409449 10293437104676076162307087)
            ·
              refine ⟨15440155657014114243460631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293437104676076162307087 15440155657014114243460631)
              ·
                refine ⟨23160233485521171365190947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15440155657014114243460631 23160233485521171365190947)
                ·
                  refine ⟨34740350228281757047786421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23160233485521171365190947 34740350228281757047786421)
                  ·
                    refine ⟨3256907833901414723229977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34740350228281757047786421 3256907833901414723229977)
                    ·
                      refine ⟨2442680875426061042422483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256907833901414723229977 2442680875426061042422483)
                      ·
                        rfl

theorem cell23_4757104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2].length) (baseStart_4757104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757104 prefixEnd_4757104 := by exact prefixLift 4757104
  have htrace : WordTrace (prefixWord ++ tailWord_4757104) baseStart_4757104 baseEnd_4757104 := by
    simpa [prefixWord, tailWord_4757104, baseEnd_4757104] using wordTrace_append hprefix tailTrace_4757104
  have hstable : (prefixWord ++ tailWord_4757104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757104).length < 2 ^ (prefixWord ++ tailWord_4757104).sum := by decide
  have hdescent : baseEnd_4757104 < baseStart_4757104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757128 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4757128 : Nat := 118140960795 + 4757128 * 2 ^ 59
def prefixEnd_4757128 : Nat := 4983230072969 + 3 ^ 40 * 4757128 * 2
def baseEnd_4757128 : Nat := 2442693198961768948522373

theorem tailTrace_4757128 : CollatzResearch.WordTrace tailWord_4757128 prefixEnd_4757128 2442693198961768948522373 := by
  unfold tailWord_4757128
  simp only [CollatzResearch.WordTrace]
  refine ⟨86753356154872591812420019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115671141539830122416560025 86753356154872591812420019)
  ·
    refine ⟨130130034232308887718630029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86753356154872591812420019 130130034232308887718630029)
    ·
      refine ⟨48798762837115832894486261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130130034232308887718630029 48798762837115832894486261)
      ·
        refine ⟨4574884015979609333858087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48798762837115832894486261 4574884015979609333858087)
        ·
          refine ⟨6862326023969414000787131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574884015979609333858087 6862326023969414000787131)
          ·
            refine ⟨10293489035954121001180697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862326023969414000787131 10293489035954121001180697)
            ·
              refine ⟨7720116776965590750885523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10293489035954121001180697 7720116776965590750885523)
              ·
                refine ⟨11580175165448386126328285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720116776965590750885523 11580175165448386126328285)
                ·
                  refine ⟨4342565687043144797373107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11580175165448386126328285 4342565687043144797373107)
                  ·
                    refine ⟨6513848530564717196059661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342565687043144797373107 6513848530564717196059661)
                    ·
                      refine ⟨2442693198961768948522373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513848530564717196059661 2442693198961768948522373)
                      ·
                        rfl

theorem cell23_4757128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4757128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757128 prefixEnd_4757128 := by exact prefixLift 4757128
  have htrace : WordTrace (prefixWord ++ tailWord_4757128) baseStart_4757128 baseEnd_4757128 := by
    simpa [prefixWord, tailWord_4757128, baseEnd_4757128] using wordTrace_append hprefix tailTrace_4757128
  have hstable : (prefixWord ++ tailWord_4757128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757128).length < 2 ^ (prefixWord ++ tailWord_4757128).sum := by decide
  have hdescent : baseEnd_4757128 < baseStart_4757128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757137 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_4757137 : Nat := 118140960795 + 4757137 * 2 ^ 59
def prefixEnd_4757137 : Nat := 4983230072969 + 3 ^ 40 * 4757137 * 2
def baseEnd_4757137 : Nat := 2442697820287659413309831

theorem tailTrace_4757137 : CollatzResearch.WordTrace tailWord_4757137 prefixEnd_4757137 2442697820287659413309831 := by
  unfold tailWord_4757137
  simp only [CollatzResearch.WordTrace]
  refine ⟨173507040566712578161917665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115671360377808385441278443 173507040566712578161917665)
  ·
    refine ⟨130130280425034433621438249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173507040566712578161917665 130130280425034433621438249)
    ·
      refine ⟨97597710318775825216078687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130130280425034433621438249 97597710318775825216078687)
      ·
        refine ⟨146396565478163737824118031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97597710318775825216078687 146396565478163737824118031)
        ·
          refine ⟨219594848217245606736177047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146396565478163737824118031 219594848217245606736177047)
          ·
            refine ⟨329392272325868410104265571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219594848217245606736177047 329392272325868410104265571)
            ·
              refine ⟨494088408488802615156398357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329392272325868410104265571 494088408488802615156398357)
              ·
                refine ⟨23160394147912622585456173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 494088408488802615156398357 23160394147912622585456173)
                ·
                  refine ⟨8685147805467233469546065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23160394147912622585456173 8685147805467233469546065)
                  ·
                    refine ⟨6513860854100425102159549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8685147805467233469546065 6513860854100425102159549)
                    ·
                      refine ⟨2442697820287659413309831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513860854100425102159549 2442697820287659413309831)
                      ·
                        rfl

theorem cell23_4757137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_4757137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757137 prefixEnd_4757137 := by exact prefixLift 4757137
  have htrace : WordTrace (prefixWord ++ tailWord_4757137) baseStart_4757137 baseEnd_4757137 := by
    simpa [prefixWord, tailWord_4757137, baseEnd_4757137] using wordTrace_append hprefix tailTrace_4757137
  have hstable : (prefixWord ++ tailWord_4757137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757137).length < 2 ^ (prefixWord ++ tailWord_4757137).sum := by decide
  have hdescent : baseEnd_4757137 < baseStart_4757137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757144 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_4757144 : Nat := 118140960795 + 4757144 * 2 ^ 59
def prefixEnd_4757144 : Nat := 4983230072969 + 3 ^ 40 * 4757144 * 2
def baseEnd_4757144 : Nat := 814233804884080295307433

theorem tailTrace_4757144 : CollatzResearch.WordTrace tailWord_4757144 prefixEnd_4757144 814233804884080295307433 := by
  unfold tailWord_4757144
  simp only [CollatzResearch.WordTrace]
  refine ⟨86753647938843609178711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115671530585124812238281657 86753647938843609178711243)
  ·
    refine ⟨130130471908265413768066865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86753647938843609178711243 130130471908265413768066865)
    ·
      refine ⟨97597853931199060326050149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130130471908265413768066865 97597853931199060326050149)
      ·
        refine ⟨18299597612099823811134403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97597853931199060326050149 18299597612099823811134403)
        ·
          refine ⟨27449396418149735716701605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18299597612099823811134403 27449396418149735716701605)
          ·
            refine ⟨5146761828403075446881551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27449396418149735716701605 5146761828403075446881551)
            ·
              refine ⟨7720142742604613170322327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146761828403075446881551 7720142742604613170322327)
              ·
                refine ⟨11580214113906919755483491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720142742604613170322327 11580214113906919755483491)
                ·
                  refine ⟨17370321170860379633225237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11580214113906919755483491 17370321170860379633225237)
                  ·
                    refine ⟨814233804884080295307433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17370321170860379633225237 814233804884080295307433)
                    ·
                      rfl

theorem cell23_4757144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_4757144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757144 prefixEnd_4757144 := by exact prefixLift 4757144
  have htrace : WordTrace (prefixWord ++ tailWord_4757144) baseStart_4757144 baseEnd_4757144 := by
    simpa [prefixWord, tailWord_4757144, baseEnd_4757144] using wordTrace_append hprefix tailTrace_4757144
  have hstable : (prefixWord ++ tailWord_4757144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757144).length < 2 ^ (prefixWord ++ tailWord_4757144).sum := by decide
  have hdescent : baseEnd_4757144 < baseStart_4757144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757157 : List Nat := [1, 3, 1, 2, 1, 2, 6, 7]
def baseStart_4757157 : Nat := 118140960795 + 4757157 * 2 ^ 59
def prefixEnd_4757157 : Nat := 4983230072969 + 3 ^ 40 * 4757157 * 2
def baseEnd_4757157 : Nat := 90470669996324049446657

theorem tailTrace_4757157 : CollatzResearch.WordTrace tailWord_4757157 prefixEnd_4757157 90470669996324049446657 := by
  unfold tailWord_4757157
  simp only [CollatzResearch.WordTrace]
  refine ⟨173507770026640121577645725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115671846684426747718430483 173507770026640121577645725)
  ·
    refine ⟨65065413759990045591617147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173507770026640121577645725 65065413759990045591617147)
    ·
      refine ⟨97598120639985068387425721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65065413759990045591617147 97598120639985068387425721)
      ·
        refine ⟨73198590479988801290569291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97598120639985068387425721 73198590479988801290569291)
        ·
          refine ⟨109797885719983201935853937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73198590479988801290569291 109797885719983201935853937)
          ·
            refine ⟨82348414289987401451890453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109797885719983201935853937 82348414289987401451890453)
            ·
              refine ⟨3860081919843159443057365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82348414289987401451890453 3860081919843159443057365)
              ·
                refine ⟨90470669996324049446657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3860081919843159443057365 90470669996324049446657)
                ·
                  rfl

theorem cell23_4757157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 7].length) (baseStart_4757157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757157 prefixEnd_4757157 := by exact prefixLift 4757157
  have htrace : WordTrace (prefixWord ++ tailWord_4757157) baseStart_4757157 baseEnd_4757157 := by
    simpa [prefixWord, tailWord_4757157, baseEnd_4757157] using wordTrace_append hprefix tailTrace_4757157
  have hstable : (prefixWord ++ tailWord_4757157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757157).length < 2 ^ (prefixWord ++ tailWord_4757157).sum := by decide
  have hdescent : baseEnd_4757157 < baseStart_4757157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757167 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_4757167 : Nat := 118140960795 + 4757167 * 2 ^ 59
def prefixEnd_4757167 : Nat := 4983230072969 + 3 ^ 40 * 4757167 * 2
def baseEnd_4757167 : Nat := 2442713224707294295934693

theorem tailTrace_4757167 : CollatzResearch.WordTrace tailWord_4757167 prefixEnd_4757167 2442713224707294295934693 := by
  unfold tailWord_4757167
  simp only [CollatzResearch.WordTrace]
  refine ⟨173508134756603893285509755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115672089837735928857006503 173508134756603893285509755)
  ·
    refine ⟨260262202134905839928264633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173508134756603893285509755 260262202134905839928264633)
    ·
      refine ⟨195196651601179379946198475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260262202134905839928264633 195196651601179379946198475)
      ·
        refine ⟨292794977401769069919297713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195196651601179379946198475 292794977401769069919297713)
        ·
          refine ⟨219596233051326802439473285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292794977401769069919297713 219596233051326802439473285)
          ·
            refine ⟨41174293697123775457401241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219596233051326802439473285 41174293697123775457401241)
            ·
              refine ⟨30880720272842831593050931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41174293697123775457401241 30880720272842831593050931)
              ·
                refine ⟨46321080409264247389576397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30880720272842831593050931 46321080409264247389576397)
                ·
                  refine ⟨17370405153474092771091149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46321080409264247389576397 17370405153474092771091149)
                  ·
                    refine ⟨6513901932552784789159181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17370405153474092771091149 6513901932552784789159181)
                    ·
                      refine ⟨2442713224707294295934693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513901932552784789159181 2442713224707294295934693)
                      ·
                        rfl

theorem cell23_4757167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_4757167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757167 prefixEnd_4757167 := by exact prefixLift 4757167
  have htrace : WordTrace (prefixWord ++ tailWord_4757167) baseStart_4757167 baseEnd_4757167 := by
    simpa [prefixWord, tailWord_4757167, baseEnd_4757167] using wordTrace_append hprefix tailTrace_4757167
  have hstable : (prefixWord ++ tailWord_4757167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757167).length < 2 ^ (prefixWord ++ tailWord_4757167).sum := by decide
  have hdescent : baseEnd_4757167 < baseStart_4757167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757168 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 1, 2, 2]
def baseStart_4757168 : Nat := 118140960795 + 4757168 * 2 ^ 59
def prefixEnd_4757168 : Nat := 4983230072969 + 3 ^ 40 * 4757168 * 2
def baseEnd_4757168 : Nat := 2442713738187948792022189

theorem tailTrace_4757168 : CollatzResearch.WordTrace tailWord_4757168 prefixEnd_4757168 2442713738187948792022189 := by
  unfold tailWord_4757168
  simp only [CollatzResearch.WordTrace]
  refine ⟨86754085614800135228148079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115672114153066846970864105 86754085614800135228148079)
  ·
    refine ⟨130131128422200202842222119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86754085614800135228148079 130131128422200202842222119)
    ·
      refine ⟨195196692633300304263333179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130131128422200202842222119 195196692633300304263333179)
      ·
        refine ⟨292795038949950456394999769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195196692633300304263333179 292795038949950456394999769)
        ·
          refine ⟨219596279212462842296249827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292795038949950456394999769 219596279212462842296249827)
          ·
            refine ⟨329394418818694263444374741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219596279212462842296249827 329394418818694263444374741)
            ·
              refine ⟨7720181691063146799477533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 329394418818694263444374741 7720181691063146799477533)
              ·
                refine ⟨2895068134148680049804075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7720181691063146799477533 2895068134148680049804075)
                ·
                  refine ⟨4342602201223020074706113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895068134148680049804075 4342602201223020074706113)
                  ·
                    refine ⟨3256951650917265056029585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342602201223020074706113 3256951650917265056029585)
                    ·
                      refine ⟨2442713738187948792022189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256951650917265056029585 2442713738187948792022189)
                      ·
                        rfl

theorem cell23_4757168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 2, 2].length) (baseStart_4757168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757168 prefixEnd_4757168 := by exact prefixLift 4757168
  have htrace : WordTrace (prefixWord ++ tailWord_4757168) baseStart_4757168 baseEnd_4757168 := by
    simpa [prefixWord, tailWord_4757168, baseEnd_4757168] using wordTrace_append hprefix tailTrace_4757168
  have hstable : (prefixWord ++ tailWord_4757168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757168).length < 2 ^ (prefixWord ++ tailWord_4757168).sum := by decide
  have hdescent : baseEnd_4757168 < baseStart_4757168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757174 : List Nat := [5, 1, 3, 1, 1, 1, 11]
def baseStart_4757174 : Nat := 118140960795 + 4757174 * 2 ^ 59
def prefixEnd_4757174 : Nat := 4983230072969 + 3 ^ 40 * 4757174 * 2
def baseEnd_4757174 : Nat := 30156997766319453932681

theorem tailTrace_4757174 : CollatzResearch.WordTrace tailWord_4757174 prefixEnd_4757174 30156997766319453932681 := by
  unfold tailWord_4757174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844274379223658342563411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115672260045052355654009717 10844274379223658342563411)
  ·
    refine ⟨16266411568835487513845117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844274379223658342563411 16266411568835487513845117)
    ·
      refine ⟨6099904338313307817691919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16266411568835487513845117 6099904338313307817691919)
      ·
        refine ⟨9149856507469961726537879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6099904338313307817691919 9149856507469961726537879)
        ·
          refine ⟨13724784761204942589806819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149856507469961726537879 13724784761204942589806819)
          ·
            refine ⟨20587177141807413884710229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13724784761204942589806819 20587177141807413884710229)
            ·
              refine ⟨30156997766319453932681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20587177141807413884710229 30156997766319453932681)
              ·
                rfl

theorem cell23_4757174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 11].length) (baseStart_4757174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757174 prefixEnd_4757174 := by exact prefixLift 4757174
  have htrace : WordTrace (prefixWord ++ tailWord_4757174) baseStart_4757174 baseEnd_4757174 := by
    simpa [prefixWord, tailWord_4757174, baseEnd_4757174] using wordTrace_append hprefix tailTrace_4757174
  have hstable : (prefixWord ++ tailWord_4757174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757174).length < 2 ^ (prefixWord ++ tailWord_4757174).sum := by decide
  have hdescent : baseEnd_4757174 < baseStart_4757174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757184 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_4757184 : Nat := 118140960795 + 4757184 * 2 ^ 59
def prefixEnd_4757184 : Nat := 4983230072969 + 3 ^ 40 * 4757184 * 2
def baseEnd_4757184 : Nat := 2442721953878420729422115

theorem tailTrace_4757184 : CollatzResearch.WordTrace tailWord_4757184 prefixEnd_4757184 2442721953878420729422115 := by
  unfold tailWord_4757184
  simp only [CollatzResearch.WordTrace]
  refine ⟨86754377398771152594439303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115672503198361536792585737 86754377398771152594439303)
  ·
    refine ⟨130131566098156728891658955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86754377398771152594439303 130131566098156728891658955)
    ·
      refine ⟨195197349147235093337488433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130131566098156728891658955 195197349147235093337488433)
      ·
        refine ⟨146398011860426320003116325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195197349147235093337488433 146398011860426320003116325)
        ·
          refine ⟨27449627223829935000584311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146398011860426320003116325 27449627223829935000584311)
          ·
            refine ⟨41174440835744902500876467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27449627223829935000584311 41174440835744902500876467)
            ·
              refine ⟨61761661253617353751314701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41174440835744902500876467 61761661253617353751314701)
              ·
                refine ⟨23160622970106507656743013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61761661253617353751314701 23160622970106507656743013)
                ·
                  refine ⟨4342616806894970185639315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23160622970106507656743013 4342616806894970185639315)
                  ·
                    refine ⟨6513925210342455278458973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342616806894970185639315 6513925210342455278458973)
                    ·
                      refine ⟨2442721953878420729422115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513925210342455278458973 2442721953878420729422115)
                      ·
                        rfl

theorem cell23_4757184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_4757184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757184 prefixEnd_4757184 := by exact prefixLift 4757184
  have htrace : WordTrace (prefixWord ++ tailWord_4757184) baseStart_4757184 baseEnd_4757184 := by
    simpa [prefixWord, tailWord_4757184, baseEnd_4757184] using wordTrace_append hprefix tailTrace_4757184
  have hstable : (prefixWord ++ tailWord_4757184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757184).length < 2 ^ (prefixWord ++ tailWord_4757184).sum := by decide
  have hdescent : baseEnd_4757184 < baseStart_4757184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757201 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_4757201 : Nat := 118140960795 + 4757201 * 2 ^ 59
def prefixEnd_4757201 : Nat := 4983230072969 + 3 ^ 40 * 4757201 * 2
def baseEnd_4757201 : Nat := 2442730683049547162909537

theorem tailTrace_4757201 : CollatzResearch.WordTrace tailWord_4757201 prefixEnd_4757201 2442730683049547162909537 := by
  unfold tailWord_4757201
  simp only [CollatzResearch.WordTrace]
  refine ⟨173509374838480717092247457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115672916558987144728164971 173509374838480717092247457)
  ·
    refine ⟨130132031128860537819185593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173509374838480717092247457 130132031128860537819185593)
    ·
      refine ⟨97599023346645403364389195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130132031128860537819185593 97599023346645403364389195)
      ·
        refine ⟨146398535019968105046583793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97599023346645403364389195 146398535019968105046583793)
        ·
          refine ⟨109798901264976078784937845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146398535019968105046583793 109798901264976078784937845)
          ·
            refine ⟨10293646993591507386087923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109798901264976078784937845 10293646993591507386087923)
            ·
              refine ⟨15440470490387261079131885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293646993591507386087923 15440470490387261079131885)
              ·
                refine ⟨5790176433895222904674457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15440470490387261079131885 5790176433895222904674457)
                ·
                  refine ⟨4342632325421417178505843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5790176433895222904674457 4342632325421417178505843)
                  ·
                    refine ⟨6513948488132125767758765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342632325421417178505843 6513948488132125767758765)
                    ·
                      refine ⟨2442730683049547162909537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6513948488132125767758765 2442730683049547162909537)
                      ·
                        rfl

theorem cell23_4757201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_4757201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757201 prefixEnd_4757201 := by exact prefixLift 4757201
  have htrace : WordTrace (prefixWord ++ tailWord_4757201) baseStart_4757201 baseEnd_4757201 := by
    simpa [prefixWord, tailWord_4757201, baseEnd_4757201] using wordTrace_append hprefix tailTrace_4757201
  have hstable : (prefixWord ++ tailWord_4757201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757201).length < 2 ^ (prefixWord ++ tailWord_4757201).sum := by decide
  have hdescent : baseEnd_4757201 < baseStart_4757201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757227 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_4757227 : Nat := 118140960795 + 4757227 * 2 ^ 59
def prefixEnd_4757227 : Nat := 4983230072969 + 3 ^ 40 * 4757227 * 2
def baseEnd_4757227 : Nat := 2442744033546564061184417

theorem tailTrace_4757227 : CollatzResearch.WordTrace tailWord_4757227 prefixEnd_4757227 2442744033546564061184417 := by
  unfold tailWord_4757227
  simp only [CollatzResearch.WordTrace]
  refine ⟨173510323136386523532693935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115673548757591015688462623 173510323136386523532693935)
  ·
    refine ⟨260265484704579785299040903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173510323136386523532693935 260265484704579785299040903)
    ·
      refine ⟨390398227056869677948561355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260265484704579785299040903 390398227056869677948561355)
      ·
        refine ⟨585597340585304516922842033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390398227056869677948561355 585597340585304516922842033)
        ·
          refine ⟨439198005438978387692131525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585597340585304516922842033 439198005438978387692131525)
          ·
            refine ⟨82349626019808447692274661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 439198005438978387692131525 82349626019808447692274661)
            ·
              refine ⟨15440554878714083942301499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82349626019808447692274661 15440554878714083942301499)
              ·
                refine ⟨23160832318071125913452249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15440554878714083942301499 23160832318071125913452249)
                ·
                  refine ⟨17370624238553344435089187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23160832318071125913452249 17370624238553344435089187)
                  ·
                    refine ⟨26055936357830016652633781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17370624238553344435089187 26055936357830016652633781)
                    ·
                      refine ⟨2442744033546564061184417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26055936357830016652633781 2442744033546564061184417)
                      ·
                        rfl

theorem cell23_4757227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_4757227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757227 prefixEnd_4757227 := by exact prefixLift 4757227
  have htrace : WordTrace (prefixWord ++ tailWord_4757227) baseStart_4757227 baseEnd_4757227 := by
    simpa [prefixWord, tailWord_4757227, baseEnd_4757227] using wordTrace_append hprefix tailTrace_4757227
  have hstable : (prefixWord ++ tailWord_4757227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757227).length < 2 ^ (prefixWord ++ tailWord_4757227).sum := by decide
  have hdescent : baseEnd_4757227 < baseStart_4757227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757236 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4757236 : Nat := 118140960795 + 4757236 * 2 ^ 59
def prefixEnd_4757236 : Nat := 4983230072969 + 3 ^ 40 * 4757236 * 2
def baseEnd_4757236 : Nat := 2442748654872454525971877

theorem tailTrace_4757236 : CollatzResearch.WordTrace tailWord_4757236 prefixEnd_4757236 2442748654872454525971877 := by
  unfold tailWord_4757236
  simp only [CollatzResearch.WordTrace]
  refine ⟨86755325696676959034885781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115673767595569278713181041 86755325696676959034885781)
  ·
    refine ⟨4066655892031732454760271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86755325696676959034885781 4066655892031732454760271)
    ·
      refine ⟨6099983838047598682140407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066655892031732454760271 6099983838047598682140407)
      ·
        refine ⟨9149975757071398023210611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6099983838047598682140407 9149975757071398023210611)
        ·
          refine ⟨13724963635607097034815917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149975757071398023210611 13724963635607097034815917)
          ·
            refine ⟨5146861363352661388055969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13724963635607097034815917 5146861363352661388055969)
            ·
              refine ⟨3860146022514496041041977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146861363352661388055969 3860146022514496041041977)
              ·
                refine ⟨2895109516885872030781483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3860146022514496041041977 2895109516885872030781483)
                ·
                  refine ⟨4342664275328808046172225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895109516885872030781483 4342664275328808046172225)
                  ·
                    refine ⟨3256998206496606034629169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342664275328808046172225 3256998206496606034629169)
                    ·
                      refine ⟨2442748654872454525971877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3256998206496606034629169 2442748654872454525971877)
                      ·
                        rfl

theorem cell23_4757236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4757236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757236 prefixEnd_4757236 := by exact prefixLift 4757236
  have htrace : WordTrace (prefixWord ++ tailWord_4757236) baseStart_4757236 baseEnd_4757236 := by
    simpa [prefixWord, tailWord_4757236, baseEnd_4757236] using wordTrace_append hprefix tailTrace_4757236
  have hstable : (prefixWord ++ tailWord_4757236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757236).length < 2 ^ (prefixWord ++ tailWord_4757236).sum := by decide
  have hdescent : baseEnd_4757236 < baseStart_4757236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757258 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_4757258 : Nat := 118140960795 + 4757258 * 2 ^ 59
def prefixEnd_4757258 : Nat := 4983230072969 + 3 ^ 40 * 4757258 * 2
def baseEnd_4757258 : Nat := 2442759951446853439896775

theorem tailTrace_4757258 : CollatzResearch.WordTrace tailWord_4757258 prefixEnd_4757258 2442759951446853439896775 := by
  unfold tailWord_4757258
  simp only [CollatzResearch.WordTrace]
  refine ⟨43377863449818553956768107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115674302532849477218048285 43377863449818553956768107)
  ·
    refine ⟨65066795174727830935152161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43377863449818553956768107 65066795174727830935152161)
    ·
      refine ⟨48800096381045873201364121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65066795174727830935152161 48800096381045873201364121)
      ·
        refine ⟨36600072285784404901023091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48800096381045873201364121 36600072285784404901023091)
        ·
          refine ⟨54900108428676607351534637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36600072285784404901023091 54900108428676607351534637)
          ·
            refine ⟨20587540660753727756825489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54900108428676607351534637 20587540660753727756825489)
            ·
              refine ⟨15440655495565295817619117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20587540660753727756825489 15440655495565295817619117)
              ·
                refine ⟨5790245810836985931607169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15440655495565295817619117 5790245810836985931607169)
                ·
                  refine ⟨4342684358127739448705377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5790245810836985931607169 4342684358127739448705377)
                  ·
                    refine ⟨3257013268595804586529033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342684358127739448705377 3257013268595804586529033)
                    ·
                      refine ⟨2442759951446853439896775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257013268595804586529033 2442759951446853439896775)
                      ·
                        rfl

theorem cell23_4757258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_4757258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757258 prefixEnd_4757258 := by exact prefixLift 4757258
  have htrace : WordTrace (prefixWord ++ tailWord_4757258) baseStart_4757258 baseEnd_4757258 := by
    simpa [prefixWord, tailWord_4757258, baseEnd_4757258] using wordTrace_append hprefix tailTrace_4757258
  have hstable : (prefixWord ++ tailWord_4757258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757258).length < 2 ^ (prefixWord ++ tailWord_4757258).sum := by decide
  have hdescent : baseEnd_4757258 < baseStart_4757258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757281 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 5]
def baseStart_4757281 : Nat := 118140960795 + 4757281 * 2 ^ 59
def prefixEnd_4757281 : Nat := 4983230072969 + 3 ^ 40 * 4757281 * 2
def baseEnd_4757281 : Nat := 271419084611322983323241

theorem tailTrace_4757281 : CollatzResearch.WordTrace tailWord_4757281 prefixEnd_4757281 271419084611322983323241 := by
  unfold tailWord_4757281
  simp only [CollatzResearch.WordTrace]
  refine ⟨173512292678190890755159697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115674861785460593836773131 173512292678190890755159697)
  ·
    refine ⟨130134219508643168066369773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173512292678190890755159697 130134219508643168066369773)
    ·
      refine ⟨48800332315741188024888665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130134219508643168066369773 48800332315741188024888665)
      ·
        refine ⟨36600249236805891018666499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48800332315741188024888665 36600249236805891018666499)
        ·
          refine ⟨54900373855208836527999749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36600249236805891018666499 54900373855208836527999749)
          ·
            refine ⟨10293820097851656848999953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54900373855208836527999749 10293820097851656848999953)
            ·
              refine ⟨7720365073388742636749965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10293820097851656848999953 7720365073388742636749965)
              ·
                refine ⟨2895136902520778488781237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7720365073388742636749965 2895136902520778488781237)
                ·
                  refine ⟨271419084611322983323241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2895136902520778488781237 271419084611322983323241)
                  ·
                    rfl

theorem cell23_4757281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 5].length) (baseStart_4757281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757281 prefixEnd_4757281 := by exact prefixLift 4757281
  have htrace : WordTrace (prefixWord ++ tailWord_4757281) baseStart_4757281 baseEnd_4757281 := by
    simpa [prefixWord, tailWord_4757281, baseEnd_4757281] using wordTrace_append hprefix tailTrace_4757281
  have hstable : (prefixWord ++ tailWord_4757281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757281).length < 2 ^ (prefixWord ++ tailWord_4757281).sum := by decide
  have hdescent : baseEnd_4757281 < baseStart_4757281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757337 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 10]
def baseStart_4757337 : Nat := 118140960795 + 4757337 * 2 ^ 59
def prefixEnd_4757337 : Nat := 4983230072969 + 3 ^ 40 * 4757337 * 2
def baseEnd_4757337 : Nat := 271422279602062070089879

theorem tailTrace_4757337 : CollatzResearch.WordTrace tailWord_4757337 prefixEnd_4757337 271422279602062070089879 := by
  unfold tailWord_4757337
  simp only [CollatzResearch.WordTrace]
  refine ⟨173514335165988012319198265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115676223443992008212798843 173514335165988012319198265)
  ·
    refine ⟨130135751374491009239398699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173514335165988012319198265 130135751374491009239398699)
    ·
      refine ⟨195203627061736513859098049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130135751374491009239398699 195203627061736513859098049)
      ·
        refine ⟨146402720296302385394323537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195203627061736513859098049 146402720296302385394323537)
        ·
          refine ⟨109802040222226789045742653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146402720296302385394323537 109802040222226789045742653)
          ·
            refine ⟨41175765083335045892153495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109802040222226789045742653 41175765083335045892153495)
            ·
              refine ⟨61763647625002568838230243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41175765083335045892153495 61763647625002568838230243)
              ·
                refine ⟨92645471437503853257345365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61763647625002568838230243 92645471437503853257345365)
                ·
                  refine ⟨271422279602062070089879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92645471437503853257345365 271422279602062070089879)
                  ·
                    rfl

theorem cell23_4757337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_4757337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757337 prefixEnd_4757337 := by exact prefixLift 4757337
  have htrace : WordTrace (prefixWord ++ tailWord_4757337) baseStart_4757337 baseEnd_4757337 := by
    simpa [prefixWord, tailWord_4757337, baseEnd_4757337] using wordTrace_append hprefix tailTrace_4757337
  have hstable : (prefixWord ++ tailWord_4757337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757337).length < 2 ^ (prefixWord ++ tailWord_4757337).sum := by decide
  have hdescent : baseEnd_4757337 < baseStart_4757337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757351 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_4757351 : Nat := 118140960795 + 4757351 * 2 ^ 59
def prefixEnd_4757351 : Nat := 4983230072969 + 3 ^ 40 * 4757351 * 2
def baseEnd_4757351 : Nat := 2442807705147721576033847

theorem tailTrace_4757351 : CollatzResearch.WordTrace tailWord_4757351 prefixEnd_4757351 2442807705147721576033847 := by
  unfold tailWord_4757351
  simp only [CollatzResearch.WordTrace]
  refine ⟨173514845787937292710207907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115676563858624861806805271 173514845787937292710207907)
  ·
    refine ⟨260272268681905939065311861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173514845787937292710207907 260272268681905939065311861)
    ·
      refine ⟨24400525188928681787372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260272268681905939065311861 24400525188928681787372987)
      ·
        refine ⟨36600787783393022681059481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24400525188928681787372987 36600787783393022681059481)
        ·
          refine ⟨27450590837544767010794611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36600787783393022681059481 27450590837544767010794611)
          ·
            refine ⟨41175886256317150516191917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27450590837544767010794611 41175886256317150516191917)
            ·
              refine ⟨15440957346118931443571969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41175886256317150516191917 15440957346118931443571969)
              ·
                refine ⟨11580718009589198582678977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15440957346118931443571969 11580718009589198582678977)
                ·
                  refine ⟨8685538507191898937009233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11580718009589198582678977 8685538507191898937009233)
                  ·
                    refine ⟨6514153880393924202756925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8685538507191898937009233 6514153880393924202756925)
                    ·
                      refine ⟨2442807705147721576033847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514153880393924202756925 2442807705147721576033847)
                      ·
                        rfl

theorem cell23_4757351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_4757351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757351 prefixEnd_4757351 := by exact prefixLift 4757351
  have htrace : WordTrace (prefixWord ++ tailWord_4757351) baseStart_4757351 baseEnd_4757351 := by
    simpa [prefixWord, tailWord_4757351, baseEnd_4757351] using wordTrace_append hprefix tailTrace_4757351
  have hstable : (prefixWord ++ tailWord_4757351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757351).length < 2 ^ (prefixWord ++ tailWord_4757351).sum := by decide
  have hdescent : baseEnd_4757351 < baseStart_4757351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757358 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4757358 : Nat := 118140960795 + 4757358 * 2 ^ 59
def prefixEnd_4757358 : Nat := 4983230072969 + 3 ^ 40 * 4757358 * 2
def baseEnd_4757358 : Nat := 814270433170767682882105

theorem tailTrace_4757358 : CollatzResearch.WordTrace tailWord_4757358 prefixEnd_4757358 814270433170767682882105 := by
  unfold tailWord_4757358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21689387637363991613214091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115676734065941288603808485 21689387637363991613214091)
  ·
    refine ⟨32534081456045987419821137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21689387637363991613214091 32534081456045987419821137)
    ·
      refine ⟨24400561092034490564865853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32534081456045987419821137 24400561092034490564865853)
      ·
        refine ⟨9150210409512933961824695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24400561092034490564865853 9150210409512933961824695)
        ·
          refine ⟨13725315614269400942737043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9150210409512933961824695 13725315614269400942737043)
          ·
            refine ⟨20587973421404101414105565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13725315614269400942737043 20587973421404101414105565)
            ·
              refine ⟨7720490033026538030289587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20587973421404101414105565 7720490033026538030289587)
              ·
                refine ⟨11580735049539807045434381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720490033026538030289587 11580735049539807045434381)
                ·
                  refine ⟨4342775643577427642037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11580735049539807045434381 4342775643577427642037893)
                  ·
                    refine ⟨814270433170767682882105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342775643577427642037893 814270433170767682882105)
                    ·
                      rfl

theorem cell23_4757358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4757358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757358 prefixEnd_4757358 := by exact prefixLift 4757358
  have htrace : WordTrace (prefixWord ++ tailWord_4757358) baseStart_4757358 baseEnd_4757358 := by
    simpa [prefixWord, tailWord_4757358, baseEnd_4757358] using wordTrace_append hprefix tailTrace_4757358
  have hstable : (prefixWord ++ tailWord_4757358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757358).length < 2 ^ (prefixWord ++ tailWord_4757358).sum := by decide
  have hdescent : baseEnd_4757358 < baseStart_4757358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757367 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 11]
def baseStart_4757367 : Nat := 118140960795 + 4757367 * 2 ^ 59
def prefixEnd_4757367 : Nat := 4983230072969 + 3 ^ 40 * 4757367 * 2
def baseEnd_4757367 : Nat := 814271973612731171144591

theorem tailTrace_4757367 : CollatzResearch.WordTrace tailWord_4757367 prefixEnd_4757367 814271973612731171144591 := by
  unfold tailWord_4757367
  simp only [CollatzResearch.WordTrace]
  refine ⟨173515429355879327442790355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115676952903919551628526903 173515429355879327442790355)
  ·
    refine ⟨260273144033818991164185533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173515429355879327442790355 260273144033818991164185533)
    ·
      refine ⟨97602429012682121686569575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260273144033818991164185533 97602429012682121686569575)
      ·
        refine ⟨146403643519023182529854363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97602429012682121686569575 146403643519023182529854363)
        ·
          refine ⟨219605465278534773794781545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146403643519023182529854363 219605465278534773794781545)
          ·
            refine ⟨164704098958901080346086159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219605465278534773794781545 164704098958901080346086159)
            ·
              refine ⟨247056148438351620519129239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164704098958901080346086159 247056148438351620519129239)
              ·
                refine ⟨370584222657527430778693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247056148438351620519129239 370584222657527430778693859)
                ·
                  refine ⟨555876333986291146168040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370584222657527430778693859 555876333986291146168040789)
                  ·
                    refine ⟨814271973612731171144591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 555876333986291146168040789 814271973612731171144591)
                    ·
                      rfl

theorem cell23_4757367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_4757367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757367 prefixEnd_4757367 := by exact prefixLift 4757367
  have htrace : WordTrace (prefixWord ++ tailWord_4757367) baseStart_4757367 baseEnd_4757367 := by
    simpa [prefixWord, tailWord_4757367, baseEnd_4757367] using wordTrace_append hprefix tailTrace_4757367
  have hstable : (prefixWord ++ tailWord_4757367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757367).length < 2 ^ (prefixWord ++ tailWord_4757367).sum := by decide
  have hdescent : baseEnd_4757367 < baseStart_4757367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757381 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_4757381 : Nat := 118140960795 + 4757381 * 2 ^ 59
def prefixEnd_4757381 : Nat := 4983230072969 + 3 ^ 40 * 4757381 * 2
def baseEnd_4757381 : Nat := 2442823109567356458658709

theorem tailTrace_4757381 : CollatzResearch.WordTrace tailWord_4757381 prefixEnd_4757381 2442823109567356458658709 := by
  unfold tailWord_4757381
  simp only [CollatzResearch.WordTrace]
  refine ⟨173515939977828607833799997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115677293318552405222533331 173515939977828607833799997)
  ·
    refine ⟨65068477491685727937674999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173515939977828607833799997 65068477491685727937674999)
    ·
      refine ⟨97602716237528591906512499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65068477491685727937674999 97602716237528591906512499)
      ·
        refine ⟨146404074356292887859768749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97602716237528591906512499 146404074356292887859768749)
        ·
          refine ⟨54901527883609832947413281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146404074356292887859768749 54901527883609832947413281)
          ·
            refine ⟨41176145912707374710559961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54901527883609832947413281 41176145912707374710559961)
            ·
              refine ⟨30882109434530531032919971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41176145912707374710559961 30882109434530531032919971)
              ·
                refine ⟨46323164151795796549379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30882109434530531032919971 46323164151795796549379957)
                ·
                  refine ⟨4342796639230855926504371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46323164151795796549379957 4342796639230855926504371)
                  ·
                    refine ⟨6514194958846283889756557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342796639230855926504371 6514194958846283889756557)
                    ·
                      refine ⟨2442823109567356458658709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514194958846283889756557 2442823109567356458658709)
                      ·
                        rfl

theorem cell23_4757381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_4757381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757381 prefixEnd_4757381 := by exact prefixLift 4757381
  have htrace : WordTrace (prefixWord ++ tailWord_4757381) baseStart_4757381 baseEnd_4757381 := by
    simpa [prefixWord, tailWord_4757381, baseEnd_4757381] using wordTrace_append hprefix tailTrace_4757381
  have hstable : (prefixWord ++ tailWord_4757381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757381).length < 2 ^ (prefixWord ++ tailWord_4757381).sum := by decide
  have hdescent : baseEnd_4757381 < baseStart_4757381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757409 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 1, 4]
def baseStart_4757409 : Nat := 118140960795 + 4757409 * 2 ^ 59
def prefixEnd_4757409 : Nat := 4983230072969 + 3 ^ 40 * 4757409 * 2
def baseEnd_4757409 : Nat := 814279162341894116369527

theorem tailTrace_4757409 : CollatzResearch.WordTrace tailWord_4757409 prefixEnd_4757409 814279162341894116369527 := by
  unfold tailWord_4757409
  simp only [CollatzResearch.WordTrace]
  refine ⟨173516961221727168615819281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115677974147818112410546187 173516961221727168615819281)
  ·
    refine ⟨130137720916295376461864461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173516961221727168615819281 130137720916295376461864461)
    ·
      refine ⟨48801645343610766173199173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130137720916295376461864461 48801645343610766173199173)
      ·
        refine ⟨9150308501927018657474845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48801645343610766173199173 9150308501927018657474845)
        ·
          refine ⟨3431365688222631996553067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9150308501927018657474845 3431365688222631996553067)
          ·
            refine ⟨5147048532333947994829601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431365688222631996553067 5147048532333947994829601)
            ·
              refine ⟨3860286399250460996122201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5147048532333947994829601 3860286399250460996122201)
              ·
                refine ⟨2895214799437845747091651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3860286399250460996122201 2895214799437845747091651)
                ·
                  refine ⟨4342822199156768620637477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895214799437845747091651 4342822199156768620637477)
                  ·
                    refine ⟨814279162341894116369527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342822199156768620637477 814279162341894116369527)
                    ·
                      rfl

theorem cell23_4757409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_4757409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757409 prefixEnd_4757409 := by exact prefixLift 4757409
  have htrace : WordTrace (prefixWord ++ tailWord_4757409) baseStart_4757409 baseEnd_4757409 := by
    simpa [prefixWord, tailWord_4757409, baseEnd_4757409] using wordTrace_append hprefix tailTrace_4757409
  have hstable : (prefixWord ++ tailWord_4757409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757409).length < 2 ^ (prefixWord ++ tailWord_4757409).sum := by decide
  have hdescent : baseEnd_4757409 < baseStart_4757409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757465 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_4757465 : Nat := 118140960795 + 4757465 * 2 ^ 59
def prefixEnd_4757465 : Nat := 4983230072969 + 3 ^ 40 * 4757465 * 2
def baseEnd_4757465 : Nat := 814288747314111376669441

theorem tailTrace_4757465 : CollatzResearch.WordTrace tailWord_4757465 prefixEnd_4757465 814288747314111376669441 := by
  unfold tailWord_4757465
  simp only [CollatzResearch.WordTrace]
  refine ⟨173519003709524290179857849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115679335806349526786571899 173519003709524290179857849)
  ·
    refine ⟨130139252782143217634893387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173519003709524290179857849 130139252782143217634893387)
    ·
      refine ⟨195208879173214826452340081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130139252782143217634893387 195208879173214826452340081)
      ·
        refine ⟨146406659379911119839255061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195208879173214826452340081 146406659379911119839255061)
        ·
          refine ⟨6862812158433333742465081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146406659379911119839255061 6862812158433333742465081)
          ·
            refine ⟨5147109118825000306848811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6862812158433333742465081 5147109118825000306848811)
            ·
              refine ⟨7720663678237500460273217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147109118825000306848811 7720663678237500460273217)
              ·
                refine ⟨5790497758678125345204913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7720663678237500460273217 5790497758678125345204913)
                ·
                  refine ⟨4342873319008594008903685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5790497758678125345204913 4342873319008594008903685)
                  ·
                    refine ⟨814288747314111376669441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342873319008594008903685 814288747314111376669441)
                    ·
                      rfl

theorem cell23_4757465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_4757465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757465 prefixEnd_4757465 := by exact prefixLift 4757465
  have htrace : WordTrace (prefixWord ++ tailWord_4757465) baseStart_4757465 baseEnd_4757465 := by
    simpa [prefixWord, tailWord_4757465, baseEnd_4757465] using wordTrace_append hprefix tailTrace_4757465
  have hstable : (prefixWord ++ tailWord_4757465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757465).length < 2 ^ (prefixWord ++ tailWord_4757465).sum := by decide
  have hdescent : baseEnd_4757465 < baseStart_4757465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757484 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_4757484 : Nat := 118140960795 + 4757484 * 2 ^ 59
def prefixEnd_4757484 : Nat := 4983230072969 + 3 ^ 40 * 4757484 * 2
def baseEnd_4757484 : Nat := 2442875998074769555670735

theorem tailTrace_4757484 : CollatzResearch.WordTrace tailWord_4757484 prefixEnd_4757484 2442875998074769555670735 := by
  unfold tailWord_4757484
  simp only [CollatzResearch.WordTrace]
  refine ⟨86759848348227728212399753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115679797797636970949866337 86759848348227728212399753)
  ·
    refine ⟨65069886261170796159299815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86759848348227728212399753 65069886261170796159299815)
    ·
      refine ⟨97604829391756194238949723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65069886261170796159299815 97604829391756194238949723)
      ·
        refine ⟨146407244087634291358424585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97604829391756194238949723 146407244087634291358424585)
        ·
          refine ⟨109805433065725718518818439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146407244087634291358424585 109805433065725718518818439)
          ·
            refine ⟨164708149598588577778227659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109805433065725718518818439 164708149598588577778227659)
            ·
              refine ⟨247062224397882866667341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164708149598588577778227659 247062224397882866667341489)
              ·
                refine ⟨185296668298412150000506117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247062224397882866667341489 185296668298412150000506117)
                ·
                  refine ⟨34743125305952278125094897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185296668298412150000506117 34743125305952278125094897)
                  ·
                    refine ⟨26057343979464208593821173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34743125305952278125094897 26057343979464208593821173)
                    ·
                      refine ⟨2442875998074769555670735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26057343979464208593821173 2442875998074769555670735)
                      ·
                        rfl

theorem cell23_4757484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_4757484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757484 prefixEnd_4757484 := by exact prefixLift 4757484
  have htrace : WordTrace (prefixWord ++ tailWord_4757484) baseStart_4757484 baseEnd_4757484 := by
    simpa [prefixWord, tailWord_4757484, baseEnd_4757484] using wordTrace_append hprefix tailTrace_4757484
  have hstable : (prefixWord ++ tailWord_4757484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757484).length < 2 ^ (prefixWord ++ tailWord_4757484).sum := by decide
  have hdescent : baseEnd_4757484 < baseStart_4757484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757488 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_4757488 : Nat := 118140960795 + 4757488 * 2 ^ 59
def prefixEnd_4757488 : Nat := 4983230072969 + 3 ^ 40 * 4757488 * 2
def baseEnd_4757488 : Nat := 2442878051997387540020717

theorem tailTrace_4757488 : CollatzResearch.WordTrace tailWord_4757488 prefixEnd_4757488 2442878051997387540020717 := by
  unfold tailWord_4757488
  simp only [CollatzResearch.WordTrace]
  refine ⟨86759921294220482553972559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115679895058960643405296745 86759921294220482553972559)
  ·
    refine ⟨130139881941330723830958839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86759921294220482553972559 130139881941330723830958839)
    ·
      refine ⟨195209822911996085746438259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130139881941330723830958839 195209822911996085746438259)
      ·
        refine ⟨292814734367994128619657389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195209822911996085746438259 292814734367994128619657389)
        ·
          refine ⟨109805525387997798232371521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292814734367994128619657389 109805525387997798232371521)
          ·
            refine ⟨82354144040998348674278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109805525387997798232371521 82354144040998348674278641)
            ·
              refine ⟨61765608030748761505708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82354144040998348674278641 61765608030748761505708981)
              ·
                refine ⟨5790525752882696391160217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61765608030748761505708981 5790525752882696391160217)
                ·
                  refine ⟨4342894314662022293370163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5790525752882696391160217 4342894314662022293370163)
                  ·
                    refine ⟨6514341471993033440055245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342894314662022293370163 6514341471993033440055245)
                    ·
                      refine ⟨2442878051997387540020717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514341471993033440055245 2442878051997387540020717)
                      ·
                        rfl

theorem cell23_4757488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_4757488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757488 prefixEnd_4757488 := by exact prefixLift 4757488
  have htrace : WordTrace (prefixWord ++ tailWord_4757488) baseStart_4757488 baseEnd_4757488 := by
    simpa [prefixWord, tailWord_4757488, baseEnd_4757488] using wordTrace_append hprefix tailTrace_4757488
  have hstable : (prefixWord ++ tailWord_4757488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757488).length < 2 ^ (prefixWord ++ tailWord_4757488).sum := by decide
  have hdescent : baseEnd_4757488 < baseStart_4757488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_4757504 : Nat := 118140960795 + 4757504 * 2 ^ 59
def prefixEnd_4757504 : Nat := 4983230072969 + 3 ^ 40 * 4757504 * 2
def baseEnd_4757504 : Nat := 814295422562619825806881

theorem tailTrace_4757504 : CollatzResearch.WordTrace tailWord_4757504 prefixEnd_4757504 814295422562619825806881 := by
  unfold tailWord_4757504
  simp only [CollatzResearch.WordTrace]
  refine ⟨86760213078191499920263783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115680284104255333227018377 86760213078191499920263783)
  ·
    refine ⟨130140319617287249880395675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86760213078191499920263783 130140319617287249880395675)
    ·
      refine ⟨195210479425930874820593513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130140319617287249880395675 195210479425930874820593513)
      ·
        refine ⟨146407859569448156115445135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195210479425930874820593513 146407859569448156115445135)
        ·
          refine ⟨219611789354172234173167703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146407859569448156115445135 219611789354172234173167703)
          ·
            refine ⟨329417684031258351259751555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219611789354172234173167703 329417684031258351259751555)
            ·
              refine ⟨494126526046887526889627333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329417684031258351259751555 494126526046887526889627333)
              ·
                refine ⟨92648723633791411291805125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494126526046887526889627333 92648723633791411291805125)
                ·
                  refine ⟨17371635681335889617213461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92648723633791411291805125 17371635681335889617213461)
                  ·
                    refine ⟨814295422562619825806881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17371635681335889617213461 814295422562619825806881)
                    ·
                      rfl

theorem cell23_4757504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_4757504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757504 prefixEnd_4757504 := by exact prefixLift 4757504
  have htrace : WordTrace (prefixWord ++ tailWord_4757504) baseStart_4757504 baseEnd_4757504 := by
    simpa [prefixWord, tailWord_4757504, baseEnd_4757504] using wordTrace_append hprefix tailTrace_4757504
  have hstable : (prefixWord ++ tailWord_4757504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757504).length < 2 ^ (prefixWord ++ tailWord_4757504).sum := by decide
  have hdescent : baseEnd_4757504 < baseStart_4757504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757591 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4757591 : Nat := 118140960795 + 4757591 * 2 ^ 59
def prefixEnd_4757591 : Nat := 4983230072969 + 3 ^ 40 * 4757591 * 2
def baseEnd_4757591 : Nat := 2442930940504800637032743

theorem tailTrace_4757591 : CollatzResearch.WordTrace tailWord_4757591 prefixEnd_4757591 2442930940504800637032743 := by
  unfold tailWord_4757591
  simp only [CollatzResearch.WordTrace]
  refine ⟨173523599307067813698944627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115682399538045209132629751 173523599307067813698944627)
  ·
    refine ⟨260285398960601720548416941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173523599307067813698944627 260285398960601720548416941)
    ·
      refine ⟨97607024610225645205656353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260285398960601720548416941 97607024610225645205656353)
      ·
        refine ⟨73205268457669233904242265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97607024610225645205656353 73205268457669233904242265)
        ·
          refine ⟨54903951343251925428181699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73205268457669233904242265 54903951343251925428181699)
          ·
            refine ⟨82355927014877888142272549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54903951343251925428181699 82355927014877888142272549)
            ·
              refine ⟨15441736315289604026676103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82355927014877888142272549 15441736315289604026676103)
              ·
                refine ⟨23162604472934406040014155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441736315289604026676103 23162604472934406040014155)
                ·
                  refine ⟨34743906709401609060021233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23162604472934406040014155 34743906709401609060021233)
                  ·
                    refine ⟨26057930032051206795015925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34743906709401609060021233 26057930032051206795015925)
                    ·
                      refine ⟨2442930940504800637032743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26057930032051206795015925 2442930940504800637032743)
                      ·
                        rfl

theorem cell23_4757591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4757591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757591 prefixEnd_4757591 := by exact prefixLift 4757591
  have htrace : WordTrace (prefixWord ++ tailWord_4757591) baseStart_4757591 baseEnd_4757591 := by
    simpa [prefixWord, tailWord_4757591, baseEnd_4757591] using wordTrace_append hprefix tailTrace_4757591
  have hstable : (prefixWord ++ tailWord_4757591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757591).length < 2 ^ (prefixWord ++ tailWord_4757591).sum := by decide
  have hdescent : baseEnd_4757591 < baseStart_4757591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757601 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_4757601 : Nat := 118140960795 + 4757601 * 2 ^ 59
def prefixEnd_4757601 : Nat := 4983230072969 + 3 ^ 40 * 4757601 * 2
def baseEnd_4757601 : Nat := 2442936075311345597907697

theorem tailTrace_4757601 : CollatzResearch.WordTrace tailWord_4757601 prefixEnd_4757601 2442936075311345597907697 := by
  unfold tailWord_4757601
  simp only [CollatzResearch.WordTrace]
  refine ⟨173523964037031585406808657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115682642691354390271205771 173523964037031585406808657)
  ·
    refine ⟨130142973027773689055106493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173523964037031585406808657 130142973027773689055106493)
    ·
      refine ⟨48803614885415133395664935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130142973027773689055106493 48803614885415133395664935)
      ·
        refine ⟨73205422328122700093497403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48803614885415133395664935 73205422328122700093497403)
        ·
          refine ⟨109808133492184050140246105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73205422328122700093497403 109808133492184050140246105)
          ·
            refine ⟨82356100119138037605184579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109808133492184050140246105 82356100119138037605184579)
            ·
              refine ⟨123534150178707056407776869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82356100119138037605184579 123534150178707056407776869)
              ·
                refine ⟨23162653158507573076458163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123534150178707056407776869 23162653158507573076458163)
                ·
                  refine ⟨34743979737761359614687245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23162653158507573076458163 34743979737761359614687245)
                  ·
                    refine ⟨13028992401660509855507717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34743979737761359614687245 13028992401660509855507717)
                    ·
                      refine ⟨2442936075311345597907697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13028992401660509855507717 2442936075311345597907697)
                      ·
                        rfl

theorem cell23_4757601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_4757601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757601 prefixEnd_4757601 := by exact prefixLift 4757601
  have htrace : WordTrace (prefixWord ++ tailWord_4757601) baseStart_4757601 baseEnd_4757601 := by
    simpa [prefixWord, tailWord_4757601, baseEnd_4757601] using wordTrace_append hprefix tailTrace_4757601
  have hstable : (prefixWord ++ tailWord_4757601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757601).length < 2 ^ (prefixWord ++ tailWord_4757601).sum := by decide
  have hdescent : baseEnd_4757601 < baseStart_4757601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757618 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4757618 : Nat := 118140960795 + 4757618 * 2 ^ 59
def prefixEnd_4757618 : Nat := 4983230072969 + 3 ^ 40 * 4757618 * 2
def baseEnd_4757618 : Nat := 2442944804482472031395119

theorem tailTrace_4757618 : CollatzResearch.WordTrace tailWord_4757618 prefixEnd_4757618 2442944804482472031395119 := by
  unfold tailWord_4757618
  simp only [CollatzResearch.WordTrace]
  refine ⟨43381146019492499327544377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115683056051979998206785005 43381146019492499327544377)
  ·
    refine ⟨32535859514619374495658283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43381146019492499327544377 32535859514619374495658283)
    ·
      refine ⟨48803789271929061743487425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32535859514619374495658283 48803789271929061743487425)
      ·
        refine ⟨36602841953946796307615569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48803789271929061743487425 36602841953946796307615569)
        ·
          refine ⟨27452131465460097230711677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36602841953946796307615569 27452131465460097230711677)
          ·
            refine ⟨10294549299547536461516879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27452131465460097230711677 10294549299547536461516879)
            ·
              refine ⟨15441823949321304692275319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294549299547536461516879 15441823949321304692275319)
              ·
                refine ⟨23162735923981957038412979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441823949321304692275319 23162735923981957038412979)
                ·
                  refine ⟨34744103885972935557619469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23162735923981957038412979 34744103885972935557619469)
                  ·
                    refine ⟨13029038957239850834107301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34744103885972935557619469 13029038957239850834107301)
                    ·
                      refine ⟨2442944804482472031395119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13029038957239850834107301 2442944804482472031395119)
                      ·
                        rfl

theorem cell23_4757618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4757618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757618 prefixEnd_4757618 := by exact prefixLift 4757618
  have htrace : WordTrace (prefixWord ++ tailWord_4757618) baseStart_4757618 baseEnd_4757618 := by
    simpa [prefixWord, tailWord_4757618, baseEnd_4757618] using wordTrace_append hprefix tailTrace_4757618
  have hstable : (prefixWord ++ tailWord_4757618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757618).length < 2 ^ (prefixWord ++ tailWord_4757618).sum := by decide
  have hdescent : baseEnd_4757618 < baseStart_4757618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757641 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 8]
def baseStart_4757641 : Nat := 118140960795 + 4757641 * 2 ^ 59
def prefixEnd_4757641 : Nat := 4983230072969 + 3 ^ 40 * 4757641 * 2
def baseEnd_4757641 : Nat := 271439623837502826823057

theorem tailTrace_4757641 : CollatzResearch.WordTrace tailWord_4757641 prefixEnd_4757641 271439623837502826823057 := by
  unfold tailWord_4757641
  simp only [CollatzResearch.WordTrace]
  refine ⟨173525422956886672238264777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115683615304591114825509851 173525422956886672238264777)
  ·
    refine ⟨130144067217665004178698583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173525422956886672238264777 130144067217665004178698583)
    ·
      refine ⟨195216100826497506268047875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130144067217665004178698583 195216100826497506268047875)
      ·
        refine ⟨292824151239746259402071813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195216100826497506268047875 292824151239746259402071813)
        ·
          refine ⟨54904528357452423637888465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292824151239746259402071813 54904528357452423637888465)
          ·
            refine ⟨41178396268089317728416349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54904528357452423637888465 41178396268089317728416349)
            ·
              refine ⟨15441898600533494148156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41178396268089317728416349 15441898600533494148156131)
              ·
                refine ⟨23162847900800241222234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441898600533494148156131 23162847900800241222234197)
                ·
                  refine ⟨271439623837502826823057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23162847900800241222234197 271439623837502826823057)
                  ·
                    rfl

theorem cell23_4757641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_4757641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757641 prefixEnd_4757641 := by exact prefixLift 4757641
  have htrace : WordTrace (prefixWord ++ tailWord_4757641) baseStart_4757641 baseEnd_4757641 := by
    simpa [prefixWord, tailWord_4757641, baseEnd_4757641] using wordTrace_append hprefix tailTrace_4757641
  have hstable : (prefixWord ++ tailWord_4757641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757641).length < 2 ^ (prefixWord ++ tailWord_4757641).sum := by decide
  have hdescent : baseEnd_4757641 < baseStart_4757641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757688 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_4757688 : Nat := 118140960795 + 4757688 * 2 ^ 59
def prefixEnd_4757688 : Nat := 4983230072969 + 3 ^ 40 * 4757688 * 2
def baseEnd_4757688 : Nat := 814326916042762252506599

theorem tailTrace_4757688 : CollatzResearch.WordTrace tailWord_4757688 prefixEnd_4757688 814326916042762252506599 := by
  unfold tailWord_4757688
  simp only [CollatzResearch.WordTrace]
  refine ⟨86763568593858199632612859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115684758125144266176817145 86763568593858199632612859)
  ·
    refine ⟨130145352890787299448919289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86763568593858199632612859 130145352890787299448919289)
    ·
      refine ⟨97609014668090474586689467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130145352890787299448919289 97609014668090474586689467)
      ·
        refine ⟨146413522002135711880034201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97609014668090474586689467 146413522002135711880034201)
        ·
          refine ⟨109810141501601783910025651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146413522002135711880034201 109810141501601783910025651)
          ·
            refine ⟨164715212252402675865038477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109810141501601783910025651 164715212252402675865038477)
            ·
              refine ⟨61768204594651003449389429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164715212252402675865038477 61768204594651003449389429)
              ·
                refine ⟨5790769180748531573380259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61768204594651003449389429 5790769180748531573380259)
                ·
                  refine ⟨8686153771122797360070389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790769180748531573380259 8686153771122797360070389)
                  ·
                    refine ⟨814326916042762252506599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8686153771122797360070389 814326916042762252506599)
                    ·
                      rfl

theorem cell23_4757688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_4757688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757688 prefixEnd_4757688 := by exact prefixLift 4757688
  have htrace : WordTrace (prefixWord ++ tailWord_4757688) baseStart_4757688 baseEnd_4757688 := by
    simpa [prefixWord, tailWord_4757688, baseEnd_4757688] using wordTrace_append hprefix tailTrace_4757688
  have hstable : (prefixWord ++ tailWord_4757688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757688).length < 2 ^ (prefixWord ++ tailWord_4757688).sum := by decide
  have hdescent : baseEnd_4757688 < baseStart_4757688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757735 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4757735 : Nat := 118140960795 + 4757735 * 2 ^ 59
def prefixEnd_4757735 : Nat := 4983230072969 + 3 ^ 40 * 4757735 * 2
def baseEnd_4757735 : Nat := 814334960573016024544027

theorem tailTrace_4757735 : CollatzResearch.WordTrace tailWord_4757735 prefixEnd_4757735 814334960573016024544027 := by
  unfold tailWord_4757735
  simp only [CollatzResearch.WordTrace]
  refine ⟨173528851418546126292186659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115685900945697417528124439 173528851418546126292186659)
  ·
    refine ⟨260293277127819189438279989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173528851418546126292186659 260293277127819189438279989)
    ·
      refine ⟨24402494730733049009838749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260293277127819189438279989 24402494730733049009838749)
      ·
        refine ⟨9150935524024893378689531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24402494730733049009838749 9150935524024893378689531)
        ·
          refine ⟨13726403286037340068034297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9150935524024893378689531 13726403286037340068034297)
          ·
            refine ⟨10294802464528005051025723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13726403286037340068034297 10294802464528005051025723)
            ·
              refine ⟨15442203696792007576538585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294802464528005051025723 15442203696792007576538585)
              ·
                refine ⟨11581652772594005682403939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15442203696792007576538585 11581652772594005682403939)
                ·
                  refine ⟨17372479158891008523605909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11581652772594005682403939 17372479158891008523605909)
                  ·
                    refine ⟨814334960573016024544027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17372479158891008523605909 814334960573016024544027)
                    ·
                      rfl

theorem cell23_4757735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4757735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757735 prefixEnd_4757735 := by exact prefixLift 4757735
  have htrace : WordTrace (prefixWord ++ tailWord_4757735) baseStart_4757735 baseEnd_4757735 := by
    simpa [prefixWord, tailWord_4757735, baseEnd_4757735] using wordTrace_append hprefix tailTrace_4757735
  have hstable : (prefixWord ++ tailWord_4757735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757735).length < 2 ^ (prefixWord ++ tailWord_4757735).sum := by decide
  have hdescent : baseEnd_4757735 < baseStart_4757735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757745 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_4757745 : Nat := 118140960795 + 4757745 * 2 ^ 59
def prefixEnd_4757745 : Nat := 4983230072969 + 3 ^ 40 * 4757745 * 2
def baseEnd_4757745 : Nat := 2443010016525593034507035

theorem tailTrace_4757745 : CollatzResearch.WordTrace tailWord_4757745 prefixEnd_4757745 2443010016525593034507035 := by
  unfold tailWord_4757745
  simp only [CollatzResearch.WordTrace]
  refine ⟨173529216148509898000050689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115686144099006598666700459 173529216148509898000050689)
  ·
    refine ⟨130146912111382423500038017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173529216148509898000050689 130146912111382423500038017)
    ·
      refine ⟨97610184083536817625028513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130146912111382423500038017 97610184083536817625028513)
      ·
        refine ⟨73207638062652613218771385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97610184083536817625028513 73207638062652613218771385)
        ·
          refine ⟨54905728546989459914078539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73207638062652613218771385 54905728546989459914078539)
          ·
            refine ⟨82358592820484189871117809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54905728546989459914078539 82358592820484189871117809)
            ·
              refine ⟨61768944615363142403338357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82358592820484189871117809 61768944615363142403338357)
              ·
                refine ⟨5790838557690294600312971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61768944615363142403338357 5790838557690294600312971)
                ·
                  refine ⟨8686257836535441900469457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790838557690294600312971 8686257836535441900469457)
                  ·
                    refine ⟨6514693377401581425352093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8686257836535441900469457 6514693377401581425352093)
                    ·
                      refine ⟨2443010016525593034507035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514693377401581425352093 2443010016525593034507035)
                      ·
                        rfl

theorem cell23_4757745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_4757745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757745 prefixEnd_4757745 := by exact prefixLift 4757745
  have htrace : WordTrace (prefixWord ++ tailWord_4757745) baseStart_4757745 baseEnd_4757745 := by
    simpa [prefixWord, tailWord_4757745, baseEnd_4757745] using wordTrace_append hprefix tailTrace_4757745
  have hstable : (prefixWord ++ tailWord_4757745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757745).length < 2 ^ (prefixWord ++ tailWord_4757745).sum := by decide
  have hdescent : baseEnd_4757745 < baseStart_4757745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757759 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 1, 2, 2]
def baseStart_4757759 : Nat := 118140960795 + 4757759 * 2 ^ 59
def prefixEnd_4757759 : Nat := 4983230072969 + 3 ^ 40 * 4757759 * 2
def baseEnd_4757759 : Nat := 2443017205254755979731971

theorem tailTrace_4757759 : CollatzResearch.WordTrace tailWord_4757759 prefixEnd_4757759 2443017205254755979731971 := by
  unfold tailWord_4757759
  simp only [CollatzResearch.WordTrace]
  refine ⟨173529726770459178391060331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115686484513639452260706887 173529726770459178391060331)
  ·
    refine ⟨260294590155688767586590497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173529726770459178391060331 260294590155688767586590497)
    ·
      refine ⟨195220942616766575689942873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260294590155688767586590497 195220942616766575689942873)
      ·
        refine ⟨146415706962574931767457155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195220942616766575689942873 146415706962574931767457155)
        ·
          refine ⟨219623560443862397651185733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146415706962574931767457155 219623560443862397651185733)
          ·
            refine ⟨41179417583224199559597325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219623560443862397651185733 41179417583224199559597325)
            ·
              refine ⟨15442281593709074834848997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41179417583224199559597325 15442281593709074834848997)
              ·
                refine ⟨2895427798820451531534187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15442281593709074834848997 2895427798820451531534187)
                ·
                  refine ⟨4343141698230677297301281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895427798820451531534187 4343141698230677297301281)
                  ·
                    refine ⟨3257356273673007972975961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4343141698230677297301281 3257356273673007972975961)
                    ·
                      refine ⟨2443017205254755979731971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257356273673007972975961 2443017205254755979731971)
                      ·
                        rfl

theorem cell23_4757759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_4757759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757759 prefixEnd_4757759 := by exact prefixLift 4757759
  have htrace : WordTrace (prefixWord ++ tailWord_4757759) baseStart_4757759 baseEnd_4757759 := by
    simpa [prefixWord, tailWord_4757759, baseEnd_4757759] using wordTrace_append hprefix tailTrace_4757759
  have hstable : (prefixWord ++ tailWord_4757759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757759).length < 2 ^ (prefixWord ++ tailWord_4757759).sum := by decide
  have hdescent : baseEnd_4757759 < baseStart_4757759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757762 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_4757762 : Nat := 118140960795 + 4757762 * 2 ^ 59
def prefixEnd_4757762 : Nat := 4983230072969 + 3 ^ 40 * 4757762 * 2
def baseEnd_4757762 : Nat := 2443018745696719467994457

theorem tailTrace_4757762 : CollatzResearch.WordTrace tailWord_4757762 prefixEnd_4757762 2443018745696719467994457 := by
  unfold tailWord_4757762
  simp only [CollatzResearch.WordTrace]
  refine ⟨43382459047362077475854885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115686557459632206602279693 43382459047362077475854885)
  ·
    refine ⟨8134211071380389526722791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43382459047362077475854885 8134211071380389526722791)
    ·
      refine ⟨12201316607070584290084187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134211071380389526722791 12201316607070584290084187)
      ·
        refine ⟨18301974910605876435126281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201316607070584290084187 18301974910605876435126281)
        ·
          refine ⟨13726481182954407326344711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18301974910605876435126281 13726481182954407326344711)
          ·
            refine ⟨20589721774431610989517067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13726481182954407326344711 20589721774431610989517067)
            ·
              refine ⟨30884582661647416484275601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20589721774431610989517067 30884582661647416484275601)
              ·
                refine ⟨23163436996235562363206701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30884582661647416484275601 23163436996235562363206701)
                ·
                  refine ⟨8686288873588335886202513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23163436996235562363206701 8686288873588335886202513)
                  ·
                    refine ⟨6514716655191251914651885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8686288873588335886202513 6514716655191251914651885)
                    ·
                      refine ⟨2443018745696719467994457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514716655191251914651885 2443018745696719467994457)
                      ·
                        rfl

theorem cell23_4757762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_4757762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757762 prefixEnd_4757762 := by exact prefixLift 4757762
  have htrace : WordTrace (prefixWord ++ tailWord_4757762) baseStart_4757762 baseEnd_4757762 := by
    simpa [prefixWord, tailWord_4757762, baseEnd_4757762] using wordTrace_append hprefix tailTrace_4757762
  have hstable : (prefixWord ++ tailWord_4757762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757762).length < 2 ^ (prefixWord ++ tailWord_4757762).sum := by decide
  have hdescent : baseEnd_4757762 < baseStart_4757762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757788 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4757788 : Nat := 118140960795 + 4757788 * 2 ^ 59
def prefixEnd_4757788 : Nat := 4983230072969 + 3 ^ 40 * 4757788 * 2
def baseEnd_4757788 : Nat := 2443032096193736366269337

theorem tailTrace_4757788 : CollatzResearch.WordTrace tailWord_4757788 prefixEnd_4757788 2443032096193736366269337 := by
  unfold tailWord_4757788
  simp only [CollatzResearch.WordTrace]
  refine ⟨86765392243677058171933009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115687189658236077562577345 86765392243677058171933009)
  ·
    refine ⟨65074044182757793628949757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86765392243677058171933009 65074044182757793628949757)
    ·
      refine ⟨24402766568534172610856159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65074044182757793628949757 24402766568534172610856159)
      ·
        refine ⟨36604149852801258916284239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24402766568534172610856159 36604149852801258916284239)
        ·
          refine ⟨54906224779201888374426359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36604149852801258916284239 54906224779201888374426359)
          ·
            refine ⟨82359337168802832561639539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54906224779201888374426359 82359337168802832561639539)
            ·
              refine ⟨123539005753204248842459309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82359337168802832561639539 123539005753204248842459309)
              ·
                refine ⟨46327127157451593315922241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123539005753204248842459309 46327127157451593315922241)
                ·
                  refine ⟨34745345368088694986941681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46327127157451593315922241 34745345368088694986941681)
                  ·
                    refine ⟨26059009026066521240206261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34745345368088694986941681 26059009026066521240206261)
                    ·
                      refine ⟨2443032096193736366269337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26059009026066521240206261 2443032096193736366269337)
                      ·
                        rfl

theorem cell23_4757788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4757788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757788 prefixEnd_4757788 := by exact prefixLift 4757788
  have htrace : WordTrace (prefixWord ++ tailWord_4757788) baseStart_4757788 baseEnd_4757788 := by
    simpa [prefixWord, tailWord_4757788, baseEnd_4757788] using wordTrace_append hprefix tailTrace_4757788
  have hstable : (prefixWord ++ tailWord_4757788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757788).length < 2 ^ (prefixWord ++ tailWord_4757788).sum := by decide
  have hdescent : baseEnd_4757788 < baseStart_4757788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757815 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_4757815 : Nat := 118140960795 + 4757815 * 2 ^ 59
def prefixEnd_4757815 : Nat := 4983230072969 + 3 ^ 40 * 4757815 * 2
def baseEnd_4757815 : Nat := 2443045960171407760631713

theorem tailTrace_4757815 : CollatzResearch.WordTrace tailWord_4757815 prefixEnd_4757815 2443045960171407760631713 := by
  unfold tailWord_4757815
  simp only [CollatzResearch.WordTrace]
  refine ⟨173531769258256299955098899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115687846172170866636732599 173531769258256299955098899)
  ·
    refine ⟨260297653887384449932648349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173531769258256299955098899 260297653887384449932648349)
    ·
      refine ⟨97611620207769168724743131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260297653887384449932648349 97611620207769168724743131)
      ·
        refine ⟨146417430311653753087114697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97611620207769168724743131 146417430311653753087114697)
        ·
          refine ⟨109813072733740314815336023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146417430311653753087114697 109813072733740314815336023)
          ·
            refine ⟨164719609100610472223004035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109813072733740314815336023 164719609100610472223004035)
            ·
              refine ⟨247079413650915708334506053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164719609100610472223004035 247079413650915708334506053)
              ·
                refine ⟨46327390059546695312719885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247079413650915708334506053 46327390059546695312719885)
                ·
                  refine ⟨17372771272330010742269957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46327390059546695312719885 17372771272330010742269957)
                  ·
                    refine ⟨3257394613561877014175617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17372771272330010742269957 3257394613561877014175617)
                    ·
                      refine ⟨2443045960171407760631713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257394613561877014175617 2443045960171407760631713)
                      ·
                        rfl

theorem cell23_4757815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_4757815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757815 prefixEnd_4757815 := by exact prefixLift 4757815
  have htrace : WordTrace (prefixWord ++ tailWord_4757815) baseStart_4757815 baseEnd_4757815 := by
    simpa [prefixWord, tailWord_4757815, baseEnd_4757815] using wordTrace_append hprefix tailTrace_4757815
  have hstable : (prefixWord ++ tailWord_4757815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757815).length < 2 ^ (prefixWord ++ tailWord_4757815).sum := by decide
  have hdescent : baseEnd_4757815 < baseStart_4757815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757832 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_4757832 : Nat := 118140960795 + 4757832 * 2 ^ 59
def prefixEnd_4757832 : Nat := 4983230072969 + 3 ^ 40 * 4757832 * 2
def baseEnd_4757832 : Nat := 2443054689342534194119135

theorem tailTrace_4757832 : CollatzResearch.WordTrace tailWord_4757832 prefixEnd_4757832 2443054689342534194119135 := by
  unfold tailWord_4757832
  simp only [CollatzResearch.WordTrace]
  refine ⟨86766194649597355929233875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115688259532796474572311833 86766194649597355929233875)
  ·
    refine ⟨130149291974396033893850813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86766194649597355929233875 130149291974396033893850813)
    ·
      refine ⟨48805984490398512710194055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130149291974396033893850813 48805984490398512710194055)
      ·
        refine ⟨73208976735597769065291083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48805984490398512710194055 73208976735597769065291083)
        ·
          refine ⟨109813465103396653597936625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73208976735597769065291083 109813465103396653597936625)
          ·
            refine ⟨82360098827547490198452469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109813465103396653597936625 82360098827547490198452469)
            ·
              refine ⟨7721259265082577206104919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82360098827547490198452469 7721259265082577206104919)
              ·
                refine ⟨11581888897623865809157379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721259265082577206104919 11581888897623865809157379)
                ·
                  refine ⟨17372833346435798713736069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11581888897623865809157379 17372833346435798713736069)
                  ·
                    refine ⟨3257406252456712258825513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17372833346435798713736069 3257406252456712258825513)
                    ·
                      refine ⟨2443054689342534194119135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257406252456712258825513 2443054689342534194119135)
                      ·
                        rfl

theorem cell23_4757832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_4757832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757832 prefixEnd_4757832 := by exact prefixLift 4757832
  have htrace : WordTrace (prefixWord ++ tailWord_4757832) baseStart_4757832 baseEnd_4757832 := by
    simpa [prefixWord, tailWord_4757832, baseEnd_4757832] using wordTrace_append hprefix tailTrace_4757832
  have hstable : (prefixWord ++ tailWord_4757832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757832).length < 2 ^ (prefixWord ++ tailWord_4757832).sum := by decide
  have hdescent : baseEnd_4757832 < baseStart_4757832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757838 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_4757838 : Nat := 118140960795 + 4757838 * 2 ^ 59
def prefixEnd_4757838 : Nat := 4983230072969 + 3 ^ 40 * 4757838 * 2
def baseEnd_4757838 : Nat := 271450863358495685627123

theorem tailTrace_4757838 : CollatzResearch.WordTrace tailWord_4757838 prefixEnd_4757838 271450863358495685627123 := by
  unfold tailWord_4757838
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691576017146621860398271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115688405424781983255457445 21691576017146621860398271)
  ·
    refine ⟨32537364025719932790597407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21691576017146621860398271 32537364025719932790597407)
    ·
      refine ⟨48806046038579899185896111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32537364025719932790597407 48806046038579899185896111)
      ·
        refine ⟨73209069057869848778844167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48806046038579899185896111 73209069057869848778844167)
        ·
          refine ⟨109813603586804773168266251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73209069057869848778844167 109813603586804773168266251)
          ·
            refine ⟨164720405380207159752399377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109813603586804773168266251 164720405380207159752399377)
            ·
              refine ⟨123540304035155369814299533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164720405380207159752399377 123540304035155369814299533)
              ·
                refine ⟨46327614013183263680362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123540304035155369814299533 46327614013183263680362325)
                ·
                  refine ⟨271450863358495685627123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46327614013183263680362325 271450863358495685627123)
                  ·
                    rfl

theorem cell23_4757838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_4757838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757838 prefixEnd_4757838 := by exact prefixLift 4757838
  have htrace : WordTrace (prefixWord ++ tailWord_4757838) baseStart_4757838 baseEnd_4757838 := by
    simpa [prefixWord, tailWord_4757838, baseEnd_4757838] using wordTrace_append hprefix tailTrace_4757838
  have hstable : (prefixWord ++ tailWord_4757838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757838).length < 2 ^ (prefixWord ++ tailWord_4757838).sum := by decide
  have hdescent : baseEnd_4757838 < baseStart_4757838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757875 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 7, 2]
def baseStart_4757875 : Nat := 118140960795 + 4757875 * 2 ^ 59
def prefixEnd_4757875 : Nat := 4983230072969 + 3 ^ 40 * 4757875 * 2
def baseEnd_4757875 : Nat := 2443076769010677525881437

theorem tailTrace_4757875 : CollatzResearch.WordTrace tailWord_4757875 prefixEnd_4757875 2443076769010677525881437 := by
  unfold tailWord_4757875
  simp only [CollatzResearch.WordTrace]
  refine ⟨173533957638038930202283079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115689305092025953468188719 173533957638038930202283079)
  ·
    refine ⟨260300936457058395303424619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173533957638038930202283079 260300936457058395303424619)
    ·
      refine ⟨390451404685587592955136929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260300936457058395303424619 390451404685587592955136929)
      ·
        refine ⟨292838553514190694716352697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390451404685587592955136929 292838553514190694716352697)
        ·
          refine ⟨219628915135643021037264523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292838553514190694716352697 219628915135643021037264523)
          ·
            refine ⟨329443372703464531555896785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219628915135643021037264523 329443372703464531555896785)
            ·
              refine ⟨247082529527598398666922589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329443372703464531555896785 247082529527598398666922589)
              ·
                refine ⟨92655948572849399500095971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247082529527598398666922589 92655948572849399500095971)
                ·
                  refine ⟨138983922859274099250143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92655948572849399500095971 138983922859274099250143957)
                  ·
                    refine ⟨3257435692014236701175249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138983922859274099250143957 3257435692014236701175249)
                    ·
                      refine ⟨2443076769010677525881437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257435692014236701175249 2443076769010677525881437)
                      ·
                        rfl

theorem cell23_4757875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7, 2].length) (baseStart_4757875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757875 prefixEnd_4757875 := by exact prefixLift 4757875
  have htrace : WordTrace (prefixWord ++ tailWord_4757875) baseStart_4757875 baseEnd_4757875 := by
    simpa [prefixWord, tailWord_4757875, baseEnd_4757875] using wordTrace_append hprefix tailTrace_4757875
  have hstable : (prefixWord ++ tailWord_4757875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757875).length < 2 ^ (prefixWord ++ tailWord_4757875).sum := by decide
  have hdescent : baseEnd_4757875 < baseStart_4757875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757902 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_4757902 : Nat := 118140960795 + 4757902 * 2 ^ 59
def prefixEnd_4757902 : Nat := 4983230072969 + 3 ^ 40 * 4757902 * 2
def baseEnd_4757902 : Nat := 814363544329449640081271

theorem tailTrace_4757902 : CollatzResearch.WordTrace tailWord_4757902 prefixEnd_4757902 814363544329449640081271 := by
  unfold tailWord_4757902
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691867801117639226689495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115689961605960742542343973 21691867801117639226689495)
  ·
    refine ⟨32537801701676458840034243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21691867801117639226689495 32537801701676458840034243)
    ·
      refine ⟨48806702552514688260051365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32537801701676458840034243 48806702552514688260051365)
      ·
        refine ⟨9151256728596504048759631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48806702552514688260051365 9151256728596504048759631)
        ·
          refine ⟨13726885092894756073139447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9151256728596504048759631 13726885092894756073139447)
          ·
            refine ⟨20590327639342134109709171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13726885092894756073139447 20590327639342134109709171)
            ·
              refine ⟨30885491459013201164563757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20590327639342134109709171 30885491459013201164563757)
              ·
                refine ⟨11582059297129950436711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30885491459013201164563757 11582059297129950436711409)
                ·
                  refine ⟨8686544472847462827533557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582059297129950436711409 8686544472847462827533557)
                  ·
                    refine ⟨814363544329449640081271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8686544472847462827533557 814363544329449640081271)
                    ·
                      rfl

theorem cell23_4757902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_4757902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757902 prefixEnd_4757902 := by exact prefixLift 4757902
  have htrace : WordTrace (prefixWord ++ tailWord_4757902) baseStart_4757902 baseEnd_4757902 := by
    simpa [prefixWord, tailWord_4757902, baseEnd_4757902] using wordTrace_append hprefix tailTrace_4757902
  have hstable : (prefixWord ++ tailWord_4757902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757902).length < 2 ^ (prefixWord ++ tailWord_4757902).sum := by decide
  have hdescent : baseEnd_4757902 < baseStart_4757902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757922 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4757922 : Nat := 118140960795 + 4757922 * 2 ^ 59
def prefixEnd_4757922 : Nat := 4983230072969 + 3 ^ 40 * 4757922 * 2
def baseEnd_4757922 : Nat := 2443100902601438841993721

theorem tailTrace_4757922 : CollatzResearch.WordTrace tailWord_4757922 prefixEnd_4757922 2443100902601438841993721 := by
  unfold tailWord_4757922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43383917967217164307311005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115690447912579104819496013 43383917967217164307311005)
  ·
    refine ⟨16268969237706436615241627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43383917967217164307311005 16268969237706436615241627)
    ·
      refine ⟨24403453856559654922862441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16268969237706436615241627 24403453856559654922862441)
      ·
        refine ⟨18302590392419741192146831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24403453856559654922862441 18302590392419741192146831)
        ·
          refine ⟨27453885588629611788220247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18302590392419741192146831 27453885588629611788220247)
          ·
            refine ⟨41180828382944417682330371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27453885588629611788220247 41180828382944417682330371)
            ·
              refine ⟨61771242574416626523495557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41180828382944417682330371 61771242574416626523495557)
              ·
                refine ⟨11582107982703117473155417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61771242574416626523495557 11582107982703117473155417)
                ·
                  refine ⟨8686580987027338104866563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582107982703117473155417 8686580987027338104866563)
                  ·
                    refine ⟨13029871480541007157299845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8686580987027338104866563 13029871480541007157299845)
                    ·
                      refine ⟨2443100902601438841993721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13029871480541007157299845 2443100902601438841993721)
                      ·
                        rfl

theorem cell23_4757922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4757922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757922 prefixEnd_4757922 := by exact prefixLift 4757922
  have htrace : WordTrace (prefixWord ++ tailWord_4757922) baseStart_4757922 baseEnd_4757922 := by
    simpa [prefixWord, tailWord_4757922, baseEnd_4757922] using wordTrace_append hprefix tailTrace_4757922
  have hstable : (prefixWord ++ tailWord_4757922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757922).length < 2 ^ (prefixWord ++ tailWord_4757922).sum := by decide
  have hdescent : baseEnd_4757922 < baseStart_4757922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757953 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4757953 : Nat := 118140960795 + 4757953 * 2 ^ 59
def prefixEnd_4757953 : Nat := 4983230072969 + 3 ^ 40 * 4757953 * 2
def baseEnd_4757953 : Nat := 814372273500576073568693

theorem tailTrace_4757953 : CollatzResearch.WordTrace tailWord_4757953 prefixEnd_4757953 814372273500576073568693 := by
  unfold tailWord_4757953
  simp only [CollatzResearch.WordTrace]
  refine ⟨173536802531756349523622513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115691201687837566349081675 173536802531756349523622513)
  ·
    refine ⟨130152601898817262142716885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173536802531756349523622513 130152601898817262142716885)
    ·
      refine ⟨3050451607003529581469927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 130152601898817262142716885 3050451607003529581469927)
      ·
        refine ⟨4575677410505294372204891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050451607003529581469927 4575677410505294372204891)
        ·
          refine ⟨6863516115757941558307337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575677410505294372204891 6863516115757941558307337)
          ·
            refine ⟨5147637086818456168730503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863516115757941558307337 5147637086818456168730503)
            ·
              refine ⟨7721455630227684253095755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147637086818456168730503 7721455630227684253095755)
              ·
                refine ⟨11582183445341526379643633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721455630227684253095755 11582183445341526379643633)
                ·
                  refine ⟨8686637584006144784732725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582183445341526379643633 8686637584006144784732725)
                  ·
                    refine ⟨814372273500576073568693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8686637584006144784732725 814372273500576073568693)
                    ·
                      rfl

theorem cell23_4757953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4757953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757953 prefixEnd_4757953 := by exact prefixLift 4757953
  have htrace : WordTrace (prefixWord ++ tailWord_4757953) baseStart_4757953 baseEnd_4757953 := by
    simpa [prefixWord, tailWord_4757953, baseEnd_4757953] using wordTrace_append hprefix tailTrace_4757953
  have hstable : (prefixWord ++ tailWord_4757953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757953).length < 2 ^ (prefixWord ++ tailWord_4757953).sum := by decide
  have hdescent : baseEnd_4757953 < baseStart_4757953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757956 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4757956 : Nat := 118140960795 + 4757956 * 2 ^ 59
def prefixEnd_4757956 : Nat := 4983230072969 + 3 ^ 40 * 4757956 * 2
def baseEnd_4757956 : Nat := 2443118360943691708968565

theorem tailTrace_4757956 : CollatzResearch.WordTrace tailWord_4757956 prefixEnd_4757956 2443118360943691708968565 := by
  unfold tailWord_4757956
  simp only [CollatzResearch.WordTrace]
  refine ⟨86768455975372740517990861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115691274633830320690654481 86768455975372740517990861)
  ·
    refine ⟨32538170990764777694246573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86768455975372740517990861 32538170990764777694246573)
    ·
      refine ⟨12201814121536791635342465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32538170990764777694246573 12201814121536791635342465)
      ·
        refine ⟨9151360591152593726506849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12201814121536791635342465 9151360591152593726506849)
        ·
          refine ⟨6863520443364445294880137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9151360591152593726506849 6863520443364445294880137)
          ·
            refine ⟨5147640332523333971160103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863520443364445294880137 5147640332523333971160103)
            ·
              refine ⟨7721460498785000956740155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147640332523333971160103 7721460498785000956740155)
              ·
                refine ⟨11582190748177501435110233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721460498785000956740155 11582190748177501435110233)
                ·
                  refine ⟨8686643061133126076332675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582190748177501435110233 8686643061133126076332675)
                  ·
                    refine ⟨13029964591699689114499013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8686643061133126076332675 13029964591699689114499013)
                    ·
                      refine ⟨2443118360943691708968565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13029964591699689114499013 2443118360943691708968565)
                      ·
                        rfl

theorem cell23_4757956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4757956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757956 prefixEnd_4757956 := by exact prefixLift 4757956
  have htrace : WordTrace (prefixWord ++ tailWord_4757956) baseStart_4757956 baseEnd_4757956 := by
    simpa [prefixWord, tailWord_4757956, baseEnd_4757956] using wordTrace_append hprefix tailTrace_4757956
  have hstable : (prefixWord ++ tailWord_4757956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757956).length < 2 ^ (prefixWord ++ tailWord_4757956).sum := by decide
  have hdescent : baseEnd_4757956 < baseStart_4757956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4757959 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_4757959 : Nat := 118140960795 + 4757959 * 2 ^ 59
def prefixEnd_4757959 : Nat := 4983230072969 + 3 ^ 40 * 4757959 * 2
def baseEnd_4757959 : Nat := 2443119901385655197231051

theorem tailTrace_4757959 : CollatzResearch.WordTrace tailWord_4757959 prefixEnd_4757959 2443119901385655197231051 := by
  unfold tailWord_4757959
  simp only [CollatzResearch.WordTrace]
  refine ⟨173537021369734612548340931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115691347579823075032227287 173537021369734612548340931)
  ·
    refine ⟨260305532054601918822511397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173537021369734612548340931 260305532054601918822511397)
    ·
      refine ⟨48807287260237859779220887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260305532054601918822511397 48807287260237859779220887)
      ·
        refine ⟨73210930890356789668831331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48807287260237859779220887 73210930890356789668831331)
        ·
          refine ⟨109816396335535184503246997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73210930890356789668831331 109816396335535184503246997)
          ·
            refine ⟨5147643578228211773589703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109816396335535184503246997 5147643578228211773589703)
            ·
              refine ⟨7721465367342317660384555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147643578228211773589703 7721465367342317660384555)
              ·
                refine ⟨11582198051013476490576833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721465367342317660384555 11582198051013476490576833)
                ·
                  refine ⟨8686648538260107367932625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582198051013476490576833 8686648538260107367932625)
                  ·
                    refine ⟨6514986403695080525949469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8686648538260107367932625 6514986403695080525949469)
                    ·
                      refine ⟨2443119901385655197231051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6514986403695080525949469 2443119901385655197231051)
                      ·
                        rfl

theorem cell23_4757959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_4757959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4757959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4757959 prefixEnd_4757959 := by exact prefixLift 4757959
  have htrace : WordTrace (prefixWord ++ tailWord_4757959) baseStart_4757959 baseEnd_4757959 := by
    simpa [prefixWord, tailWord_4757959, baseEnd_4757959] using wordTrace_append hprefix tailTrace_4757959
  have hstable : (prefixWord ++ tailWord_4757959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4757959).length < 2 ^ (prefixWord ++ tailWord_4757959).sum := by decide
  have hdescent : baseEnd_4757959 < baseStart_4757959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4757959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758012 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_4758012 : Nat := 118140960795 + 4758012 * 2 ^ 59
def prefixEnd_4758012 : Nat := 4983230072969 + 3 ^ 40 * 4758012 * 2
def baseEnd_4758012 : Nat := 2443147115860343489868307

theorem tailTrace_4758012 : CollatzResearch.WordTrace tailWord_4758012 prefixEnd_4758012 2443147115860343489868307 := by
  unfold tailWord_4758012
  simp only [CollatzResearch.WordTrace]
  refine ⟨86769477219271301300010145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115692636292361735066680193 86769477219271301300010145)
  ·
    refine ⟨65077107914453475975007609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86769477219271301300010145 65077107914453475975007609)
    ·
      refine ⟨48807830935840106981255707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65077107914453475975007609 48807830935840106981255707)
      ·
        refine ⟨73211746403760160471883561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48807830935840106981255707 73211746403760160471883561)
        ·
          refine ⟨54908809802820120353912671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73211746403760160471883561 54908809802820120353912671)
          ·
            refine ⟨82363214704230180530869007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54908809802820120353912671 82363214704230180530869007)
            ·
              refine ⟨123544822056345270796303511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82363214704230180530869007 123544822056345270796303511)
              ·
                refine ⟨185317233084517906194455267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123544822056345270796303511 185317233084517906194455267)
                ·
                  refine ⟨277975849626776859291682901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185317233084517906194455267 277975849626776859291682901)
                  ·
                    refine ⟨3257529487813791319824409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 277975849626776859291682901 3257529487813791319824409)
                    ·
                      refine ⟨2443147115860343489868307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257529487813791319824409 2443147115860343489868307)
                      ·
                        rfl

theorem cell23_4758012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_4758012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758012 prefixEnd_4758012 := by exact prefixLift 4758012
  have htrace : WordTrace (prefixWord ++ tailWord_4758012) baseStart_4758012 baseEnd_4758012 := by
    simpa [prefixWord, tailWord_4758012, baseEnd_4758012] using wordTrace_append hprefix tailTrace_4758012
  have hstable : (prefixWord ++ tailWord_4758012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758012).length < 2 ^ (prefixWord ++ tailWord_4758012).sum := by decide
  have hdescent : baseEnd_4758012 < baseStart_4758012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758015 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_4758015 : Nat := 118140960795 + 4758015 * 2 ^ 59
def prefixEnd_4758015 : Nat := 4983230072969 + 3 ^ 40 * 4758015 * 2
def baseEnd_4758015 : Nat := 2443148656302306978130793

theorem tailTrace_4758015 : CollatzResearch.WordTrace tailWord_4758015 prefixEnd_4758015 2443148656302306978130793 := by
  unfold tailWord_4758015
  simp only [CollatzResearch.WordTrace]
  refine ⟨173539063857531734112379499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115692709238354489408252999 173539063857531734112379499)
  ·
    refine ⟨260308595786297601168569249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173539063857531734112379499 260308595786297601168569249)
    ·
      refine ⟨195231446839723200876426937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260308595786297601168569249 195231446839723200876426937)
      ·
        refine ⟨146423585129792400657320203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195231446839723200876426937 146423585129792400657320203)
        ·
          refine ⟨219635377694688600985980305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146423585129792400657320203 219635377694688600985980305)
          ·
            refine ⟨164726533271016450739485229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219635377694688600985980305 164726533271016450739485229)
            ·
              refine ⟨61772449976631169027306961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164726533271016450739485229 61772449976631169027306961)
              ·
                refine ⟨46329337482473376770480221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61772449976631169027306961 46329337482473376770480221)
                ·
                  refine ⟨17373501555927516288930083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46329337482473376770480221 17373501555927516288930083)
                  ·
                    refine ⟨26060252333891274433395125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17373501555927516288930083 26060252333891274433395125)
                    ·
                      refine ⟨2443148656302306978130793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26060252333891274433395125 2443148656302306978130793)
                      ·
                        rfl

theorem cell23_4758015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_4758015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758015 prefixEnd_4758015 := by exact prefixLift 4758015
  have htrace : WordTrace (prefixWord ++ tailWord_4758015) baseStart_4758015 baseEnd_4758015 := by
    simpa [prefixWord, tailWord_4758015, baseEnd_4758015] using wordTrace_append hprefix tailTrace_4758015
  have hstable : (prefixWord ++ tailWord_4758015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758015).length < 2 ^ (prefixWord ++ tailWord_4758015).sum := by decide
  have hdescent : baseEnd_4758015 < baseStart_4758015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758056 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4758056 : Nat := 118140960795 + 4758056 * 2 ^ 59
def prefixEnd_4758056 : Nat := 4983230072969 + 3 ^ 40 * 4758056 * 2
def baseEnd_4758056 : Nat := 814389903003047105906035

theorem tailTrace_4758056 : CollatzResearch.WordTrace tailWord_4758056 prefixEnd_4758056 814389903003047105906035 := by
  unfold tailWord_4758056
  simp only [CollatzResearch.WordTrace]
  refine ⟨86770279625191599057311011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115693706166922132076414681 86770279625191599057311011)
  ·
    refine ⟨130155419437787398585966517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86770279625191599057311011 130155419437787398585966517)
    ·
      refine ⟨12202070572292568617434361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130155419437787398585966517 12202070572292568617434361)
      ·
        refine ⟨9151552929219426463075771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12202070572292568617434361 9151552929219426463075771)
        ·
          refine ⟨13727329393829139694613657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9151552929219426463075771 13727329393829139694613657)
          ·
            refine ⟨10295497045371854770960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13727329393829139694613657 10295497045371854770960243)
            ·
              refine ⟨15443245568057782156440365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295497045371854770960243 15443245568057782156440365)
              ·
                refine ⟨5791217088021668308665137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15443245568057782156440365 5791217088021668308665137)
                ·
                  refine ⟨4343412816016251231498853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791217088021668308665137 4343412816016251231498853)
                  ·
                    refine ⟨814389903003047105906035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343412816016251231498853 814389903003047105906035)
                    ·
                      rfl

theorem cell23_4758056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4758056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758056 prefixEnd_4758056 := by exact prefixLift 4758056
  have htrace : WordTrace (prefixWord ++ tailWord_4758056) baseStart_4758056 baseEnd_4758056 := by
    simpa [prefixWord, tailWord_4758056, baseEnd_4758056] using wordTrace_append hprefix tailTrace_4758056
  have hstable : (prefixWord ++ tailWord_4758056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758056).length < 2 ^ (prefixWord ++ tailWord_4758056).sum := by decide
  have hdescent : baseEnd_4758056 < baseStart_4758056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758075 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_4758075 : Nat := 118140960795 + 4758075 * 2 ^ 59
def prefixEnd_4758075 : Nat := 4983230072969 + 3 ^ 40 * 4758075 * 2
def baseEnd_4758075 : Nat := 2443179465141576743380517

theorem tailTrace_4758075 : CollatzResearch.WordTrace tailWord_4758075 prefixEnd_4758075 2443179465141576743380517 := by
  unfold tailWord_4758075
  simp only [CollatzResearch.WordTrace]
  refine ⟨173541252237314364359563679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115694168158209576239709119 173541252237314364359563679)
  ·
    refine ⟨260311878355971546539345519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173541252237314364359563679 260311878355971546539345519)
    ·
      refine ⟨390467817533957319809018279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260311878355971546539345519 390467817533957319809018279)
      ·
        refine ⟨585701726300935979713527419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390467817533957319809018279 585701726300935979713527419)
        ·
          refine ⟨878552589451403969570291129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585701726300935979713527419 878552589451403969570291129)
          ·
            refine ⟨658914442088552977177718347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878552589451403969570291129 658914442088552977177718347)
            ·
              refine ⟨988371663132829465766577521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658914442088552977177718347 988371663132829465766577521)
              ·
                refine ⟨741278747349622099324933141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988371663132829465766577521 741278747349622099324933141)
                ·
                  refine ⟨34747441282013535905856241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 741278747349622099324933141 34747441282013535905856241)
                  ·
                    refine ⟨26060580961510151929392181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34747441282013535905856241 26060580961510151929392181)
                    ·
                      refine ⟨2443179465141576743380517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26060580961510151929392181 2443179465141576743380517)
                      ·
                        rfl

theorem cell23_4758075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_4758075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758075 prefixEnd_4758075 := by exact prefixLift 4758075
  have htrace : WordTrace (prefixWord ++ tailWord_4758075) baseStart_4758075 baseEnd_4758075 := by
    simpa [prefixWord, tailWord_4758075, baseEnd_4758075] using wordTrace_append hprefix tailTrace_4758075
  have hstable : (prefixWord ++ tailWord_4758075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758075).length < 2 ^ (prefixWord ++ tailWord_4758075).sum := by decide
  have hdescent : baseEnd_4758075 < baseStart_4758075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758110 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4758110 : Nat := 118140960795 + 4758110 * 2 ^ 59
def prefixEnd_4758110 : Nat := 4983230072969 + 3 ^ 40 * 4758110 * 2
def baseEnd_4758110 : Nat := 2443197436964484106442857

theorem tailTrace_4758110 : CollatzResearch.WordTrace tailWord_4758110 prefixEnd_4758110 2443197436964484106442857 := by
  unfold tailWord_4758110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21692816099023445667135973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115695019194791710224725189 21692816099023445667135973)
  ·
    refine ⟨4067403018566896062587995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21692816099023445667135973 4067403018566896062587995)
    ·
      refine ⟨6101104527850344093881993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067403018566896062587995 6101104527850344093881993)
      ·
        refine ⟨4575828395887758070411495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6101104527850344093881993 4575828395887758070411495)
        ·
          refine ⟨6863742593831637105617243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575828395887758070411495 6863742593831637105617243)
          ·
            refine ⟨10295613890747455658425865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863742593831637105617243 10295613890747455658425865)
            ·
              refine ⟨7721710418060591743819399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10295613890747455658425865 7721710418060591743819399)
              ·
                refine ⟨11582565627090887615729099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721710418060591743819399 11582565627090887615729099)
                ·
                  refine ⟨17373848440636331423593649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11582565627090887615729099 17373848440636331423593649)
                  ·
                    refine ⟨13030386330477248567695237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17373848440636331423593649 13030386330477248567695237)
                    ·
                      refine ⟨2443197436964484106442857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13030386330477248567695237 2443197436964484106442857)
                      ·
                        rfl

theorem cell23_4758110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4758110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758110 prefixEnd_4758110 := by exact prefixLift 4758110
  have htrace : WordTrace (prefixWord ++ tailWord_4758110) baseStart_4758110 baseEnd_4758110 := by
    simpa [prefixWord, tailWord_4758110, baseEnd_4758110] using wordTrace_append hprefix tailTrace_4758110
  have hstable : (prefixWord ++ tailWord_4758110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758110).length < 2 ^ (prefixWord ++ tailWord_4758110).sum := by decide
  have hdescent : baseEnd_4758110 < baseStart_4758110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758170 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4758170 : Nat := 118140960795 + 4758170 * 2 ^ 59
def prefixEnd_4758170 : Nat := 4983230072969 + 3 ^ 40 * 4758170 * 2
def baseEnd_4758170 : Nat := 2443228245803753871692581

theorem tailTrace_4758170 : CollatzResearch.WordTrace tailWord_4758170 prefixEnd_4758170 2443228245803753871692581 := by
  unfold tailWord_4758170
  simp only [CollatzResearch.WordTrace]
  refine ⟨43386179292992548896067991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115696478114646797056181309 43386179292992548896067991)
  ·
    refine ⟨65079268939488823344101987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43386179292992548896067991 65079268939488823344101987)
    ·
      refine ⟨97618903409233235016152981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65079268939488823344101987 97618903409233235016152981)
      ·
        refine ⟨4575886097307807891382171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97618903409233235016152981 4575886097307807891382171)
        ·
          refine ⟨6863829145961711837073257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575886097307807891382171 6863829145961711837073257)
          ·
            refine ⟨5147871859471283877804943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863829145961711837073257 5147871859471283877804943)
            ·
              refine ⟨7721807789206925816707415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147871859471283877804943 7721807789206925816707415)
              ·
                refine ⟨11582711683810388725061123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721807789206925816707415 11582711683810388725061123)
                ·
                  refine ⟨17374067525715583087591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11582711683810388725061123 17374067525715583087591685)
                  ·
                    refine ⟨3257637661071671828923441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17374067525715583087591685 3257637661071671828923441)
                    ·
                      refine ⟨2443228245803753871692581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257637661071671828923441 2443228245803753871692581)
                      ·
                        rfl

theorem cell23_4758170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4758170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758170 prefixEnd_4758170 := by exact prefixLift 4758170
  have htrace : WordTrace (prefixWord ++ tailWord_4758170) baseStart_4758170 baseEnd_4758170 := by
    simpa [prefixWord, tailWord_4758170, baseEnd_4758170] using wordTrace_append hprefix tailTrace_4758170
  have hstable : (prefixWord ++ tailWord_4758170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758170).length < 2 ^ (prefixWord ++ tailWord_4758170).sum := by decide
  have hdescent : baseEnd_4758170 < baseStart_4758170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758189 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4758189 : Nat := 118140960795 + 4758189 * 2 ^ 59
def prefixEnd_4758189 : Nat := 4983230072969 + 3 ^ 40 * 4758189 * 2
def baseEnd_4758189 : Nat := 814412667312063099118331

theorem tailTrace_4758189 : CollatzResearch.WordTrace tailWord_4758189 prefixEnd_4758189 814412667312063099118331 := by
  unfold tailWord_4758189
  simp only [CollatzResearch.WordTrace]
  refine ⟨173545410158901361829213621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115696940105934241219475747 173545410158901361829213621)
  ·
    refine ⟨16269882202397002671488777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173545410158901361829213621 16269882202397002671488777)
    ·
      refine ⟨12202411651797752003616583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16269882202397002671488777 12202411651797752003616583)
      ·
        refine ⟨18303617477696628005424875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12202411651797752003616583 18303617477696628005424875)
        ·
          refine ⟨27455426216544942008137313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18303617477696628005424875 27455426216544942008137313)
          ·
            refine ⟨20591569662408706506102985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27455426216544942008137313 20591569662408706506102985)
            ·
              refine ⟨15443677246806529879577239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20591569662408706506102985 15443677246806529879577239)
              ·
                refine ⟨23165515870209794819365859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15443677246806529879577239 23165515870209794819365859)
                ·
                  refine ⟨34748273805314692229048789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23165515870209794819365859 34748273805314692229048789)
                  ·
                    refine ⟨814412667312063099118331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34748273805314692229048789 814412667312063099118331)
                    ·
                      rfl

theorem cell23_4758189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4758189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758189 prefixEnd_4758189 := by exact prefixLift 4758189
  have htrace : WordTrace (prefixWord ++ tailWord_4758189) baseStart_4758189 baseEnd_4758189 := by
    simpa [prefixWord, tailWord_4758189, baseEnd_4758189] using wordTrace_append hprefix tailTrace_4758189
  have hstable : (prefixWord ++ tailWord_4758189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758189).length < 2 ^ (prefixWord ++ tailWord_4758189).sum := by decide
  have hdescent : baseEnd_4758189 < baseStart_4758189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758221 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4758221 : Nat := 118140960795 + 4758221 * 2 ^ 59
def prefixEnd_4758221 : Nat := 4983230072969 + 3 ^ 40 * 4758221 * 2
def baseEnd_4758221 : Nat := 2443254433317133172154847

theorem tailTrace_4758221 : CollatzResearch.WordTrace tailWord_4758221 prefixEnd_4758221 2443254433317133172154847 := by
  unfold tailWord_4758221
  simp only [CollatzResearch.WordTrace]
  refine ⟨173546577294785431294378517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115697718196523620862919011 173546577294785431294378517)
  ·
    refine ⟨8134995810693067091923993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173546577294785431294378517 8134995810693067091923993)
    ·
      refine ⟨6101246858019800318942995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8134995810693067091923993 6101246858019800318942995)
      ·
        refine ⟨9151870287029700478414493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6101246858019800318942995 9151870287029700478414493)
        ·
          refine ⟨3431951357636137679405435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9151870287029700478414493 3431951357636137679405435)
          ·
            refine ⟨5147927036454206519108153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431951357636137679405435 5147927036454206519108153)
            ·
              refine ⟨3860945277340654889331115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5147927036454206519108153 3860945277340654889331115)
              ·
                refine ⟨5791417916010982333996673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860945277340654889331115 5791417916010982333996673)
                ·
                  refine ⟨4343563437008236750497505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791417916010982333996673 4343563437008236750497505)
                  ·
                    refine ⟨3257672577756177562873129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4343563437008236750497505 3257672577756177562873129)
                    ·
                      refine ⟨2443254433317133172154847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257672577756177562873129 2443254433317133172154847)
                      ·
                        rfl

theorem cell23_4758221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4758221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758221 prefixEnd_4758221 := by exact prefixLift 4758221
  have htrace : WordTrace (prefixWord ++ tailWord_4758221) baseStart_4758221 baseEnd_4758221 := by
    simpa [prefixWord, tailWord_4758221, baseEnd_4758221] using wordTrace_append hprefix tailTrace_4758221
  have hstable : (prefixWord ++ tailWord_4758221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758221).length < 2 ^ (prefixWord ++ tailWord_4758221).sum := by decide
  have hdescent : baseEnd_4758221 < baseStart_4758221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758252 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_4758252 : Nat := 118140960795 + 4758252 * 2 ^ 59
def prefixEnd_4758252 : Nat := 4983230072969 + 3 ^ 40 * 4758252 * 2
def baseEnd_4758252 : Nat := 2443270351217422550867203

theorem tailTrace_4758252 : CollatzResearch.WordTrace tailWord_4758252 prefixEnd_4758252 2443270351217422550867203 := by
  unfold tailWord_4758252
  simp only [CollatzResearch.WordTrace]
  refine ⟨86773853978836561794378505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115698471971782082392504673 86773853978836561794378505)
  ·
    refine ⟨65080390484127421345783879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86773853978836561794378505 65080390484127421345783879)
    ·
      refine ⟨97620585726191132018675819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65080390484127421345783879 97620585726191132018675819)
      ·
        refine ⟨146430878589286698028013729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97620585726191132018675819 146430878589286698028013729)
        ·
          refine ⟨109823158941965023521010297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146430878589286698028013729 109823158941965023521010297)
          ·
            refine ⟨82367369206473767640757723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109823158941965023521010297 82367369206473767640757723)
            ·
              refine ⟨123551053809710651461136585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82367369206473767640757723 123551053809710651461136585)
              ·
                refine ⟨92663290357282988595852439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123551053809710651461136585 92663290357282988595852439)
                ·
                  refine ⟨138994935535924482893778659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92663290357282988595852439 138994935535924482893778659)
                  ·
                    refine ⟨208492403303886724340667989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138994935535924482893778659 208492403303886724340667989)
                    ·
                      refine ⟨2443270351217422550867203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208492403303886724340667989 2443270351217422550867203)
                      ·
                        rfl

theorem cell23_4758252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_4758252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758252 prefixEnd_4758252 := by exact prefixLift 4758252
  have htrace : WordTrace (prefixWord ++ tailWord_4758252) baseStart_4758252 baseEnd_4758252 := by
    simpa [prefixWord, tailWord_4758252, baseEnd_4758252] using wordTrace_append hprefix tailTrace_4758252
  have hstable : (prefixWord ++ tailWord_4758252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758252).length < 2 ^ (prefixWord ++ tailWord_4758252).sum := by decide
  have hdescent : baseEnd_4758252 < baseStart_4758252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758253 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_4758253 : Nat := 118140960795 + 4758253 * 2 ^ 59
def prefixEnd_4758253 : Nat := 4983230072969 + 3 ^ 40 * 4758253 * 2
def baseEnd_4758253 : Nat := 814423621566025682318233

theorem tailTrace_4758253 : CollatzResearch.WordTrace tailWord_4758253 prefixEnd_4758253 814423621566025682318233 := by
  unfold tailWord_4758253
  simp only [CollatzResearch.WordTrace]
  refine ⟨173547744430669500759543413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115698496287113000506362275 173547744430669500759543413)
  ·
    refine ⟨16270101040375265696207195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173547744430669500759543413 16270101040375265696207195)
    ·
      refine ⟨24405151560562898544310793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16270101040375265696207195 24405151560562898544310793)
      ·
        refine ⟨18303863670422173908233095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24405151560562898544310793 18303863670422173908233095)
        ·
          refine ⟨27455795505633260862349643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18303863670422173908233095 27455795505633260862349643)
          ·
            refine ⟨41183693258449891293524465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27455795505633260862349643 41183693258449891293524465)
            ·
              refine ⟨30887769943837418470143349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41183693258449891293524465 30887769943837418470143349)
              ·
                refine ⟨2895728432234757981575939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30887769943837418470143349 2895728432234757981575939)
                ·
                  refine ⟨4343592648352136972363909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895728432234757981575939 4343592648352136972363909)
                  ·
                    refine ⟨814423621566025682318233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343592648352136972363909 814423621566025682318233)
                    ·
                      rfl

theorem cell23_4758253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_4758253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758253 prefixEnd_4758253 := by exact prefixLift 4758253
  have htrace : WordTrace (prefixWord ++ tailWord_4758253) baseStart_4758253 baseEnd_4758253 := by
    simpa [prefixWord, tailWord_4758253, baseEnd_4758253] using wordTrace_append hprefix tailTrace_4758253
  have hstable : (prefixWord ++ tailWord_4758253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758253).length < 2 ^ (prefixWord ++ tailWord_4758253).sum := by decide
  have hdescent : baseEnd_4758253 < baseStart_4758253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758270 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4758270 : Nat := 118140960795 + 4758270 * 2 ^ 59
def prefixEnd_4758270 : Nat := 4983230072969 + 3 ^ 40 * 4758270 * 2
def baseEnd_4758270 : Nat := 814426531289734493480707

theorem tailTrace_4758270 : CollatzResearch.WordTrace tailWord_4758270 prefixEnd_4758270 814426531289734493480707 := by
  unfold tailWord_4758270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693545558950989082864033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115698909647738608441941509 21693545558950989082864033)
  ·
    refine ⟨16270159169213241812148025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21693545558950989082864033 16270159169213241812148025)
    ·
      refine ⟨12202619376909931359111019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16270159169213241812148025 12202619376909931359111019)
      ·
        refine ⟨18303929065364897038666529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12202619376909931359111019 18303929065364897038666529)
        ·
          refine ⟨13727946799023672778999897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18303929065364897038666529 13727946799023672778999897)
          ·
            refine ⟨10295960099267754584249923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13727946799023672778999897 10295960099267754584249923)
            ·
              refine ⟨15443940148901631876374885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295960099267754584249923 15443940148901631876374885)
              ·
                refine ⟨2895738777919055976820291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15443940148901631876374885 2895738777919055976820291)
                ·
                  refine ⟨4343608166878583965230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895738777919055976820291 4343608166878583965230437)
                  ·
                    refine ⟨814426531289734493480707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343608166878583965230437 814426531289734493480707)
                    ·
                      rfl

theorem cell23_4758270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4758270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758270 prefixEnd_4758270 := by exact prefixLift 4758270
  have htrace : WordTrace (prefixWord ++ tailWord_4758270) baseStart_4758270 baseEnd_4758270 := by
    simpa [prefixWord, tailWord_4758270, baseEnd_4758270] using wordTrace_append hprefix tailTrace_4758270
  have hstable : (prefixWord ++ tailWord_4758270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758270).length < 2 ^ (prefixWord ++ tailWord_4758270).sum := by decide
  have hdescent : baseEnd_4758270 < baseStart_4758270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758272 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_4758272 : Nat := 118140960795 + 4758272 * 2 ^ 59
def prefixEnd_4758272 : Nat := 4983230072969 + 3 ^ 40 * 4758272 * 2
def baseEnd_4758272 : Nat := 2443280620830512472617111

theorem tailTrace_4758272 : CollatzResearch.WordTrace tailWord_4758272 prefixEnd_4758272 2443280620830512472617111 := by
  unfold tailWord_4758272
  simp only [CollatzResearch.WordTrace]
  refine ⟨86774218708800333502242535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115698958278400444669656713 86774218708800333502242535)
  ·
    refine ⟨130161328063200500253363803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86774218708800333502242535 130161328063200500253363803)
    ·
      refine ⟨195241992094800750380045705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130161328063200500253363803 195241992094800750380045705)
      ·
        refine ⟨146431494071100562785034279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195241992094800750380045705 146431494071100562785034279)
        ·
          refine ⟨219647241106650844177551419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146431494071100562785034279 219647241106650844177551419)
          ·
            refine ⟨329470861659976266266327129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219647241106650844177551419 329470861659976266266327129)
            ·
              refine ⟨247103146244982199699745347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329470861659976266266327129 247103146244982199699745347)
              ·
                refine ⟨370654719367473299549618021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247103146244982199699745347 370654719367473299549618021)
                ·
                  refine ⟨69497759881401243665553379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370654719367473299549618021 69497759881401243665553379)
                  ·
                    refine ⟨104246639822101865498330069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69497759881401243665553379 104246639822101865498330069)
                    ·
                      refine ⟨2443280620830512472617111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104246639822101865498330069 2443280620830512472617111)
                      ·
                        rfl

theorem cell23_4758272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_4758272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758272 prefixEnd_4758272 := by exact prefixLift 4758272
  have htrace : WordTrace (prefixWord ++ tailWord_4758272) baseStart_4758272 baseEnd_4758272 := by
    simpa [prefixWord, tailWord_4758272, baseEnd_4758272] using wordTrace_append hprefix tailTrace_4758272
  have hstable : (prefixWord ++ tailWord_4758272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758272).length < 2 ^ (prefixWord ++ tailWord_4758272).sum := by decide
  have hdescent : baseEnd_4758272 < baseStart_4758272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758286 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4758286 : Nat := 118140960795 + 4758286 * 2 ^ 59
def prefixEnd_4758286 : Nat := 4983230072969 + 3 ^ 40 * 4758286 * 2
def baseEnd_4758286 : Nat := 2443287809559675417842047

theorem tailTrace_4758286 : CollatzResearch.WordTrace tailWord_4758286 prefixEnd_4758286 2443287809559675417842047 := by
  unfold tailWord_4758286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693618504943743424436839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115699298693033298263663141 21693618504943743424436839)
  ·
    refine ⟨32540427757415615136655259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21693618504943743424436839 32540427757415615136655259)
    ·
      refine ⟨48810641636123422704982889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32540427757415615136655259 48810641636123422704982889)
      ·
        refine ⟨36607981227092567028737167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48810641636123422704982889 36607981227092567028737167)
        ·
          refine ⟨54911971840638850543105751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36607981227092567028737167 54911971840638850543105751)
          ·
            refine ⟨82367957760958275814658627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54911971840638850543105751 82367957760958275814658627)
            ·
              refine ⟨123551936641437413721987941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82367957760958275814658627 123551936641437413721987941)
              ·
                refine ⟨23165988120269515072872739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123551936641437413721987941 23165988120269515072872739)
                ·
                  refine ⟨34748982180404272609309109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23165988120269515072872739 34748982180404272609309109)
                  ·
                    refine ⟨3257717079412900557122729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34748982180404272609309109 3257717079412900557122729)
                    ·
                      refine ⟨2443287809559675417842047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257717079412900557122729 2443287809559675417842047)
                      ·
                        rfl

theorem cell23_4758286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4758286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758286 prefixEnd_4758286 := by exact prefixLift 4758286
  have htrace : WordTrace (prefixWord ++ tailWord_4758286) baseStart_4758286 baseEnd_4758286 := by
    simpa [prefixWord, tailWord_4758286, baseEnd_4758286] using wordTrace_append hprefix tailTrace_4758286
  have hstable : (prefixWord ++ tailWord_4758286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758286).length < 2 ^ (prefixWord ++ tailWord_4758286).sum := by decide
  have hdescent : baseEnd_4758286 < baseStart_4758286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758303 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 2, 3, 2]
def baseStart_4758303 : Nat := 118140960795 + 4758303 * 2 ^ 59
def prefixEnd_4758303 : Nat := 4983230072969 + 3 ^ 40 * 4758303 * 2
def baseEnd_4758303 : Nat := 2443296538730801851329469

theorem tailTrace_4758303 : CollatzResearch.WordTrace tailWord_4758303 prefixEnd_4758303 2443296538730801851329469 := by
  unfold tailWord_4758303
  simp only [CollatzResearch.WordTrace]
  refine ⟨173549568080488359298863563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115699712053658906199242375 173549568080488359298863563)
  ·
    refine ⟨260324352120732538948295345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173549568080488359298863563 260324352120732538948295345)
    ·
      refine ⟨195243264090549404211221509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260324352120732538948295345 195243264090549404211221509)
      ·
        refine ⟨36608112016978013289604033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195243264090549404211221509 36608112016978013289604033)
        ·
          refine ⟨27456084012733509967203025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36608112016978013289604033 27456084012733509967203025)
          ·
            refine ⟨20592063009550132475402269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27456084012733509967203025 20592063009550132475402269)
            ·
              refine ⟨7722023628581299678275851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20592063009550132475402269 7722023628581299678275851)
              ·
                refine ⟨11583035442871949517413777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7722023628581299678275851 11583035442871949517413777)
                ·
                  refine ⟨8687276582153962138060333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11583035442871949517413777 8687276582153962138060333)
                  ·
                    refine ⟨3257728718307735801772625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8687276582153962138060333 3257728718307735801772625)
                    ·
                      refine ⟨2443296538730801851329469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257728718307735801772625 2443296538730801851329469)
                      ·
                        rfl

theorem cell23_4758303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_4758303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758303 prefixEnd_4758303 := by exact prefixLift 4758303
  have htrace : WordTrace (prefixWord ++ tailWord_4758303) baseStart_4758303 baseEnd_4758303 := by
    simpa [prefixWord, tailWord_4758303, baseEnd_4758303] using wordTrace_append hprefix tailTrace_4758303
  have hstable : (prefixWord ++ tailWord_4758303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758303).length < 2 ^ (prefixWord ++ tailWord_4758303).sum := by decide
  have hdescent : baseEnd_4758303 < baseStart_4758303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758309 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_4758309 : Nat := 118140960795 + 4758309 * 2 ^ 59
def prefixEnd_4758309 : Nat := 4983230072969 + 3 ^ 40 * 4758309 * 2
def baseEnd_4758309 : Nat := 814433206538242942618147

theorem tailTrace_4758309 : CollatzResearch.WordTrace tailWord_4758309 prefixEnd_4758309 814433206538242942618147 := by
  unfold tailWord_4758309
  simp only [CollatzResearch.WordTrace]
  refine ⟨173549786918466622323581981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115699857945644414882387987 173549786918466622323581981)
  ·
    refine ⟨65081170094424983371343243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173549786918466622323581981 65081170094424983371343243)
    ·
      refine ⟨97621755141637475057014865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65081170094424983371343243 97621755141637475057014865)
      ·
        refine ⟨73216316356228106292761149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97621755141637475057014865 73216316356228106292761149)
        ·
          refine ⟨27456118633585539859785431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73216316356228106292761149 27456118633585539859785431)
          ·
            refine ⟨41184177950378309789678147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27456118633585539859785431 41184177950378309789678147)
            ·
              refine ⟨61776266925567464684517221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41184177950378309789678147 61776266925567464684517221)
              ·
                refine ⟨11583050048543899628346979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61776266925567464684517221 11583050048543899628346979)
                ·
                  refine ⟨17374575072815849442520469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11583050048543899628346979 17374575072815849442520469)
                  ·
                    refine ⟨814433206538242942618147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17374575072815849442520469 814433206538242942618147)
                    ·
                      rfl

theorem cell23_4758309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_4758309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758309 prefixEnd_4758309 := by exact prefixLift 4758309
  have htrace : WordTrace (prefixWord ++ tailWord_4758309) baseStart_4758309 baseEnd_4758309 := by
    simpa [prefixWord, tailWord_4758309, baseEnd_4758309] using wordTrace_append hprefix tailTrace_4758309
  have hstable : (prefixWord ++ tailWord_4758309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758309).length < 2 ^ (prefixWord ++ tailWord_4758309).sum := by decide
  have hdescent : baseEnd_4758309 < baseStart_4758309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758316 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_4758316 : Nat := 118140960795 + 4758316 * 2 ^ 59
def prefixEnd_4758316 : Nat := 4983230072969 + 3 ^ 40 * 4758316 * 2
def baseEnd_4758316 : Nat := 2443303213979310300466909

theorem tailTrace_4758316 : CollatzResearch.WordTrace tailWord_4758316 prefixEnd_4758316 2443303213979310300466909 := by
  unfold tailWord_4758316
  simp only [CollatzResearch.WordTrace]
  refine ⟨86775021114720631259543401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115700028152960841679391201 86775021114720631259543401)
  ·
    refine ⟨65081265836040473444657551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86775021114720631259543401 65081265836040473444657551)
    ·
      refine ⟨97621898754060710166986327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65081265836040473444657551 97621898754060710166986327)
      ·
        refine ⟨146432848131091065250479491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97621898754060710166986327 146432848131091065250479491)
        ·
          refine ⟨219649272196636597875719237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146432848131091065250479491 219649272196636597875719237)
          ·
            refine ⟨41184238536869362101697357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219649272196636597875719237 41184238536869362101697357)
            ·
              refine ⟨15444089451326010788136509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41184238536869362101697357 15444089451326010788136509)
              ·
                refine ⟨5791533544247254045551191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15444089451326010788136509 5791533544247254045551191)
                ·
                  refine ⟨8687300316370881068326787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791533544247254045551191 8687300316370881068326787)
                  ·
                    refine ⟨13030950474556321602490181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8687300316370881068326787 13030950474556321602490181)
                    ·
                      refine ⟨2443303213979310300466909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13030950474556321602490181 2443303213979310300466909)
                      ·
                        rfl

theorem cell23_4758316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_4758316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758316 prefixEnd_4758316 := by exact prefixLift 4758316
  have htrace : WordTrace (prefixWord ++ tailWord_4758316) baseStart_4758316 baseEnd_4758316 := by
    simpa [prefixWord, tailWord_4758316, baseEnd_4758316] using wordTrace_append hprefix tailTrace_4758316
  have hstable : (prefixWord ++ tailWord_4758316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758316).length < 2 ^ (prefixWord ++ tailWord_4758316).sum := by decide
  have hdescent : baseEnd_4758316 < baseStart_4758316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758317 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 6]
def baseStart_4758317 : Nat := 118140960795 + 4758317 * 2 ^ 59
def prefixEnd_4758317 : Nat := 4983230072969 + 3 ^ 40 * 4758317 * 2
def baseEnd_4758317 : Nat := 271478191939996088506045

theorem tailTrace_4758317 : CollatzResearch.WordTrace tailWord_4758317 prefixEnd_4758317 271478191939996088506045 := by
  unfold tailWord_4758317
  simp only [CollatzResearch.WordTrace]
  refine ⟨173550078702437639689873205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115700052468291759793248803 173550078702437639689873205)
  ·
    refine ⟨16270319878353528720925613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173550078702437639689873205 16270319878353528720925613)
    ·
      refine ⟨6101369954382573270347105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16270319878353528720925613 6101369954382573270347105)
      ·
        refine ⟨4576027465786929952760329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6101369954382573270347105 4576027465786929952760329)
        ·
          refine ⟨3432020599340197464570247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4576027465786929952760329 3432020599340197464570247)
          ·
            refine ⟨5148030899010296196855371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432020599340197464570247 5148030899010296196855371)
            ·
              refine ⟨7722046348515444295283057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148030899010296196855371 7722046348515444295283057)
              ·
                refine ⟨5791534761386583221462293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7722046348515444295283057 5791534761386583221462293)
                ·
                  refine ⟨271478191939996088506045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5791534761386583221462293 271478191939996088506045)
                  ·
                    rfl

theorem cell23_4758317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_4758317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758317 prefixEnd_4758317 := by exact prefixLift 4758317
  have htrace : WordTrace (prefixWord ++ tailWord_4758317) baseStart_4758317 baseEnd_4758317 := by
    simpa [prefixWord, tailWord_4758317, baseEnd_4758317] using wordTrace_append hprefix tailTrace_4758317
  have hstable : (prefixWord ++ tailWord_4758317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758317).length < 2 ^ (prefixWord ++ tailWord_4758317).sum := by decide
  have hdescent : baseEnd_4758317 < baseStart_4758317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758356 : List Nat := [2, 4, 1, 1, 4, 1, 1, 9]
def baseStart_4758356 : Nat := 118140960795 + 4758356 * 2 ^ 59
def prefixEnd_4758356 : Nat := 4983230072969 + 3 ^ 40 * 4758356 * 2
def baseEnd_4758356 : Nat := 90493472340944079406175

theorem tailTrace_4758356 : CollatzResearch.WordTrace tailWord_4758356 prefixEnd_4758356 90493472340944079406175 := by
  unfold tailWord_4758356
  simp only [CollatzResearch.WordTrace]
  refine ⟨86775750574648174675271461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115701000766197566233695281 86775750574648174675271461)
  ·
    refine ⟨16270453232746532751613399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86775750574648174675271461 16270453232746532751613399)
    ·
      refine ⟨24405679849119799127420099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16270453232746532751613399 24405679849119799127420099)
      ·
        refine ⟨36608519773679698691130149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24405679849119799127420099 36608519773679698691130149)
        ·
          refine ⟨6864097457564943504586903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36608519773679698691130149 6864097457564943504586903)
          ·
            refine ⟨10296146186347415256880355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864097457564943504586903 10296146186347415256880355)
            ·
              refine ⟨15444219279521122885320533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296146186347415256880355 15444219279521122885320533)
              ·
                refine ⟨90493472340944079406175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15444219279521122885320533 90493472340944079406175)
                ·
                  rfl

theorem cell23_4758356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 9].length) (baseStart_4758356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758356 prefixEnd_4758356 := by exact prefixLift 4758356
  have htrace : WordTrace (prefixWord ++ tailWord_4758356) baseStart_4758356 baseEnd_4758356 := by
    simpa [prefixWord, tailWord_4758356, baseEnd_4758356] using wordTrace_append hprefix tailTrace_4758356
  have hstable : (prefixWord ++ tailWord_4758356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758356).length < 2 ^ (prefixWord ++ tailWord_4758356).sum := by decide
  have hdescent : baseEnd_4758356 < baseStart_4758356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758399 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 6]
def baseStart_4758399 : Nat := 118140960795 + 4758399 * 2 ^ 59
def prefixEnd_4758399 : Nat := 4983230072969 + 3 ^ 40 * 4758399 * 2
def baseEnd_4758399 : Nat := 814448610957877825243009

theorem tailTrace_4758399 : CollatzResearch.WordTrace tailWord_4758399 prefixEnd_4758399 814448610957877825243009 := by
  unfold tailWord_4758399
  simp only [CollatzResearch.WordTrace]
  refine ⟨173553069488140567694358251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115702046325427045129572167 173553069488140567694358251)
  ·
    refine ⟨260329604232210851541537377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173553069488140567694358251 260329604232210851541537377)
    ·
      refine ⟨195247203174158138656153033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260329604232210851541537377 195247203174158138656153033)
      ·
        refine ⟨146435402380618603992114775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195247203174158138656153033 146435402380618603992114775)
        ·
          refine ⟨219653103570927905988172163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146435402380618603992114775 219653103570927905988172163)
          ·
            refine ⟨329479655356391858982258245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219653103570927905988172163 329479655356391858982258245)
            ·
              refine ⟨61777435379323473559173421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329479655356391858982258245 61777435379323473559173421)
              ·
                refine ⟨23166538267246302584690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61777435379323473559173421 23166538267246302584690033)
                ·
                  refine ⟨17374903700434726938517525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23166538267246302584690033 17374903700434726938517525)
                  ·
                    refine ⟨814448610957877825243009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17374903700434726938517525 814448610957877825243009)
                    ·
                      rfl

theorem cell23_4758399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_4758399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758399 prefixEnd_4758399 := by exact prefixLift 4758399
  have htrace : WordTrace (prefixWord ++ tailWord_4758399) baseStart_4758399 baseEnd_4758399 := by
    simpa [prefixWord, tailWord_4758399, baseEnd_4758399] using wordTrace_append hprefix tailTrace_4758399
  have hstable : (prefixWord ++ tailWord_4758399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758399).length < 2 ^ (prefixWord ++ tailWord_4758399).sum := by decide
  have hdescent : baseEnd_4758399 < baseStart_4758399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758410 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4758410 : Nat := 118140960795 + 4758410 * 2 ^ 59
def prefixEnd_4758410 : Nat := 4983230072969 + 3 ^ 40 * 4758410 * 2
def baseEnd_4758410 : Nat := 2443351481160832932691477

theorem tailTrace_4758410 : CollatzResearch.WordTrace tailWord_4758410 prefixEnd_4758410 2443351481160832932691477 := by
  unfold tailWord_4758410
  simp only [CollatzResearch.WordTrace]
  refine ⟨43388367672775179143252171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115702313794067144382005789 43388367672775179143252171)
  ·
    refine ⟨65082551509162768714878257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43388367672775179143252171 65082551509162768714878257)
    ·
      refine ⟨48811913631872076536158693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65082551509162768714878257 48811913631872076536158693)
      ·
        refine ⟨9152233805976014350529755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48811913631872076536158693 9152233805976014350529755)
        ·
          refine ⟨13728350708964021525794633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9152233805976014350529755 13728350708964021525794633)
          ·
            refine ⟨10296263031723016144345975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13728350708964021525794633 10296263031723016144345975)
            ·
              refine ⟨15444394547584524216518963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296263031723016144345975 15444394547584524216518963)
              ·
                refine ⟨23166591821376786324778445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15444394547584524216518963 23166591821376786324778445)
                ·
                  refine ⟨8687471933016294871791917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23166591821376786324778445 8687471933016294871791917)
                  ·
                    refine ⟨3257801974881110576921969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8687471933016294871791917 3257801974881110576921969)
                    ·
                      refine ⟨2443351481160832932691477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257801974881110576921969 2443351481160832932691477)
                      ·
                        rfl

theorem cell23_4758410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4758410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758410 prefixEnd_4758410 := by exact prefixLift 4758410
  have htrace : WordTrace (prefixWord ++ tailWord_4758410) baseStart_4758410 baseEnd_4758410 := by
    simpa [prefixWord, tailWord_4758410, baseEnd_4758410] using wordTrace_append hprefix tailTrace_4758410
  have hstable : (prefixWord ++ tailWord_4758410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758410).length < 2 ^ (prefixWord ++ tailWord_4758410).sum := by decide
  have hdescent : baseEnd_4758410 < baseStart_4758410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_4758419 : Nat := 118140960795 + 4758419 * 2 ^ 59
def prefixEnd_4758419 : Nat := 4983230072969 + 3 ^ 40 * 4758419 * 2
def baseEnd_4758419 : Nat := 2443356102486723397478935

theorem tailTrace_4758419 : CollatzResearch.WordTrace tailWord_4758419 prefixEnd_4758419 2443356102486723397478935 := by
  unfold tailWord_4758419
  simp only [CollatzResearch.WordTrace]
  refine ⟨173553798948068111110086311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115702532632045407406724207 173553798948068111110086311)
  ·
    refine ⟨260330698422102166665129467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173553798948068111110086311 260330698422102166665129467)
    ·
      refine ⟨390496047633153249997694201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260330698422102166665129467 390496047633153249997694201)
      ·
        refine ⟨292872035724864937498270651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390496047633153249997694201 292872035724864937498270651)
        ·
          refine ⟨439308053587297406247405977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292872035724864937498270651 439308053587297406247405977)
          ·
            refine ⟨329481040190473054685554483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439308053587297406247405977 329481040190473054685554483)
            ·
              refine ⟨494221560285709582028331725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329481040190473054685554483 494221560285709582028331725)
              ·
                refine ⟨185333085107141093260624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494221560285709582028331725 185333085107141093260624397)
                ·
                  refine ⟨69499906915177909972734149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185333085107141093260624397 69499906915177909972734149)
                  ·
                    refine ⟨13031232546595858119887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69499906915177909972734149 13031232546595858119887653)
                    ·
                      refine ⟨2443356102486723397478935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13031232546595858119887653 2443356102486723397478935)
                      ·
                        rfl

theorem cell23_4758419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_4758419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758419 prefixEnd_4758419 := by exact prefixLift 4758419
  have htrace : WordTrace (prefixWord ++ tailWord_4758419) baseStart_4758419 baseEnd_4758419 := by
    simpa [prefixWord, tailWord_4758419, baseEnd_4758419] using wordTrace_append hprefix tailTrace_4758419
  have hstable : (prefixWord ++ tailWord_4758419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758419).length < 2 ^ (prefixWord ++ tailWord_4758419).sum := by decide
  have hdescent : baseEnd_4758419 < baseStart_4758419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758423 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_4758423 : Nat := 118140960795 + 4758423 * 2 ^ 59
def prefixEnd_4758423 : Nat := 4983230072969 + 3 ^ 40 * 4758423 * 2
def baseEnd_4758423 : Nat := 2443358156409341381828917

theorem tailTrace_4758423 : CollatzResearch.WordTrace tailWord_4758423 prefixEnd_4758423 2443358156409341381828917 := by
  unfold tailWord_4758423
  simp only [CollatzResearch.WordTrace]
  refine ⟨173553944840053619793231923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115702629893369079862154615 173553944840053619793231923)
  ·
    refine ⟨260330917260080429689847885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173553944840053619793231923 260330917260080429689847885)
    ·
      refine ⟨97624093972530161133692957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260330917260080429689847885 97624093972530161133692957)
      ·
        refine ⟨36609035239698810425134859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97624093972530161133692957 36609035239698810425134859)
        ·
          refine ⟨54913552859548215637702289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36609035239698810425134859 54913552859548215637702289)
          ·
            refine ⟨41185164644661161728276717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54913552859548215637702289 41185164644661161728276717)
            ·
              refine ⟨15444436741747935648103769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41185164644661161728276717 15444436741747935648103769)
              ·
                refine ⟨11583327556310951736077827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15444436741747935648103769 11583327556310951736077827)
                ·
                  refine ⟨17374991334466427604116741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11583327556310951736077827 17374991334466427604116741)
                  ·
                    refine ⟨3257810875212455175771889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17374991334466427604116741 3257810875212455175771889)
                    ·
                      refine ⟨2443358156409341381828917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257810875212455175771889 2443358156409341381828917)
                      ·
                        rfl

theorem cell23_4758423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_4758423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758423 prefixEnd_4758423 := by exact prefixLift 4758423
  have htrace : WordTrace (prefixWord ++ tailWord_4758423) baseStart_4758423 baseEnd_4758423 := by
    simpa [prefixWord, tailWord_4758423, baseEnd_4758423] using wordTrace_append hprefix tailTrace_4758423
  have hstable : (prefixWord ++ tailWord_4758423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758423).length < 2 ^ (prefixWord ++ tailWord_4758423).sum := by decide
  have hdescent : baseEnd_4758423 < baseStart_4758423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758436 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_4758436 : Nat := 118140960795 + 4758436 * 2 ^ 59
def prefixEnd_4758436 : Nat := 4983230072969 + 3 ^ 40 * 4758436 * 2
def baseEnd_4758436 : Nat := 2443364831657849830966357

theorem tailTrace_4758436 : CollatzResearch.WordTrace tailWord_4758436 prefixEnd_4758436 2443364831657849830966357 := by
  unfold tailWord_4758436
  simp only [CollatzResearch.WordTrace]
  refine ⟨86777209494503261506727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115702945992671015342303441 86777209494503261506727581)
  ·
    refine ⟨32541453560438723065022843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86777209494503261506727581 32541453560438723065022843)
    ·
      refine ⟨48812180340658084597534265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32541453560438723065022843 48812180340658084597534265)
      ·
        refine ⟨36609135255493563448150699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48812180340658084597534265 36609135255493563448150699)
        ·
          refine ⟨54913702883240345172226049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36609135255493563448150699 54913702883240345172226049)
          ·
            refine ⟨41185277162430258879169537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54913702883240345172226049 41185277162430258879169537)
            ·
              refine ⟨30888957871822694159377153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41185277162430258879169537 30888957871822694159377153)
              ·
                refine ⟨23166718403867020619532865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30888957871822694159377153 23166718403867020619532865)
                ·
                  refine ⟨17375038802900265464649649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23166718403867020619532865 17375038802900265464649649)
                  ·
                    refine ⟨13031279102175199098487237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17375038802900265464649649 13031279102175199098487237)
                    ·
                      refine ⟨2443364831657849830966357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13031279102175199098487237 2443364831657849830966357)
                      ·
                        rfl

theorem cell23_4758436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_4758436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758436 prefixEnd_4758436 := by exact prefixLift 4758436
  have htrace : WordTrace (prefixWord ++ tailWord_4758436) baseStart_4758436 baseEnd_4758436 := by
    simpa [prefixWord, tailWord_4758436, baseEnd_4758436] using wordTrace_append hprefix tailTrace_4758436
  have hstable : (prefixWord ++ tailWord_4758436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758436).length < 2 ^ (prefixWord ++ tailWord_4758436).sum := by decide
  have hdescent : baseEnd_4758436 < baseStart_4758436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758456 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_4758456 : Nat := 118140960795 + 4758456 * 2 ^ 59
def prefixEnd_4758456 : Nat := 4983230072969 + 3 ^ 40 * 4758456 * 2
def baseEnd_4758456 : Nat := 2443375101270939752716265

theorem tailTrace_4758456 : CollatzResearch.WordTrace tailWord_4758456 prefixEnd_4758456 2443375101270939752716265 := by
  unfold tailWord_4758456
  simp only [CollatzResearch.WordTrace]
  refine ⟨86777574224467033214591611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115703432299289377619455481 86777574224467033214591611)
  ·
    refine ⟨130166361336700549821887417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86777574224467033214591611 130166361336700549821887417)
    ·
      refine ⟨97624771002525412366415563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130166361336700549821887417 97624771002525412366415563)
      ·
        refine ⟨146437156503788118549623345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97624771002525412366415563 146437156503788118549623345)
        ·
          refine ⟨109827867377841088912217509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146437156503788118549623345 109827867377841088912217509)
          ·
            refine ⟨20592725133345204171040783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109827867377841088912217509 20592725133345204171040783)
            ·
              refine ⟨30889087700017806256561175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20592725133345204171040783 30889087700017806256561175)
              ·
                refine ⟨46333631550026709384841763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30889087700017806256561175 46333631550026709384841763)
                ·
                  refine ⟨69500447325040064077262645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46333631550026709384841763 69500447325040064077262645)
                  ·
                    refine ⟨6515666936722506007243373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69500447325040064077262645 6515666936722506007243373)
                    ·
                      refine ⟨2443375101270939752716265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6515666936722506007243373 2443375101270939752716265)
                      ·
                        rfl

theorem cell23_4758456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_4758456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758456 prefixEnd_4758456 := by exact prefixLift 4758456
  have htrace : WordTrace (prefixWord ++ tailWord_4758456) baseStart_4758456 baseEnd_4758456 := by
    simpa [prefixWord, tailWord_4758456, baseEnd_4758456] using wordTrace_append hprefix tailTrace_4758456
  have hstable : (prefixWord ++ tailWord_4758456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758456).length < 2 ^ (prefixWord ++ tailWord_4758456).sum := by decide
  have hdescent : baseEnd_4758456 < baseStart_4758456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758476 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_4758476 : Nat := 118140960795 + 4758476 * 2 ^ 59
def prefixEnd_4758476 : Nat := 4983230072969 + 3 ^ 40 * 4758476 * 2
def baseEnd_4758476 : Nat := 814461790294676558155391

theorem tailTrace_4758476 : CollatzResearch.WordTrace tailWord_4758476 prefixEnd_4758476 814461790294676558155391 := by
  unfold tailWord_4758476
  simp only [CollatzResearch.WordTrace]
  refine ⟨86777938954430804922455641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115703918605907739896607521 86777938954430804922455641)
  ·
    refine ⟨65083454215823103691841731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86777938954430804922455641 65083454215823103691841731)
    ·
      refine ⟨97625181323734655537762597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65083454215823103691841731 97625181323734655537762597)
      ·
        refine ⟨18304721498200247913330487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97625181323734655537762597 18304721498200247913330487)
        ·
          refine ⟨27457082247300371869995731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18304721498200247913330487 27457082247300371869995731)
          ·
            refine ⟨41185623370950557804993597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27457082247300371869995731 41185623370950557804993597)
            ·
              refine ⟨15444608764106459176872599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41185623370950557804993597 15444608764106459176872599)
              ·
                refine ⟨23166913146159688765308899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15444608764106459176872599 23166913146159688765308899)
                ·
                  refine ⟨34750369719239533147963349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23166913146159688765308899 34750369719239533147963349)
                  ·
                    refine ⟨814461790294676558155391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34750369719239533147963349 814461790294676558155391)
                    ·
                      rfl

theorem cell23_4758476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_4758476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758476 prefixEnd_4758476 := by exact prefixLift 4758476
  have htrace : WordTrace (prefixWord ++ tailWord_4758476) baseStart_4758476 baseEnd_4758476 := by
    simpa [prefixWord, tailWord_4758476, baseEnd_4758476] using wordTrace_append hprefix tailTrace_4758476
  have hstable : (prefixWord ++ tailWord_4758476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758476).length < 2 ^ (prefixWord ++ tailWord_4758476).sum := by decide
  have hdescent : baseEnd_4758476 < baseStart_4758476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758533 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_4758533 : Nat := 118140960795 + 4758533 * 2 ^ 59
def prefixEnd_4758533 : Nat := 4983230072969 + 3 ^ 40 * 4758533 * 2
def baseEnd_4758533 : Nat := 2443414639281335951453411

theorem tailTrace_4758533 : CollatzResearch.WordTrace tailWord_4758533 prefixEnd_4758533 2443414639281335951453411 := by
  unfold tailWord_4758533
  simp only [CollatzResearch.WordTrace]
  refine ⟨173557956869655108579736253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115705304579770072386490835 173557956869655108579736253)
  ·
    refine ⟨65084233826120665717401095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173557956869655108579736253 65084233826120665717401095)
    ·
      refine ⟨97626350739180998576101643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65084233826120665717401095 97626350739180998576101643)
      ·
        refine ⟨146439526108771497864152465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97626350739180998576101643 146439526108771497864152465)
        ·
          refine ⟨109829644581578623398114349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146439526108771497864152465 109829644581578623398114349)
          ·
            refine ⟨41186116718091983774292881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109829644581578623398114349 41186116718091983774292881)
            ·
              refine ⟨30889587538568987830719661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41186116718091983774292881 30889587538568987830719661)
              ·
                refine ⟨11583595326963370436519873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30889587538568987830719661 11583595326963370436519873)
                ·
                  refine ⟨8687696495222527827389905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11583595326963370436519873 8687696495222527827389905)
                  ·
                    refine ⟨6515772371416895870542429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8687696495222527827389905 6515772371416895870542429)
                    ·
                      refine ⟨2443414639281335951453411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6515772371416895870542429 2443414639281335951453411)
                      ·
                        rfl

theorem cell23_4758533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_4758533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758533 prefixEnd_4758533 := by exact prefixLift 4758533
  have htrace : WordTrace (prefixWord ++ tailWord_4758533) baseStart_4758533 baseEnd_4758533 := by
    simpa [prefixWord, tailWord_4758533, baseEnd_4758533] using wordTrace_append hprefix tailTrace_4758533
  have hstable : (prefixWord ++ tailWord_4758533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758533).length < 2 ^ (prefixWord ++ tailWord_4758533).sum := by decide
  have hdescent : baseEnd_4758533 < baseStart_4758533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758536 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 8]
def baseStart_4758536 : Nat := 118140960795 + 4758536 * 2 ^ 59
def prefixEnd_4758536 : Nat := 4983230072969 + 3 ^ 40 * 4758536 * 2
def baseEnd_4758536 : Nat := 271490686635922159968433

theorem tailTrace_4758536 : CollatzResearch.WordTrace tailWord_4758536 prefixEnd_4758536 271490686635922159968433 := by
  unfold tailWord_4758536
  simp only [CollatzResearch.WordTrace]
  refine ⟨86779033144322120046047731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115705377525762826728063641 86779033144322120046047731)
  ·
    refine ⟨130168549716483180069071597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86779033144322120046047731 130168549716483180069071597)
    ·
      refine ⟨48813206143681192525901849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130168549716483180069071597 48813206143681192525901849)
      ·
        refine ⟨36609904607760894394426387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48813206143681192525901849 36609904607760894394426387)
        ·
          refine ⟨54914856911641341591639581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36609904607760894394426387 54914856911641341591639581)
          ·
            refine ⟨20593071341865503096864843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54914856911641341591639581 20593071341865503096864843)
            ·
              refine ⟨30889607012798254645297265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20593071341865503096864843 30889607012798254645297265)
              ·
                refine ⟨23167205259598690983972949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30889607012798254645297265 23167205259598690983972949)
                ·
                  refine ⟨271490686635922159968433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23167205259598690983972949 271490686635922159968433)
                  ·
                    rfl

theorem cell23_4758536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_4758536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758536 prefixEnd_4758536 := by exact prefixLift 4758536
  have htrace : WordTrace (prefixWord ++ tailWord_4758536) baseStart_4758536 baseEnd_4758536 := by
    simpa [prefixWord, tailWord_4758536, baseEnd_4758536] using wordTrace_append hprefix tailTrace_4758536
  have hstable : (prefixWord ++ tailWord_4758536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758536).length < 2 ^ (prefixWord ++ tailWord_4758536).sum := by decide
  have hdescent : baseEnd_4758536 < baseStart_4758536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758557 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4758557 : Nat := 118140960795 + 4758557 * 2 ^ 59
def prefixEnd_4758557 : Nat := 4983230072969 + 3 ^ 40 * 4758557 * 2
def baseEnd_4758557 : Nat := 814475654272347952517767

theorem tailTrace_4758557 : CollatzResearch.WordTrace tailWord_4758557 prefixEnd_4758557 814475654272347952517767 := by
  unfold tailWord_4758557
  simp only [CollatzResearch.WordTrace]
  refine ⟨173558832221568160678609925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115705888147712107119073283 173558832221568160678609925)
  ·
    refine ⟨32542281041544030127239361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173558832221568160678609925 32542281041544030127239361)
    ·
      refine ⟨24406710781158022595429521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32542281041544030127239361 24406710781158022595429521)
      ·
        refine ⟨18305033085868516946572141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24406710781158022595429521 18305033085868516946572141)
        ·
          refine ⟨6864387407200693854964553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18305033085868516946572141 6864387407200693854964553)
          ·
            refine ⟨5148290555400520391223415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6864387407200693854964553 5148290555400520391223415)
            ·
              refine ⟨7722435833100780586835123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148290555400520391223415 7722435833100780586835123)
              ·
                refine ⟨11583653749651170880252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7722435833100780586835123 11583653749651170880252685)
                ·
                  refine ⟨4343870156119189080094757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11583653749651170880252685 4343870156119189080094757)
                  ·
                    refine ⟨814475654272347952517767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343870156119189080094757 814475654272347952517767)
                    ·
                      rfl

theorem cell23_4758557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4758557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758557 prefixEnd_4758557 := by exact prefixLift 4758557
  have htrace : WordTrace (prefixWord ++ tailWord_4758557) baseStart_4758557 baseEnd_4758557 := by
    simpa [prefixWord, tailWord_4758557, baseEnd_4758557] using wordTrace_append hprefix tailTrace_4758557
  have hstable : (prefixWord ++ tailWord_4758557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758557).length < 2 ^ (prefixWord ++ tailWord_4758557).sum := by decide
  have hdescent : baseEnd_4758557 < baseStart_4758557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758570 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_4758570 : Nat := 118140960795 + 4758570 * 2 ^ 59
def prefixEnd_4758570 : Nat := 4983230072969 + 3 ^ 40 * 4758570 * 2
def baseEnd_4758570 : Nat := 271492626451728034076749

theorem tailTrace_4758570 : CollatzResearch.WordTrace tailWord_4758570 prefixEnd_4758570 271492626451728034076749 := by
  unfold tailWord_4758570
  simp only [CollatzResearch.WordTrace]
  refine ⟨43389826592630265974708291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115706204247014042599222109 43389826592630265974708291)
  ·
    refine ⟨65084739888945398962062437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43389826592630265974708291 65084739888945398962062437)
    ·
      refine ⟨12203388729177262305386707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65084739888945398962062437 12203388729177262305386707)
      ·
        refine ⟨18305083093765893458080061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203388729177262305386707 18305083093765893458080061)
        ·
          refine ⟨6864406160162210046780023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18305083093765893458080061 6864406160162210046780023)
          ·
            refine ⟨10296609240243315070170035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864406160162210046780023 10296609240243315070170035)
            ·
              refine ⟨15444913860364972605255053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296609240243315070170035 15444913860364972605255053)
              ·
                refine ⟨5791842697636864726970645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15444913860364972605255053 5791842697636864726970645)
                ·
                  refine ⟨271492626451728034076749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5791842697636864726970645 271492626451728034076749)
                  ·
                    rfl

theorem cell23_4758570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_4758570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758570 prefixEnd_4758570 := by exact prefixLift 4758570
  have htrace : WordTrace (prefixWord ++ tailWord_4758570) baseStart_4758570 baseEnd_4758570 := by
    simpa [prefixWord, tailWord_4758570, baseEnd_4758570] using wordTrace_append hprefix tailTrace_4758570
  have hstable : (prefixWord ++ tailWord_4758570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758570).length < 2 ^ (prefixWord ++ tailWord_4758570).sum := by decide
  have hdescent : baseEnd_4758570 < baseStart_4758570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758600 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_4758600 : Nat := 118140960795 + 4758600 * 2 ^ 59
def prefixEnd_4758600 : Nat := 4983230072969 + 3 ^ 40 * 4758600 * 2
def baseEnd_4758600 : Nat := 814483014161729063105201

theorem tailTrace_4758600 : CollatzResearch.WordTrace tailWord_4758600 prefixEnd_4758600 814483014161729063105201 := by
  unfold tailWord_4758600
  simp only [CollatzResearch.WordTrace]
  refine ⟨86780200280206189511212627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115706933706941586014950169 86780200280206189511212627)
  ·
    refine ⟨130170300420309284266818941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86780200280206189511212627 130170300420309284266818941)
    ·
      refine ⟨48813862657615981600057103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130170300420309284266818941 48813862657615981600057103)
      ·
        refine ⟨73220793986423972400085655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48813862657615981600057103 73220793986423972400085655)
        ·
          refine ⟨109831190979635958600128483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73220793986423972400085655 109831190979635958600128483)
          ·
            refine ⟨164746786469453937900192725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109831190979635958600128483 164746786469453937900192725)
            ·
              refine ⟨3861252807877826669535767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 164746786469453937900192725 3861252807877826669535767)
              ·
                refine ⟨5791879211816740004303651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861252807877826669535767 5791879211816740004303651)
                ·
                  refine ⟨8687818817725110006455477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791879211816740004303651 8687818817725110006455477)
                  ·
                    refine ⟨814483014161729063105201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8687818817725110006455477 814483014161729063105201)
                    ·
                      rfl

theorem cell23_4758600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_4758600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758600 prefixEnd_4758600 := by exact prefixLift 4758600
  have htrace : WordTrace (prefixWord ++ tailWord_4758600) baseStart_4758600 baseEnd_4758600 := by
    simpa [prefixWord, tailWord_4758600, baseEnd_4758600] using wordTrace_append hprefix tailTrace_4758600
  have hstable : (prefixWord ++ tailWord_4758600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758600).length < 2 ^ (prefixWord ++ tailWord_4758600).sum := by decide
  have hdescent : baseEnd_4758600 < baseStart_4758600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758623 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_4758623 : Nat := 118140960795 + 4758623 * 2 ^ 59
def prefixEnd_4758623 : Nat := 4983230072969 + 3 ^ 40 * 4758623 * 2
def baseEnd_4758623 : Nat := 2443460852540240599327997

theorem tailTrace_4758623 : CollatzResearch.WordTrace tailWord_4758623 prefixEnd_4758623 2443460852540240599327997 := by
  unfold tailWord_4758623
  simp only [CollatzResearch.WordTrace]
  refine ⟨173561239439329053950512523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115707492959552702633675015 173561239439329053950512523)
  ·
    refine ⟨260341859158993580925768785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173561239439329053950512523 260341859158993580925768785)
    ·
      refine ⟨195256394369245185694326589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260341859158993580925768785 195256394369245185694326589)
      ·
        refine ⟨73221147888466944635372471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195256394369245185694326589 73221147888466944635372471)
        ·
          refine ⟨109831721832700416953058707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73221147888466944635372471 109831721832700416953058707)
          ·
            refine ⟨164747582749050625429588061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109831721832700416953058707 164747582749050625429588061)
            ·
              refine ⟨61780343530893984536095523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164747582749050625429588061 61780343530893984536095523)
              ·
                refine ⟨92670515296340976804143285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61780343530893984536095523 92670515296340976804143285)
                ·
                  refine ⟨8687860809031966575388433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92670515296340976804143285 8687860809031966575388433)
                  ·
                    refine ⟨6515895606773974931541325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8687860809031966575388433 6515895606773974931541325)
                    ·
                      refine ⟨2443460852540240599327997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6515895606773974931541325 2443460852540240599327997)
                      ·
                        rfl

theorem cell23_4758623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_4758623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758623 prefixEnd_4758623 := by exact prefixLift 4758623
  have htrace : WordTrace (prefixWord ++ tailWord_4758623) baseStart_4758623 baseEnd_4758623 := by
    simpa [prefixWord, tailWord_4758623, baseEnd_4758623] using wordTrace_append hprefix tailTrace_4758623
  have hstable : (prefixWord ++ tailWord_4758623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758623).length < 2 ^ (prefixWord ++ tailWord_4758623).sum := by decide
  have hdescent : baseEnd_4758623 < baseStart_4758623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758633 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_4758633 : Nat := 118140960795 + 4758633 * 2 ^ 59
def prefixEnd_4758633 : Nat := 4983230072969 + 3 ^ 40 * 4758633 * 2
def baseEnd_4758633 : Nat := 2443465987346785560202951

theorem tailTrace_4758633 : CollatzResearch.WordTrace tailWord_4758633 prefixEnd_4758633 2443465987346785560202951 := by
  unfold tailWord_4758633
  simp only [CollatzResearch.WordTrace]
  refine ⟨173561604169292825658376553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115707736112861883772251035 173561604169292825658376553)
  ·
    refine ⟨130171203126969619243782415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173561604169292825658376553 130171203126969619243782415)
    ·
      refine ⟨195256804690454428865673623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130171203126969619243782415 195256804690454428865673623)
      ·
        refine ⟨292885207035681643298510435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195256804690454428865673623 292885207035681643298510435)
        ·
          refine ⟨439327810553522464947765653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292885207035681643298510435 439327810553522464947765653)
          ·
            refine ⟨20593491119696365544426515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 439327810553522464947765653 20593491119696365544426515)
            ·
              refine ⟨30890236679544548316639773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20593491119696365544426515 30890236679544548316639773)
              ·
                refine ⟨11583838754829205618739915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30890236679544548316639773 11583838754829205618739915)
                ·
                  refine ⟨17375758132243808428109873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11583838754829205618739915 17375758132243808428109873)
                  ·
                    refine ⟨13031818599182856321082405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17375758132243808428109873 13031818599182856321082405)
                    ·
                      refine ⟨2443465987346785560202951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13031818599182856321082405 2443465987346785560202951)
                      ·
                        rfl

theorem cell23_4758633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_4758633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758633 prefixEnd_4758633 := by exact prefixLift 4758633
  have htrace : WordTrace (prefixWord ++ tailWord_4758633) baseStart_4758633 baseEnd_4758633 := by
    simpa [prefixWord, tailWord_4758633, baseEnd_4758633] using wordTrace_append hprefix tailTrace_4758633
  have hstable : (prefixWord ++ tailWord_4758633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758633).length < 2 ^ (prefixWord ++ tailWord_4758633).sum := by decide
  have hdescent : baseEnd_4758633 < baseStart_4758633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758637 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_4758637 : Nat := 118140960795 + 4758637 * 2 ^ 59
def prefixEnd_4758637 : Nat := 4983230072969 + 3 ^ 40 * 4758637 * 2
def baseEnd_4758637 : Nat := 2443468041269403544552933

theorem tailTrace_4758637 : CollatzResearch.WordTrace tailWord_4758637 prefixEnd_4758637 2443468041269403544552933 := by
  unfold tailWord_4758637
  simp only [CollatzResearch.WordTrace]
  refine ⟨173561750061278334341522165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115707833374185556227681443 173561750061278334341522165)
  ·
    refine ⟨16271414068244843844517703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173561750061278334341522165 16271414068244843844517703)
    ·
      refine ⟨24407121102367265766776555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16271414068244843844517703 24407121102367265766776555)
      ·
        refine ⟨36610681653550898650164833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24407121102367265766776555 36610681653550898650164833)
        ·
          refine ⟨27458011240163173987623625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36610681653550898650164833 27458011240163173987623625)
          ·
            refine ⟨20593508430122380490717719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27458011240163173987623625 20593508430122380490717719)
            ·
              refine ⟨30890262645183570736076579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20593508430122380490717719 30890262645183570736076579)
              ·
                refine ⟨46335393967775356104114869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30890262645183570736076579 46335393967775356104114869)
                ·
                  refine ⟨4343943184478939634760769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46335393967775356104114869 4343943184478939634760769)
                  ·
                    refine ⟨3257957388359204726070577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4343943184478939634760769 3257957388359204726070577)
                    ·
                      refine ⟨2443468041269403544552933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3257957388359204726070577 2443468041269403544552933)
                      ·
                        rfl

theorem cell23_4758637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_4758637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758637 prefixEnd_4758637 := by exact prefixLift 4758637
  have htrace : WordTrace (prefixWord ++ tailWord_4758637) baseStart_4758637 baseEnd_4758637 := by
    simpa [prefixWord, tailWord_4758637, baseEnd_4758637] using wordTrace_append hprefix tailTrace_4758637
  have hstable : (prefixWord ++ tailWord_4758637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758637).length < 2 ^ (prefixWord ++ tailWord_4758637).sum := by decide
  have hdescent : baseEnd_4758637 < baseStart_4758637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758640 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_4758640 : Nat := 118140960795 + 4758640 * 2 ^ 59
def prefixEnd_4758640 : Nat := 4983230072969 + 3 ^ 40 * 4758640 * 2
def baseEnd_4758640 : Nat := 2443469581711367032815419

theorem tailTrace_4758640 : CollatzResearch.WordTrace tailWord_4758640 prefixEnd_4758640 2443469581711367032815419 := by
  unfold tailWord_4758640
  simp only [CollatzResearch.WordTrace]
  refine ⟨86780929740133732926940687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115707906320178310569254249 86780929740133732926940687)
  ·
    refine ⟨130171394610200599390411031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86780929740133732926940687 130171394610200599390411031)
    ·
      refine ⟨195257091915300899085616547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130171394610200599390411031 195257091915300899085616547)
      ·
        refine ⟨292885637872951348628424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195257091915300899085616547 292885637872951348628424821)
        ·
          refine ⟨27458028550589188933914827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292885637872951348628424821 27458028550589188933914827)
          ·
            refine ⟨41187042825883783400872241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27458028550589188933914827 41187042825883783400872241)
            ·
              refine ⟨30890282119412837550654181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41187042825883783400872241 30890282119412837550654181)
              ·
                refine ⟨5791927897389907040747659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30890282119412837550654181 5791927897389907040747659)
                ·
                  refine ⟨8687891846084860561121489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791927897389907040747659 8687891846084860561121489)
                  ·
                    refine ⟨6515918884563645420841117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8687891846084860561121489 6515918884563645420841117)
                    ·
                      refine ⟨2443469581711367032815419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6515918884563645420841117 2443469581711367032815419)
                      ·
                        rfl

theorem cell23_4758640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_4758640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758640 prefixEnd_4758640 := by exact prefixLift 4758640
  have htrace : WordTrace (prefixWord ++ tailWord_4758640) baseStart_4758640 baseEnd_4758640 := by
    simpa [prefixWord, tailWord_4758640, baseEnd_4758640] using wordTrace_append hprefix tailTrace_4758640
  have hstable : (prefixWord ++ tailWord_4758640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758640).length < 2 ^ (prefixWord ++ tailWord_4758640).sum := by decide
  have hdescent : baseEnd_4758640 < baseStart_4758640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758657 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4758657 : Nat := 118140960795 + 4758657 * 2 ^ 59
def prefixEnd_4758657 : Nat := 4983230072969 + 3 ^ 40 * 4758657 * 2
def baseEnd_4758657 : Nat := 2443478310882493466302841

theorem tailTrace_4758657 : CollatzResearch.WordTrace tailWord_4758657 prefixEnd_4758657 2443478310882493466302841 := by
  unfold tailWord_4758657
  simp only [CollatzResearch.WordTrace]
  refine ⟨173562479521205877757250225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115708319680803918504833483 173562479521205877757250225)
  ·
    refine ⟨130171859640904408317937669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173562479521205877757250225 130171859640904408317937669)
    ·
      refine ⟨24407223682669576559613313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130171859640904408317937669 24407223682669576559613313)
      ·
        refine ⟨18305417762002182419709985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24407223682669576559613313 18305417762002182419709985)
        ·
          refine ⟨13729063321501636814782489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18305417762002182419709985 13729063321501636814782489)
          ·
            refine ⟨10296797491126227611086867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13729063321501636814782489 10296797491126227611086867)
            ·
              refine ⟨15445196236689341416630301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296797491126227611086867 15445196236689341416630301)
              ·
                refine ⟨5791948588758503031236363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15445196236689341416630301 5791948588758503031236363)
                ·
                  refine ⟨8687922883137754546854545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791948588758503031236363 8687922883137754546854545)
                  ·
                    refine ⟨6515942162353315910140909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8687922883137754546854545 6515942162353315910140909)
                    ·
                      refine ⟨2443478310882493466302841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6515942162353315910140909 2443478310882493466302841)
                      ·
                        rfl

theorem cell23_4758657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4758657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758657 prefixEnd_4758657 := by exact prefixLift 4758657
  have htrace : WordTrace (prefixWord ++ tailWord_4758657) baseStart_4758657 baseEnd_4758657 := by
    simpa [prefixWord, tailWord_4758657, baseEnd_4758657] using wordTrace_append hprefix tailTrace_4758657
  have hstable : (prefixWord ++ tailWord_4758657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758657).length < 2 ^ (prefixWord ++ tailWord_4758657).sum := by decide
  have hdescent : baseEnd_4758657 < baseStart_4758657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758664 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_4758664 : Nat := 118140960795 + 4758664 * 2 ^ 59
def prefixEnd_4758664 : Nat := 4983230072969 + 3 ^ 40 * 4758664 * 2
def baseEnd_4758664 : Nat := 814493968415691646305103

theorem tailTrace_4758664 : CollatzResearch.WordTrace tailWord_4758664 prefixEnd_4758664 814493968415691646305103 := by
  unfold tailWord_4758664
  simp only [CollatzResearch.WordTrace]
  refine ⟨86781367416090258976377523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115708489888120345301836697 86781367416090258976377523)
  ·
    refine ⟨130172051124135388464566285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86781367416090258976377523 130172051124135388464566285)
    ·
      refine ⟨48814519171550770674212357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130172051124135388464566285 48814519171550770674212357)
      ·
        refine ⟨9152722344665769501414817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48814519171550770674212357 9152722344665769501414817)
        ·
          refine ⟨6864541758499327126061113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9152722344665769501414817 6864541758499327126061113)
          ·
            refine ⟨5148406318874495344545835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6864541758499327126061113 5148406318874495344545835)
            ·
              refine ⟨7722609478311743016818753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148406318874495344545835 7722609478311743016818753)
              ·
                refine ⟨5791957108733807262614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7722609478311743016818753 5791957108733807262614065)
                ·
                  refine ⟨4343967831550355446960549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791957108733807262614065 4343967831550355446960549)
                  ·
                    refine ⟨814493968415691646305103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343967831550355446960549 814493968415691646305103)
                    ·
                      rfl

theorem cell23_4758664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_4758664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758664 prefixEnd_4758664 := by exact prefixLift 4758664
  have htrace : WordTrace (prefixWord ++ tailWord_4758664) baseStart_4758664 baseEnd_4758664 := by
    simpa [prefixWord, tailWord_4758664, baseEnd_4758664] using wordTrace_append hprefix tailTrace_4758664
  have hstable : (prefixWord ++ tailWord_4758664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758664).length < 2 ^ (prefixWord ++ tailWord_4758664).sum := by decide
  have hdescent : baseEnd_4758664 < baseStart_4758664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758713 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4758713 : Nat := 118140960795 + 4758713 * 2 ^ 59
def prefixEnd_4758713 : Nat := 4983230072969 + 3 ^ 40 * 4758713 * 2
def baseEnd_4758713 : Nat := 2443507065799145247202583

theorem tailTrace_4758713 : CollatzResearch.WordTrace tailWord_4758713 prefixEnd_4758713 2443507065799145247202583 := by
  unfold tailWord_4758713
  simp only [CollatzResearch.WordTrace]
  refine ⟨173564522009002999321288793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115709681339335332880859195 173564522009002999321288793)
  ·
    refine ⟨130173391506752249490966595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173564522009002999321288793 130173391506752249490966595)
    ·
      refine ⟨195260087260128374236449893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130173391506752249490966595 195260087260128374236449893)
      ·
        refine ⟨36611266361274070169334355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195260087260128374236449893 36611266361274070169334355)
        ·
          refine ⟨54916899541911105254001533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36611266361274070169334355 54916899541911105254001533)
          ·
            refine ⟨20593837328216664470250575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54916899541911105254001533 20593837328216664470250575)
            ·
              refine ⟨30890755992324996705375863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20593837328216664470250575 30890755992324996705375863)
              ·
                refine ⟨46336133988487495058063795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30890755992324996705375863 46336133988487495058063795)
                ·
                  refine ⟨69504200982731242587095693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46336133988487495058063795 69504200982731242587095693)
                  ·
                    refine ⟨26064075368524215970160885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69504200982731242587095693 26064075368524215970160885)
                    ·
                      refine ⟨2443507065799145247202583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26064075368524215970160885 2443507065799145247202583)
                      ·
                        rfl

theorem cell23_4758713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4758713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758713 prefixEnd_4758713 := by exact prefixLift 4758713
  have htrace : WordTrace (prefixWord ++ tailWord_4758713) baseStart_4758713 baseEnd_4758713 := by
    simpa [prefixWord, tailWord_4758713, baseEnd_4758713] using wordTrace_append hprefix tailTrace_4758713
  have hstable : (prefixWord ++ tailWord_4758713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758713).length < 2 ^ (prefixWord ++ tailWord_4758713).sum := by decide
  have hdescent : baseEnd_4758713 < baseStart_4758713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758722 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4758722 : Nat := 118140960795 + 4758722 * 2 ^ 59
def prefixEnd_4758722 : Nat := 4983230072969 + 3 ^ 40 * 4758722 * 2
def baseEnd_4758722 : Nat := 2443511687125035711990043

theorem tailTrace_4758722 : CollatzResearch.WordTrace tailWord_4758722 prefixEnd_4758722 2443511687125035711990043 := by
  unfold tailWord_4758722
  simp only [CollatzResearch.WordTrace]
  refine ⟨43391212566492598464591605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115709900177313595905577613 43391212566492598464591605)
  ·
    refine ⟨4067926178108681106055463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43391212566492598464591605 4067926178108681106055463)
    ·
      refine ⟨6101889267163021659083195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067926178108681106055463 6101889267163021659083195)
      ·
        refine ⟨9152833900744532488624793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6101889267163021659083195 9152833900744532488624793)
        ·
          refine ⟨6864625425558399366468595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9152833900744532488624793 6864625425558399366468595)
          ·
            refine ⟨10296938138337599049702893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864625425558399366468595 10296938138337599049702893)
            ·
              refine ⟨3861351801876599643638585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10296938138337599049702893 3861351801876599643638585)
              ·
                refine ⟨2896013851407449732728939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861351801876599643638585 2896013851407449732728939)
                ·
                  refine ⟨4344020777111174599093409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896013851407449732728939 4344020777111174599093409)
                  ·
                    refine ⟨3258015582833380949320057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344020777111174599093409 3258015582833380949320057)
                    ·
                      refine ⟨2443511687125035711990043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258015582833380949320057 2443511687125035711990043)
                      ·
                        rfl

theorem cell23_4758722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4758722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758722 prefixEnd_4758722 := by exact prefixLift 4758722
  have htrace : WordTrace (prefixWord ++ tailWord_4758722) baseStart_4758722 baseEnd_4758722 := by
    simpa [prefixWord, tailWord_4758722, baseEnd_4758722] using wordTrace_append hprefix tailTrace_4758722
  have hstable : (prefixWord ++ tailWord_4758722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758722).length < 2 ^ (prefixWord ++ tailWord_4758722).sum := by decide
  have hdescent : baseEnd_4758722 < baseStart_4758722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758723 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4758723 : Nat := 118140960795 + 4758723 * 2 ^ 59
def prefixEnd_4758723 : Nat := 4983230072969 + 3 ^ 40 * 4758723 * 2
def baseEnd_4758723 : Nat := 2443512200605690208077537

theorem tailTrace_4758723 : CollatzResearch.WordTrace tailWord_4758723 prefixEnd_4758723 2443512200605690208077537 := by
  unfold tailWord_4758723
  simp only [CollatzResearch.WordTrace]
  refine ⟨173564886738966771029152823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115709924492644514019435215 173564886738966771029152823)
  ·
    refine ⟨260347330108450156543729235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173564886738966771029152823 260347330108450156543729235)
    ·
      refine ⟨390520995162675234815593853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260347330108450156543729235 390520995162675234815593853)
      ·
        refine ⟨146445373186003213055847695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390520995162675234815593853 146445373186003213055847695)
        ·
          refine ⟨219668059779004819583771543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146445373186003213055847695 219668059779004819583771543)
          ·
            refine ⟨329502089668507229375657315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219668059779004819583771543 329502089668507229375657315)
            ·
              refine ⟨494253134502760844063485973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329502089668507229375657315 494253134502760844063485973)
              ·
                refine ⟨23168115679816914565475905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 494253134502760844063485973 23168115679816914565475905)
                ·
                  refine ⟨17376086759862685924106929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23168115679816914565475905 17376086759862685924106929)
                  ·
                    refine ⟨13032065069897014443080197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17376086759862685924106929 13032065069897014443080197)
                    ·
                      refine ⟨2443512200605690208077537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13032065069897014443080197 2443512200605690208077537)
                      ·
                        rfl

theorem cell23_4758723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4758723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758723 prefixEnd_4758723 := by exact prefixLift 4758723
  have htrace : WordTrace (prefixWord ++ tailWord_4758723) baseStart_4758723 baseEnd_4758723 := by
    simpa [prefixWord, tailWord_4758723, baseEnd_4758723] using wordTrace_append hprefix tailTrace_4758723
  have hstable : (prefixWord ++ tailWord_4758723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758723).length < 2 ^ (prefixWord ++ tailWord_4758723).sum := by decide
  have hdescent : baseEnd_4758723 < baseStart_4758723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758814 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4758814 : Nat := 118140960795 + 4758814 * 2 ^ 59
def prefixEnd_4758814 : Nat := 4983230072969 + 3 ^ 40 * 4758814 * 2
def baseEnd_4758814 : Nat := 814519642448416450679873

theorem tailTrace_4758814 : CollatzResearch.WordTrace tailWord_4758814 prefixEnd_4758814 814519642448416450679873 := by
  unfold tailWord_4758814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696025722704636696339437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115712137187758062380476997 21696025722704636696339437)
  ·
    refine ⟨8136009646014238761127289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21696025722704636696339437 8136009646014238761127289)
    ·
      refine ⟨6102007234510679070845467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8136009646014238761127289 6102007234510679070845467)
      ·
        refine ⟨9153010851766018606268201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102007234510679070845467 9153010851766018606268201)
        ·
          refine ⟨6864758138824513954701151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9153010851766018606268201 6864758138824513954701151)
          ·
            refine ⟨10297137208236770932051727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864758138824513954701151 10297137208236770932051727)
            ·
              refine ⟨15445705812355156398077591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10297137208236770932051727 15445705812355156398077591)
              ·
                refine ⟨23168558718532734597116387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15445705812355156398077591 23168558718532734597116387)
                ·
                  refine ⟨34752838077799101895674581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23168558718532734597116387 34752838077799101895674581)
                  ·
                    refine ⟨814519642448416450679873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34752838077799101895674581 814519642448416450679873)
                    ·
                      rfl

theorem cell23_4758814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4758814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758814 prefixEnd_4758814 := by exact prefixLift 4758814
  have htrace : WordTrace (prefixWord ++ tailWord_4758814) baseStart_4758814 baseEnd_4758814 := by
    simpa [prefixWord, tailWord_4758814, baseEnd_4758814] using wordTrace_append hprefix tailTrace_4758814
  have hstable : (prefixWord ++ tailWord_4758814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758814).length < 2 ^ (prefixWord ++ tailWord_4758814).sum := by decide
  have hdescent : baseEnd_4758814 < baseStart_4758814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758844 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_4758844 : Nat := 118140960795 + 4758844 * 2 ^ 59
def prefixEnd_4758844 : Nat := 4983230072969 + 3 ^ 40 * 4758844 * 2
def baseEnd_4758844 : Nat := 814524777254961411554827

theorem tailTrace_4758844 : CollatzResearch.WordTrace tailWord_4758844 prefixEnd_4758844 814524777254961411554827 := by
  unfold tailWord_4758844
  simp only [CollatzResearch.WordTrace]
  refine ⟨86784649985764204347153793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115712866647685605796205057 86784649985764204347153793)
  ·
    refine ⟨65088487489323153260365345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86784649985764204347153793 65088487489323153260365345)
    ·
      refine ⟨48816365616992364945274009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65088487489323153260365345 48816365616992364945274009)
      ·
        refine ⟨36612274212744273708955507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48816365616992364945274009 36612274212744273708955507)
        ·
          refine ⟨54918411319116410563433261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36612274212744273708955507 54918411319116410563433261)
          ·
            refine ⟨20594404244668653961287473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54918411319116410563433261 20594404244668653961287473)
            ·
              refine ⟨15445803183501490470965605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20594404244668653961287473 15445803183501490470965605)
              ·
                refine ⟨2896088096906529463306051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15445803183501490470965605 2896088096906529463306051)
                ·
                  refine ⟨4344132145359794194959077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896088096906529463306051 4344132145359794194959077)
                  ·
                    refine ⟨814524777254961411554827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344132145359794194959077 814524777254961411554827)
                    ·
                      rfl

theorem cell23_4758844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_4758844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758844 prefixEnd_4758844 := by exact prefixLift 4758844
  have htrace : WordTrace (prefixWord ++ tailWord_4758844) baseStart_4758844 baseEnd_4758844 := by
    simpa [prefixWord, tailWord_4758844, baseEnd_4758844] using wordTrace_append hprefix tailTrace_4758844
  have hstable : (prefixWord ++ tailWord_4758844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758844).length < 2 ^ (prefixWord ++ tailWord_4758844).sum := by decide
  have hdescent : baseEnd_4758844 < baseStart_4758844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758867 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 3]
def baseStart_4758867 : Nat := 118140960795 + 4758867 * 2 ^ 59
def prefixEnd_4758867 : Nat := 4983230072969 + 3 ^ 40 * 4758867 * 2
def baseEnd_4758867 : Nat := 2443586141819937644676875

theorem tailTrace_4758867 : CollatzResearch.WordTrace tailWord_4758867 prefixEnd_4758867 2443586141819937644676875 := by
  unfold tailWord_4758867
  simp only [CollatzResearch.WordTrace]
  refine ⟨173570138850445083622394855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115713425900296722414929903 173570138850445083622394855)
  ·
    refine ⟨260355208275667625433592283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173570138850445083622394855 260355208275667625433592283)
    ·
      refine ⟨390532812413501438150388425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260355208275667625433592283 390532812413501438150388425)
      ·
        refine ⟨292899609310126078612791319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390532812413501438150388425 292899609310126078612791319)
        ·
          refine ⟨439349413965189117919186979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292899609310126078612791319 439349413965189117919186979)
          ·
            refine ⟨659024120947783676878780469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439349413965189117919186979 659024120947783676878780469)
            ·
              refine ⟨61783511338854719707385669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 659024120947783676878780469 61783511338854719707385669)
              ·
                refine ⟨11584408376035259945134813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61783511338854719707385669 11584408376035259945134813)
                ·
                  refine ⟨4344153141013222479425555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11584408376035259945134813 4344153141013222479425555)
                  ·
                    refine ⟨6516229711519833719138333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344153141013222479425555 6516229711519833719138333)
                    ·
                      refine ⟨2443586141819937644676875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516229711519833719138333 2443586141819937644676875)
                      ·
                        rfl

theorem cell23_4758867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_4758867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758867 prefixEnd_4758867 := by exact prefixLift 4758867
  have htrace : WordTrace (prefixWord ++ tailWord_4758867) baseStart_4758867 baseEnd_4758867 := by
    simpa [prefixWord, tailWord_4758867, baseEnd_4758867] using wordTrace_append hprefix tailTrace_4758867
  have hstable : (prefixWord ++ tailWord_4758867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758867).length < 2 ^ (prefixWord ++ tailWord_4758867).sum := by decide
  have hdescent : baseEnd_4758867 < baseStart_4758867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758921 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_4758921 : Nat := 118140960795 + 4758921 * 2 ^ 59
def prefixEnd_4758921 : Nat := 4983230072969 + 3 ^ 40 * 4758921 * 2
def baseEnd_4758921 : Nat := 814537956591760144467209

theorem tailTrace_4758921 : CollatzResearch.WordTrace tailWord_4758921 prefixEnd_4758921 814537956591760144467209 := by
  unfold tailWord_4758921
  simp only [CollatzResearch.WordTrace]
  refine ⟨173572108392249450844860617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115714738928166300563240411 173572108392249450844860617)
  ·
    refine ⟨130179081294187088133645463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173572108392249450844860617 130179081294187088133645463)
    ·
      refine ⟨195268621941280632200468195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130179081294187088133645463 195268621941280632200468195)
      ·
        refine ⟨292902932911920948300702293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195268621941280632200468195 292902932911920948300702293)
        ·
          refine ⟨3432456245061573612898855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 292902932911920948300702293 3432456245061573612898855)
          ·
            refine ⟨5148684367592360419348283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432456245061573612898855 5148684367592360419348283)
            ·
              refine ⟨7723026551388540629022425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148684367592360419348283 7723026551388540629022425)
              ·
                refine ⟨5792269913541405471766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723026551388540629022425 5792269913541405471766819)
                ·
                  refine ⟨8688404870312108207650229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792269913541405471766819 8688404870312108207650229)
                  ·
                    refine ⟨814537956591760144467209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8688404870312108207650229 814537956591760144467209)
                    ·
                      rfl

theorem cell23_4758921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_4758921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758921 prefixEnd_4758921 := by exact prefixLift 4758921
  have htrace : WordTrace (prefixWord ++ tailWord_4758921) baseStart_4758921 baseEnd_4758921 := by
    simpa [prefixWord, tailWord_4758921, baseEnd_4758921] using wordTrace_append hprefix tailTrace_4758921
  have hstable : (prefixWord ++ tailWord_4758921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758921).length < 2 ^ (prefixWord ++ tailWord_4758921).sum := by decide
  have hdescent : baseEnd_4758921 < baseStart_4758921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758924 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_4758924 : Nat := 118140960795 + 4758924 * 2 ^ 59
def prefixEnd_4758924 : Nat := 4983230072969 + 3 ^ 40 * 4758924 * 2
def baseEnd_4758924 : Nat := 2443615410217243921664113

theorem tailTrace_4758924 : CollatzResearch.WordTrace tailWord_4758924 prefixEnd_4758924 2443615410217243921664113 := by
  unfold tailWord_4758924
  simp only [CollatzResearch.WordTrace]
  refine ⟨86786108905619291178609913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115714811874159054904813217 86786108905619291178609913)
  ·
    refine ⟨65089581679214468383957435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86786108905619291178609913 65089581679214468383957435)
    ·
      refine ⟨97634372518821702575936153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65089581679214468383957435 97634372518821702575936153)
      ·
        refine ⟨73225779389116276931952115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97634372518821702575936153 73225779389116276931952115)
        ·
          refine ⟨109838669083674415397928173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73225779389116276931952115 109838669083674415397928173)
          ·
            refine ⟨41189500906377905774223065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109838669083674415397928173 41189500906377905774223065)
            ·
              refine ⟨30892125679783429330667299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41189500906377905774223065 30892125679783429330667299)
              ·
                refine ⟨46338188519675143996000949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30892125679783429330667299 46338188519675143996000949)
                ·
                  refine ⟨4344205173719544749625089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46338188519675143996000949 4344205173719544749625089)
                  ·
                    refine ⟨3258153880289658562218817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344205173719544749625089 3258153880289658562218817)
                    ·
                      refine ⟨2443615410217243921664113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258153880289658562218817 2443615410217243921664113)
                      ·
                        rfl

theorem cell23_4758924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_4758924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758924 prefixEnd_4758924 := by exact prefixLift 4758924
  have htrace : WordTrace (prefixWord ++ tailWord_4758924) baseStart_4758924 baseEnd_4758924 := by
    simpa [prefixWord, tailWord_4758924, baseEnd_4758924] using wordTrace_append hprefix tailTrace_4758924
  have hstable : (prefixWord ++ tailWord_4758924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758924).length < 2 ^ (prefixWord ++ tailWord_4758924).sum := by decide
  have hdescent : baseEnd_4758924 < baseStart_4758924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758937 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_4758937 : Nat := 118140960795 + 4758937 * 2 ^ 59
def prefixEnd_4758937 : Nat := 4983230072969 + 3 ^ 40 * 4758937 * 2
def baseEnd_4758937 : Nat := 2443622085465752370801553

theorem tailTrace_4758937 : CollatzResearch.WordTrace tailWord_4758937 prefixEnd_4758937 2443622085465752370801553 := by
  unfold tailWord_4758937
  simp only [CollatzResearch.WordTrace]
  refine ⟨173572691960191485577443065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115715127973460990384962043 173572691960191485577443065)
  ·
    refine ⟨130179518970143614183082299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173572691960191485577443065 130179518970143614183082299)
    ·
      refine ⟨195269278455215421274623449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130179518970143614183082299 195269278455215421274623449)
      ·
        refine ⟨146451958841411565955967587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195269278455215421274623449 146451958841411565955967587)
        ·
          refine ⟨219677938262117348933951381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146451958841411565955967587 219677938262117348933951381)
          ·
            refine ⟨10297403356036750731278971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219677938262117348933951381 10297403356036750731278971)
            ·
              refine ⟨15446105034055126096918457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10297403356036750731278971 15446105034055126096918457)
              ·
                refine ⟨11584578775541344572688843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15446105034055126096918457 11584578775541344572688843)
                ·
                  refine ⟨17376868163312016859033265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11584578775541344572688843 17376868163312016859033265)
                  ·
                    refine ⟨13032651122484012644274949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17376868163312016859033265 13032651122484012644274949)
                    ·
                      refine ⟨2443622085465752370801553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13032651122484012644274949 2443622085465752370801553)
                      ·
                        rfl

theorem cell23_4758937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_4758937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758937 prefixEnd_4758937 := by exact prefixLift 4758937
  have htrace : WordTrace (prefixWord ++ tailWord_4758937) baseStart_4758937 baseEnd_4758937 := by
    simpa [prefixWord, tailWord_4758937, baseEnd_4758937] using wordTrace_append hprefix tailTrace_4758937
  have hstable : (prefixWord ++ tailWord_4758937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758937).length < 2 ^ (prefixWord ++ tailWord_4758937).sum := by decide
  have hdescent : baseEnd_4758937 < baseStart_4758937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758941 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4758941 : Nat := 118140960795 + 4758941 * 2 ^ 59
def prefixEnd_4758941 : Nat := 4983230072969 + 3 ^ 40 * 4758941 * 2
def baseEnd_4758941 : Nat := 2443624139388370355151535

theorem tailTrace_4758941 : CollatzResearch.WordTrace tailWord_4758941 prefixEnd_4758941 2443624139388370355151535 := by
  unfold tailWord_4758941
  simp only [CollatzResearch.WordTrace]
  refine ⟨173572837852176994260588677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115715225234784662840392451 173572837852176994260588677)
  ·
    refine ⟨32544907097283186423860377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173572837852176994260588677 32544907097283186423860377)
    ·
      refine ⟨24408680322962389817895283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32544907097283186423860377 24408680322962389817895283)
      ·
        refine ⟨36613020484443584726842925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24408680322962389817895283 36613020484443584726842925)
        ·
          refine ⟨13729882681666344272566097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36613020484443584726842925 13729882681666344272566097)
          ·
            refine ⟨10297412011249758204424573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13729882681666344272566097 10297412011249758204424573)
            ·
              refine ⟨3861529504218659326659215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10297412011249758204424573 3861529504218659326659215)
              ·
                refine ⟨5792294256327988989988823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861529504218659326659215 5792294256327988989988823)
                ·
                  refine ⟨8688441384491983484983235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792294256327988989988823 8688441384491983484983235)
                  ·
                    refine ⟨13032662076737975227474853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8688441384491983484983235 13032662076737975227474853)
                    ·
                      refine ⟨2443624139388370355151535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13032662076737975227474853 2443624139388370355151535)
                      ·
                        rfl

theorem cell23_4758941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4758941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758941 prefixEnd_4758941 := by exact prefixLift 4758941
  have htrace : WordTrace (prefixWord ++ tailWord_4758941) baseStart_4758941 baseEnd_4758941 := by
    simpa [prefixWord, tailWord_4758941, baseEnd_4758941] using wordTrace_append hprefix tailTrace_4758941
  have hstable : (prefixWord ++ tailWord_4758941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758941).length < 2 ^ (prefixWord ++ tailWord_4758941).sum := by decide
  have hdescent : baseEnd_4758941 < baseStart_4758941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758952 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4758952 : Nat := 118140960795 + 4758952 * 2 ^ 59
def prefixEnd_4758952 : Nat := 4983230072969 + 3 ^ 40 * 4758952 * 2
def baseEnd_4758952 : Nat := 2443629787675569812113985

theorem tailTrace_4758952 : CollatzResearch.WordTrace tailWord_4758952 prefixEnd_4758952 2443629787675569812113985 := by
  unfold tailWord_4758952
  simp only [CollatzResearch.WordTrace]
  refine ⟨86786619527568571569619555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115715492703424762092826073 86786619527568571569619555)
  ·
    refine ⟨130179929291352857354429333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86786619527568571569619555 130179929291352857354429333)
    ·
      refine ⟨6102184185532165188488875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130179929291352857354429333 6102184185532165188488875)
      ·
        refine ⟨9153276278298247782733313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102184185532165188488875 9153276278298247782733313)
        ·
          refine ⟨6864957208723685837049985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9153276278298247782733313 6864957208723685837049985)
          ·
            refine ⟨5148717906542764377787489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6864957208723685837049985 5148717906542764377787489)
            ·
              refine ⟨3861538429907073283340617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5148717906542764377787489 3861538429907073283340617)
              ·
                refine ⟨2896153822430304962505463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861538429907073283340617 2896153822430304962505463)
                ·
                  refine ⟨4344230733645457443758195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896153822430304962505463 4344230733645457443758195)
                  ·
                    refine ⟨6516346100468186165637293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344230733645457443758195 6516346100468186165637293)
                    ·
                      refine ⟨2443629787675569812113985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516346100468186165637293 2443629787675569812113985)
                      ·
                        rfl

theorem cell23_4758952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4758952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758952 prefixEnd_4758952 := by exact prefixLift 4758952
  have htrace : WordTrace (prefixWord ++ tailWord_4758952) baseStart_4758952 baseEnd_4758952 := by
    simpa [prefixWord, tailWord_4758952, baseEnd_4758952] using wordTrace_append hprefix tailTrace_4758952
  have hstable : (prefixWord ++ tailWord_4758952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758952).length < 2 ^ (prefixWord ++ tailWord_4758952).sum := by decide
  have hdescent : baseEnd_4758952 < baseStart_4758952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758970 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_4758970 : Nat := 118140960795 + 4758970 * 2 ^ 59
def prefixEnd_4758970 : Nat := 4983230072969 + 3 ^ 40 * 4758970 * 2
def baseEnd_4758970 : Nat := 2443639030327350741688901

theorem tailTrace_4758970 : CollatzResearch.WordTrace tailWord_4758970 prefixEnd_4758970 2443639030327350741688901 := by
  unfold tailWord_4758970
  simp only [CollatzResearch.WordTrace]
  refine ⟨43393473892267983053348591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115715930379381288142262909 43393473892267983053348591)
  ·
    refine ⟨65090210838401974580022887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43393473892267983053348591 65090210838401974580022887)
    ·
      refine ⟨97635316257602961870034331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65090210838401974580022887 97635316257602961870034331)
      ·
        refine ⟨146452974386404442805051497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97635316257602961870034331 146452974386404442805051497)
        ·
          refine ⟨109839730789803332103788623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146452974386404442805051497 109839730789803332103788623)
          ·
            refine ⟨164759596184704998155682935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109839730789803332103788623 164759596184704998155682935)
            ·
              refine ⟨247139394277057497233524403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164759596184704998155682935 247139394277057497233524403)
              ·
                refine ⟨370709091415586245850286605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247139394277057497233524403 370709091415586245850286605)
                ·
                  refine ⟨139015909280844842193857477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370709091415586245850286605 139015909280844842193857477)
                  ·
                    refine ⟨26065482990158407911348277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139015909280844842193857477 26065482990158407911348277)
                    ·
                      refine ⟨2443639030327350741688901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26065482990158407911348277 2443639030327350741688901)
                      ·
                        rfl

theorem cell23_4758970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_4758970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758970 prefixEnd_4758970 := by exact prefixLift 4758970
  have htrace : WordTrace (prefixWord ++ tailWord_4758970) baseStart_4758970 baseEnd_4758970 := by
    simpa [prefixWord, tailWord_4758970, baseEnd_4758970] using wordTrace_append hprefix tailTrace_4758970
  have hstable : (prefixWord ++ tailWord_4758970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758970).length < 2 ^ (prefixWord ++ tailWord_4758970).sum := by decide
  have hdescent : baseEnd_4758970 < baseStart_4758970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758974 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_4758974 : Nat := 118140960795 + 4758974 * 2 ^ 59
def prefixEnd_4758974 : Nat := 4983230072969 + 3 ^ 40 * 4758974 * 2
def baseEnd_4758974 : Nat := 2443641084249968726038883

theorem tailTrace_4758974 : CollatzResearch.WordTrace tailWord_4758974 prefixEnd_4758974 2443641084249968726038883 := by
  unfold tailWord_4758974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696755182632180112067497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115716027640704960597693317 21696755182632180112067497)
  ·
    refine ⟨16272566386974135084050623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21696755182632180112067497 16272566386974135084050623)
    ·
      refine ⟨24408849580461202626075935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16272566386974135084050623 24408849580461202626075935)
      ·
        refine ⟨36613274370691803939113903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24408849580461202626075935 36613274370691803939113903)
        ·
          refine ⟨54919911556037705908670855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36613274370691803939113903 54919911556037705908670855)
          ·
            refine ⟨82379867334056558863006283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54919911556037705908670855 82379867334056558863006283)
            ·
              refine ⟨123569801001084838294509425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82379867334056558863006283 123569801001084838294509425)
              ·
                refine ⟨92677350750813628720882069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123569801001084838294509425 92677350750813628720882069)
                ·
                  refine ⟨4344250816444388846291347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92677350750813628720882069 4344250816444388846291347)
                  ·
                    refine ⟨6516376224666583269437021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344250816444388846291347 6516376224666583269437021)
                    ·
                      refine ⟨2443641084249968726038883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516376224666583269437021 2443641084249968726038883)
                      ·
                        rfl

theorem cell23_4758974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_4758974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758974 prefixEnd_4758974 := by exact prefixLift 4758974
  have htrace : WordTrace (prefixWord ++ tailWord_4758974) baseStart_4758974 baseEnd_4758974 := by
    simpa [prefixWord, tailWord_4758974, baseEnd_4758974] using wordTrace_append hprefix tailTrace_4758974
  have hstable : (prefixWord ++ tailWord_4758974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758974).length < 2 ^ (prefixWord ++ tailWord_4758974).sum := by decide
  have hdescent : baseEnd_4758974 < baseStart_4758974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4758984 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_4758984 : Nat := 118140960795 + 4758984 * 2 ^ 59
def prefixEnd_4758984 : Nat := 4983230072969 + 3 ^ 40 * 4758984 * 2
def baseEnd_4758984 : Nat := 2443646219056513686913837

theorem tailTrace_4758984 : CollatzResearch.WordTrace tailWord_4758984 prefixEnd_4758984 2443646219056513686913837 := by
  unfold tailWord_4758984
  simp only [CollatzResearch.WordTrace]
  refine ⟨86787203095510606302202003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115716270794014141736269337 86787203095510606302202003)
  ·
    refine ⟨130180804643265909453303005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86787203095510606302202003 130180804643265909453303005)
    ·
      refine ⟨48817801741224716044988627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130180804643265909453303005 48817801741224716044988627)
      ·
        refine ⟨73226702611837074067482941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48817801741224716044988627 73226702611837074067482941)
        ·
          refine ⟨27460013479438902775306103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73226702611837074067482941 27460013479438902775306103)
          ·
            refine ⟨41190020219158354162959155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27460013479438902775306103 41190020219158354162959155)
            ·
              refine ⟨61785030328737531244438733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41190020219158354162959155 61785030328737531244438733)
              ·
                refine ⟨23169386373276574216664525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61785030328737531244438733 23169386373276574216664525)
                ·
                  refine ⟨8688519889978715331249197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23169386373276574216664525 8688519889978715331249197)
                  ·
                    refine ⟨3258194958742018249218449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8688519889978715331249197 3258194958742018249218449)
                    ·
                      refine ⟨2443646219056513686913837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258194958742018249218449 2443646219056513686913837)
                      ·
                        rfl

theorem cell23_4758984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_4758984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4758984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4758984 prefixEnd_4758984 := by exact prefixLift 4758984
  have htrace : WordTrace (prefixWord ++ tailWord_4758984) baseStart_4758984 baseEnd_4758984 := by
    simpa [prefixWord, tailWord_4758984, baseEnd_4758984] using wordTrace_append hprefix tailTrace_4758984
  have hstable : (prefixWord ++ tailWord_4758984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4758984).length < 2 ^ (prefixWord ++ tailWord_4758984).sum := by decide
  have hdescent : baseEnd_4758984 < baseStart_4758984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4758984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759001 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 1, 3, 2]
def baseStart_4759001 : Nat := 118140960795 + 4759001 * 2 ^ 59
def prefixEnd_4759001 : Nat := 4983230072969 + 3 ^ 40 * 4759001 * 2
def baseEnd_4759001 : Nat := 2443654948227640120401259

theorem tailTrace_4759001 : CollatzResearch.WordTrace tailWord_4759001 prefixEnd_4759001 2443654948227640120401259 := by
  unfold tailWord_4759001
  simp only [CollatzResearch.WordTrace]
  refine ⟨173575026231959624507772857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115716684154639749671848571 173575026231959624507772857)
  ·
    refine ⟨130181269673969718380829643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173575026231959624507772857 130181269673969718380829643)
    ·
      refine ⟨195271904510954577571244465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130181269673969718380829643 195271904510954577571244465)
      ·
        refine ⟨146453928383215933178433349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195271904510954577571244465 146453928383215933178433349)
        ·
          refine ⟨27460111571852987470956253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146453928383215933178433349 27460111571852987470956253)
          ·
            refine ⟨10297541839444870301608595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27460111571852987470956253 10297541839444870301608595)
            ·
              refine ⟨15446312759167305452412893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10297541839444870301608595 15446312759167305452412893)
              ·
                refine ⟨5792367284687739544654835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15446312759167305452412893 5792367284687739544654835)
                ·
                  refine ⟨8688550927031609316982253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792367284687739544654835 8688550927031609316982253)
                  ·
                    refine ⟨3258206597636853493868345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8688550927031609316982253 3258206597636853493868345)
                    ·
                      refine ⟨2443654948227640120401259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258206597636853493868345 2443654948227640120401259)
                      ·
                        rfl

theorem cell23_4759001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_4759001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759001 prefixEnd_4759001 := by exact prefixLift 4759001
  have htrace : WordTrace (prefixWord ++ tailWord_4759001) baseStart_4759001 baseEnd_4759001 := by
    simpa [prefixWord, tailWord_4759001, baseEnd_4759001] using wordTrace_append hprefix tailTrace_4759001
  have hstable : (prefixWord ++ tailWord_4759001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759001).length < 2 ^ (prefixWord ++ tailWord_4759001).sum := by decide
  have hdescent : baseEnd_4759001 < baseStart_4759001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759037 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 7]
def baseStart_4759037 : Nat := 118140960795 + 4759037 * 2 ^ 59
def prefixEnd_4759037 : Nat := 4983230072969 + 3 ^ 40 * 4759037 * 2
def baseEnd_4759037 : Nat := 271519270392355775505677

theorem tailTrace_4759037 : CollatzResearch.WordTrace tailWord_4759037 prefixEnd_4759037 271519270392355775505677 := by
  unfold tailWord_4759037
  simp only [CollatzResearch.WordTrace]
  refine ⟨173576339259829202656083365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115717559506552801770722243 173576339259829202656083365)
  ·
    refine ⟨32545563611217975498015631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173576339259829202656083365 32545563611217975498015631)
    ·
      refine ⟨48818345416826963247023447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32545563611217975498015631 48818345416826963247023447)
      ·
        refine ⟨73227518125240444870535171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48818345416826963247023447 73227518125240444870535171)
        ·
          refine ⟨109841277187860667305802757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73227518125240444870535171 109841277187860667305802757)
          ·
            refine ⟨20595239472723875119838017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109841277187860667305802757 20595239472723875119838017)
            ·
              refine ⟨15446429604542906339878513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20595239472723875119838017 15446429604542906339878513)
              ·
                refine ⟨11584822203407179754908885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15446429604542906339878513 11584822203407179754908885)
                ·
                  refine ⟨271519270392355775505677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11584822203407179754908885 271519270392355775505677)
                  ·
                    rfl

theorem cell23_4759037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_4759037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759037 prefixEnd_4759037 := by exact prefixLift 4759037
  have htrace : WordTrace (prefixWord ++ tailWord_4759037) baseStart_4759037 baseEnd_4759037 := by
    simpa [prefixWord, tailWord_4759037, baseEnd_4759037] using wordTrace_append hprefix tailTrace_4759037
  have hstable : (prefixWord ++ tailWord_4759037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759037).length < 2 ^ (prefixWord ++ tailWord_4759037).sum := by decide
  have hdescent : baseEnd_4759037 < baseStart_4759037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759101 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_4759101 : Nat := 118140960795 + 4759101 * 2 ^ 59
def prefixEnd_4759101 : Nat := 4983230072969 + 3 ^ 40 * 4759101 * 2
def baseEnd_4759101 : Nat := 814568765431029909716933

theorem tailTrace_4759101 : CollatzResearch.WordTrace tailWord_4759101 prefixEnd_4759101 814568765431029909716933 := by
  unfold tailWord_4759101
  simp only [CollatzResearch.WordTrace]
  refine ⟨173578673531597341586413157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115719115687731561057608771 173578673531597341586413157)
  ·
    refine ⟨32546001287174501547452467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173578673531597341586413157 32546001287174501547452467)
    ·
      refine ⟨48819001930761752321178701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32546001287174501547452467 48819001930761752321178701)
      ·
        refine ⟨18307125724035657120442013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48819001930761752321178701 18307125724035657120442013)
        ·
          refine ⟨6865172146513371420165755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18307125724035657120442013 6865172146513371420165755)
          ·
            refine ⟨10297758219770057130248633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865172146513371420165755 10297758219770057130248633)
            ·
              refine ⟨7723318664827542847686475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10297758219770057130248633 7723318664827542847686475)
              ·
                refine ⟨11584977997241314271529713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723318664827542847686475 11584977997241314271529713)
                ·
                  refine ⟨8688733497930985703647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11584977997241314271529713 8688733497930985703647285)
                  ·
                    refine ⟨814568765431029909716933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8688733497930985703647285 814568765431029909716933)
                    ·
                      rfl

theorem cell23_4759101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_4759101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759101 prefixEnd_4759101 := by exact prefixLift 4759101
  have htrace : WordTrace (prefixWord ++ tailWord_4759101) baseStart_4759101 baseEnd_4759101 := by
    simpa [prefixWord, tailWord_4759101, baseEnd_4759101] using wordTrace_append hprefix tailTrace_4759101
  have hstable : (prefixWord ++ tailWord_4759101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759101).length < 2 ^ (prefixWord ++ tailWord_4759101).sum := by decide
  have hdescent : baseEnd_4759101 < baseStart_4759101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2]
def baseStart_4759104 : Nat := 118140960795 + 4759104 * 2 ^ 59
def prefixEnd_4759104 : Nat := 4983230072969 + 3 ^ 40 * 4759104 * 2
def baseEnd_4759104 : Nat := 2443707836735053217413285

theorem tailTrace_4759104 : CollatzResearch.WordTrace tailWord_4759104 prefixEnd_4759104 2443707836735053217413285 := by
  unfold tailWord_4759104
  simp only [CollatzResearch.WordTrace]
  refine ⟨86789391475293236549386183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115719188633724315399181577 86789391475293236549386183)
  ·
    refine ⟨130184087212939854824079275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86789391475293236549386183 130184087212939854824079275)
    ·
      refine ⟨195276130819409782236118913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130184087212939854824079275 195276130819409782236118913)
      ·
        refine ⟨146457098114557336677089185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195276130819409782236118913 146457098114557336677089185)
        ·
          refine ⟨109842823585918002507816889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146457098114557336677089185 109842823585918002507816889)
          ·
            refine ⟨82382117689438501880862667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109842823585918002507816889 82382117689438501880862667)
            ·
              refine ⟨123573176534157752821294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82382117689438501880862667 123573176534157752821294001)
              ·
                refine ⟨92679882400618314615970501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123573176534157752821294001 92679882400618314615970501)
                ·
                  refine ⟨17377477950115933990494469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92679882400618314615970501 17377477950115933990494469)
                  ·
                    refine ⟨3258277115646737623217713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17377477950115933990494469 3258277115646737623217713)
                    ·
                      refine ⟨2443707836735053217413285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258277115646737623217713 2443707836735053217413285)
                      ·
                        rfl

theorem cell23_4759104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_4759104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759104 prefixEnd_4759104 := by exact prefixLift 4759104
  have htrace : WordTrace (prefixWord ++ tailWord_4759104) baseStart_4759104 baseEnd_4759104 := by
    simpa [prefixWord, tailWord_4759104, baseEnd_4759104] using wordTrace_append hprefix tailTrace_4759104
  have hstable : (prefixWord ++ tailWord_4759104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759104).length < 2 ^ (prefixWord ++ tailWord_4759104).sum := by decide
  have hdescent : baseEnd_4759104 < baseStart_4759104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759158 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4759158 : Nat := 118140960795 + 4759158 * 2 ^ 59
def prefixEnd_4759158 : Nat := 4983230072969 + 3 ^ 40 * 4759158 * 2
def baseEnd_4759158 : Nat := 2443735564690396006138037

theorem tailTrace_4759158 : CollatzResearch.WordTrace tailWord_4759158 prefixEnd_4759158 2443735564690396006138037 := by
  unfold tailWord_4759158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848797030774427520077383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115720501661593893547492085 10848797030774427520077383)
  ·
    refine ⟨16273195546161641280116075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10848797030774427520077383 16273195546161641280116075)
    ·
      refine ⟨24409793319242461920174113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16273195546161641280116075 24409793319242461920174113)
      ·
        refine ⟨18307344989431846440130585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24409793319242461920174113 18307344989431846440130585)
        ·
          refine ⟨13730508742073884830097939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18307344989431846440130585 13730508742073884830097939)
          ·
            refine ⟨20595763113110827245146909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13730508742073884830097939 20595763113110827245146909)
            ·
              refine ⟨7723411167416560216930091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20595763113110827245146909 7723411167416560216930091)
              ·
                refine ⟨11585116751124840325395137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723411167416560216930091 11585116751124840325395137)
                ·
                  refine ⟨8688837563343630244046353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11585116751124840325395137 8688837563343630244046353)
                  ·
                    refine ⟨6516628172507722683034765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8688837563343630244046353 6516628172507722683034765)
                    ·
                      refine ⟨2443735564690396006138037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516628172507722683034765 2443735564690396006138037)
                      ·
                        rfl

theorem cell23_4759158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4759158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759158 prefixEnd_4759158 := by exact prefixLift 4759158
  have htrace : WordTrace (prefixWord ++ tailWord_4759158) baseStart_4759158 baseEnd_4759158 := by
    simpa [prefixWord, tailWord_4759158, baseEnd_4759158] using wordTrace_append hprefix tailTrace_4759158
  have hstable : (prefixWord ++ tailWord_4759158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759158).length < 2 ^ (prefixWord ++ tailWord_4759158).sum := by decide
  have hdescent : baseEnd_4759158 < baseStart_4759158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759198 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4759198 : Nat := 118140960795 + 4759198 * 2 ^ 59
def prefixEnd_4759198 : Nat := 4983230072969 + 3 ^ 40 * 4759198 * 2
def baseEnd_4759198 : Nat := 2443756103916575849637853

theorem tailTrace_4759198 : CollatzResearch.WordTrace tailWord_4759198 prefixEnd_4759198 2443756103916575849637853 := by
  unfold tailWord_4759198
  simp only [CollatzResearch.WordTrace]
  refine ⟨21697776426530740894086781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115721474274830618101796165 21697776426530740894086781)
  ·
    refine ⟨8136666159949027835282543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21697776426530740894086781 8136666159949027835282543)
    ·
      refine ⟨12204999239923541752923815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8136666159949027835282543 12204999239923541752923815)
      ·
        refine ⟨18307498859885312629385723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12204999239923541752923815 18307498859885312629385723)
        ·
          refine ⟨27461248289827968944078585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18307498859885312629385723 27461248289827968944078585)
          ·
            refine ⟨20595936217370976708058939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27461248289827968944078585 20595936217370976708058939)
            ·
              refine ⟨30893904326056465062088409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20595936217370976708058939 30893904326056465062088409)
              ·
                refine ⟨23170428244542348796566307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30893904326056465062088409 23170428244542348796566307)
                ·
                  refine ⟨34755642366813523194849461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23170428244542348796566307 34755642366813523194849461)
                  ·
                    refine ⟨3258341471888767799517137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34755642366813523194849461 3258341471888767799517137)
                    ·
                      refine ⟨2443756103916575849637853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258341471888767799517137 2443756103916575849637853)
                      ·
                        rfl

theorem cell23_4759198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4759198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759198 prefixEnd_4759198 := by exact prefixLift 4759198
  have htrace : WordTrace (prefixWord ++ tailWord_4759198) baseStart_4759198 baseEnd_4759198 := by
    simpa [prefixWord, tailWord_4759198, baseEnd_4759198] using wordTrace_append hprefix tailTrace_4759198
  have hstable : (prefixWord ++ tailWord_4759198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759198).length < 2 ^ (prefixWord ++ tailWord_4759198).sum := by decide
  have hdescent : baseEnd_4759198 < baseStart_4759198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759224 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_4759224 : Nat := 118140960795 + 4759224 * 2 ^ 59
def prefixEnd_4759224 : Nat := 4983230072969 + 3 ^ 40 * 4759224 * 2
def baseEnd_4759224 : Nat := 2443769454413592747912733

theorem tailTrace_4759224 : CollatzResearch.WordTrace tailWord_4759224 prefixEnd_4759224 2443769454413592747912733 := by
  unfold tailWord_4759224
  simp only [CollatzResearch.WordTrace]
  refine ⟨86791579855075866796570363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115722106473434489062093817 86791579855075866796570363)
  ·
    refine ⟨130187369782613800194855545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86791579855075866796570363 130187369782613800194855545)
    ·
      refine ⟨97640527336960350146141659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130187369782613800194855545 97640527336960350146141659)
      ·
        refine ⟨146460791005440525219212489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97640527336960350146141659 146460791005440525219212489)
        ·
          refine ⟨109845593254080393914409367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146460791005440525219212489 109845593254080393914409367)
          ·
            refine ⟨164768389881120590871614051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109845593254080393914409367 164768389881120590871614051)
            ·
              refine ⟨247152584821680886307421077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164768389881120590871614051 247152584821680886307421077)
              ·
                refine ⟨11585277413516291545660363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247152584821680886307421077 11585277413516291545660363)
                ·
                  refine ⟨17377916120274437318490545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11585277413516291545660363 17377916120274437318490545)
                  ·
                    refine ⟨13033437090205827988867909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17377916120274437318490545 13033437090205827988867909)
                    ·
                      refine ⟨2443769454413592747912733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13033437090205827988867909 2443769454413592747912733)
                      ·
                        rfl

theorem cell23_4759224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_4759224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759224 prefixEnd_4759224 := by exact prefixLift 4759224
  have htrace : WordTrace (prefixWord ++ tailWord_4759224) baseStart_4759224 baseEnd_4759224 := by
    simpa [prefixWord, tailWord_4759224, baseEnd_4759224] using wordTrace_append hprefix tailTrace_4759224
  have hstable : (prefixWord ++ tailWord_4759224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759224).length < 2 ^ (prefixWord ++ tailWord_4759224).sum := by decide
  have hdescent : baseEnd_4759224 < baseStart_4759224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759231 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_4759231 : Nat := 118140960795 + 4759231 * 2 ^ 59
def prefixEnd_4759231 : Nat := 4983230072969 + 3 ^ 40 * 4759231 * 2
def baseEnd_4759231 : Nat := 2443773048778174220525201

theorem tailTrace_4759231 : CollatzResearch.WordTrace tailWord_4759231 prefixEnd_4759231 2443773048778174220525201 := by
  unfold tailWord_4759231
  simp only [CollatzResearch.WordTrace]
  refine ⟨173583415021126373788645547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115722276680750915859097031 173583415021126373788645547)
  ·
    refine ⟨260375122531689560682968321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173583415021126373788645547 260375122531689560682968321)
    ·
      refine ⟨195281341898767170512226241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260375122531689560682968321 195281341898767170512226241)
      ·
        refine ⟨146461006424075377884169681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195281341898767170512226241 146461006424075377884169681)
        ·
          refine ⟨109845754818056533413127261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146461006424075377884169681 109845754818056533413127261)
          ·
            refine ⟨41192158056771200029922723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109845754818056533413127261 41192158056771200029922723)
            ·
              refine ⟨61788237085156800044884085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41192158056771200029922723 61788237085156800044884085)
              ·
                refine ⟨5792647226733450004207883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61788237085156800044884085 5792647226733450004207883)
                ·
                  refine ⟨8688970840100175006311825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792647226733450004207883 8688970840100175006311825)
                  ·
                    refine ⟨6516728130075131254733869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8688970840100175006311825 6516728130075131254733869)
                    ·
                      refine ⟨2443773048778174220525201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516728130075131254733869 2443773048778174220525201)
                      ·
                        rfl

theorem cell23_4759231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_4759231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759231 prefixEnd_4759231 := by exact prefixLift 4759231
  have htrace : WordTrace (prefixWord ++ tailWord_4759231) baseStart_4759231 baseEnd_4759231 := by
    simpa [prefixWord, tailWord_4759231, baseEnd_4759231] using wordTrace_append hprefix tailTrace_4759231
  have hstable : (prefixWord ++ tailWord_4759231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759231).length < 2 ^ (prefixWord ++ tailWord_4759231).sum := by decide
  have hdescent : baseEnd_4759231 < baseStart_4759231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759265 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_4759265 : Nat := 118140960795 + 4759265 * 2 ^ 59
def prefixEnd_4759265 : Nat := 4983230072969 + 3 ^ 40 * 4759265 * 2
def baseEnd_4759265 : Nat := 2443790507120427087500045

theorem tailTrace_4759265 : CollatzResearch.WordTrace tailWord_4759265 prefixEnd_4759265 2443790507120427087500045 := by
  unfold tailWord_4759265
  simp only [CollatzResearch.WordTrace]
  refine ⟨173584655103003197595383249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115723103402002131730255499 173584655103003197595383249)
  ·
    refine ⟨130188491327252398196537437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173584655103003197595383249 130188491327252398196537437)
    ·
      refine ⟨48820684247719649323701539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130188491327252398196537437 48820684247719649323701539)
      ·
        refine ⟨73231026371579473985552309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48820684247719649323701539 73231026371579473985552309)
        ·
          refine ⟨6865408722335575686145529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73231026371579473985552309 6865408722335575686145529)
          ·
            refine ⟨5149056541751681764609147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6865408722335575686145529 5149056541751681764609147)
            ·
              refine ⟨7723584812627522646913721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149056541751681764609147 7723584812627522646913721)
              ·
                refine ⟨5792688609470641985185291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723584812627522646913721 5792688609470641985185291)
                ·
                  refine ⟨8689032914205962977777937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792688609470641985185291 8689032914205962977777937)
                  ·
                    refine ⟨6516774685654472233333453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8689032914205962977777937 6516774685654472233333453)
                    ·
                      refine ⟨2443790507120427087500045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6516774685654472233333453 2443790507120427087500045)
                      ·
                        rfl

theorem cell23_4759265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_4759265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759265 prefixEnd_4759265 := by exact prefixLift 4759265
  have htrace : WordTrace (prefixWord ++ tailWord_4759265) baseStart_4759265 baseEnd_4759265 := by
    simpa [prefixWord, tailWord_4759265, baseEnd_4759265] using wordTrace_append hprefix tailTrace_4759265
  have hstable : (prefixWord ++ tailWord_4759265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759265).length < 2 ^ (prefixWord ++ tailWord_4759265).sum := by decide
  have hdescent : baseEnd_4759265 < baseStart_4759265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759274 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4759274 : Nat := 118140960795 + 4759274 * 2 ^ 59
def prefixEnd_4759274 : Nat := 4983230072969 + 3 ^ 40 * 4759274 * 2
def baseEnd_4759274 : Nat := 2443795128446317552287503

theorem tailTrace_4759274 : CollatzResearch.WordTrace tailWord_4759274 prefixEnd_4759274 2443795128446317552287503 := by
  unfold tailWord_4759274
  simp only [CollatzResearch.WordTrace]
  refine ⟨43396245839992648033115219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115723322239980394754973917 43396245839992648033115219)
  ·
    refine ⟨65094368759988972049672829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43396245839992648033115219 65094368759988972049672829)
    ·
      refine ⟨24410388284995864518627311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65094368759988972049672829 24410388284995864518627311)
      ·
        refine ⟨36615582427493796777940967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24410388284995864518627311 36615582427493796777940967)
        ·
          refine ⟨54923373641240695166911451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36615582427493796777940967 54923373641240695166911451)
          ·
            refine ⟨82385060461861042750367177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54923373641240695166911451 82385060461861042750367177)
            ·
              refine ⟨61788795346395782062775383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82385060461861042750367177 61788795346395782062775383)
              ·
                refine ⟨92683193019593673094163075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61788795346395782062775383 92683193019593673094163075)
                ·
                  refine ⟨139024789529390509641244613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92683193019593673094163075 139024789529390509641244613)
                  ·
                    refine ⟨26067148036760720557733365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139024789529390509641244613 26067148036760720557733365)
                    ·
                      refine ⟨2443795128446317552287503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26067148036760720557733365 2443795128446317552287503)
                      ·
                        rfl

theorem cell23_4759274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4759274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759274 prefixEnd_4759274 := by exact prefixLift 4759274
  have htrace : WordTrace (prefixWord ++ tailWord_4759274) baseStart_4759274 baseEnd_4759274 := by
    simpa [prefixWord, tailWord_4759274, baseEnd_4759274] using wordTrace_append hprefix tailTrace_4759274
  have hstable : (prefixWord ++ tailWord_4759274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759274).length < 2 ^ (prefixWord ++ tailWord_4759274).sum := by decide
  have hdescent : baseEnd_4759274 < baseStart_4759274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759309 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4759309 : Nat := 118140960795 + 4759309 * 2 ^ 59
def prefixEnd_4759309 : Nat := 4983230072969 + 3 ^ 40 * 4759309 * 2
def baseEnd_4759309 : Nat := 2443813100269224915349843

theorem tailTrace_4759309 : CollatzResearch.WordTrace tailWord_4759309 prefixEnd_4759309 2443813100269224915349843 := by
  unfold tailWord_4759309
  simp only [CollatzResearch.WordTrace]
  refine ⟨173586259914843793109984981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115724173276562528739989987 173586259914843793109984981)
  ·
    refine ⟨4068427966754151401015273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 173586259914843793109984981 4068427966754151401015273)
    ·
      refine ⟨3051320975065613550761455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4068427966754151401015273 3051320975065613550761455)
      ·
        refine ⟨4576981462598420326142183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051320975065613550761455 4576981462598420326142183)
        ·
          refine ⟨6865472193897630489213275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576981462598420326142183 6865472193897630489213275)
          ·
            refine ⟨10298208290846445733819913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865472193897630489213275 10298208290846445733819913)
            ·
              refine ⟨7723656218134834300364935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10298208290846445733819913 7723656218134834300364935)
              ·
                refine ⟨11585484327202251450547403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723656218134834300364935 11585484327202251450547403)
                ·
                  refine ⟨17378226490803377175821105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11585484327202251450547403 17378226490803377175821105)
                  ·
                    refine ⟨13033669868102532881865829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17378226490803377175821105 13033669868102532881865829)
                    ·
                      refine ⟨2443813100269224915349843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13033669868102532881865829 2443813100269224915349843)
                      ·
                        rfl

theorem cell23_4759309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4759309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759309 prefixEnd_4759309 := by exact prefixLift 4759309
  have htrace : WordTrace (prefixWord ++ tailWord_4759309) baseStart_4759309 baseEnd_4759309 := by
    simpa [prefixWord, tailWord_4759309, baseEnd_4759309] using wordTrace_append hprefix tailTrace_4759309
  have hstable : (prefixWord ++ tailWord_4759309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759309).length < 2 ^ (prefixWord ++ tailWord_4759309).sum := by decide
  have hdescent : baseEnd_4759309 < baseStart_4759309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759348 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4759348 : Nat := 118140960795 + 4759348 * 2 ^ 59
def prefixEnd_4759348 : Nat := 4983230072969 + 3 ^ 40 * 4759348 * 2
def baseEnd_4759348 : Nat := 2443833126014750262762163

theorem tailTrace_4759348 : CollatzResearch.WordTrace tailWord_4759348 prefixEnd_4759348 2443833126014750262762163 := by
  unfold tailWord_4759348
  simp only [CollatzResearch.WordTrace]
  refine ⟨86793841180851251385327349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115725121574468335180436465 86793841180851251385327349)
  ·
    refine ⟨8136922610704804817374439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86793841180851251385327349 8136922610704804817374439)
    ·
      refine ⟨12205383916057207226061659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8136922610704804817374439 12205383916057207226061659)
      ·
        refine ⟨18308075874085810839092489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12205383916057207226061659 18308075874085810839092489)
        ·
          refine ⟨13731056905564358129319367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18308075874085810839092489 13731056905564358129319367)
          ·
            refine ⟨20596585358346537193979051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13731056905564358129319367 20596585358346537193979051)
            ·
              refine ⟨30894878037519805790968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20596585358346537193979051 30894878037519805790968577)
              ·
                refine ⟨23171158528139854343226433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30894878037519805790968577 23171158528139854343226433)
                ·
                  refine ⟨17378368896104890757419825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23171158528139854343226433 17378368896104890757419825)
                  ·
                    refine ⟨13033776672078668068064869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17378368896104890757419825 13033776672078668068064869)
                    ·
                      refine ⟨2443833126014750262762163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13033776672078668068064869 2443833126014750262762163)
                      ·
                        rfl

theorem cell23_4759348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4759348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759348 prefixEnd_4759348 := by exact prefixLift 4759348
  have htrace : WordTrace (prefixWord ++ tailWord_4759348) baseStart_4759348 baseEnd_4759348 := by
    simpa [prefixWord, tailWord_4759348, baseEnd_4759348] using wordTrace_append hprefix tailTrace_4759348
  have hstable : (prefixWord ++ tailWord_4759348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759348).length < 2 ^ (prefixWord ++ tailWord_4759348).sum := by decide
  have hdescent : baseEnd_4759348 < baseStart_4759348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759352 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_4759352 : Nat := 118140960795 + 4759352 * 2 ^ 59
def prefixEnd_4759352 : Nat := 4983230072969 + 3 ^ 40 * 4759352 * 2
def baseEnd_4759352 : Nat := 2443835179937368247112145

theorem tailTrace_4759352 : CollatzResearch.WordTrace tailWord_4759352 prefixEnd_4759352 2443835179937368247112145 := by
  unfold tailWord_4759352
  simp only [CollatzResearch.WordTrace]
  refine ⟨86793914126844005726900155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115725218835792007635866873 86793914126844005726900155)
  ·
    refine ⟨130190871190266008590350233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86793914126844005726900155 130190871190266008590350233)
    ·
      refine ⟨97643153392699506442762675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130190871190266008590350233 97643153392699506442762675)
      ·
        refine ⟨146464730089049259664144013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97643153392699506442762675 146464730089049259664144013)
        ·
          refine ⟨54924273783393472374054005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146464730089049259664144013 54924273783393472374054005)
          ·
            refine ⟨5149150667193138035067563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54924273783393472374054005 5149150667193138035067563)
            ·
              refine ⟨7723726000789707052601345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149150667193138035067563 7723726000789707052601345)
              ·
                refine ⟨5792794500592280289451009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723726000789707052601345 5792794500592280289451009)
                ·
                  refine ⟨4344595875444210217088257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792794500592280289451009 4344595875444210217088257)
                  ·
                    refine ⟨3258446906583157662816193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344595875444210217088257 3258446906583157662816193)
                    ·
                      refine ⟨2443835179937368247112145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258446906583157662816193 2443835179937368247112145)
                      ·
                        rfl

theorem cell23_4759352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_4759352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759352 prefixEnd_4759352 := by exact prefixLift 4759352
  have htrace : WordTrace (prefixWord ++ tailWord_4759352) baseStart_4759352 baseEnd_4759352 := by
    simpa [prefixWord, tailWord_4759352, baseEnd_4759352] using wordTrace_append hprefix tailTrace_4759352
  have hstable : (prefixWord ++ tailWord_4759352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759352).length < 2 ^ (prefixWord ++ tailWord_4759352).sum := by decide
  have hdescent : baseEnd_4759352 < baseStart_4759352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759358 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_4759358 : Nat := 118140960795 + 4759358 * 2 ^ 59
def prefixEnd_4759358 : Nat := 4983230072969 + 3 ^ 40 * 4759358 * 2
def baseEnd_4759358 : Nat := 271537584535699469293013

theorem tailTrace_4759358 : CollatzResearch.WordTrace tailWord_4759358 prefixEnd_4759358 271537584535699469293013 := by
  unfold tailWord_4759358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21698505886458284309814841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115725364727777516319012485 21698505886458284309814841)
  ·
    refine ⟨16273879414843713232361131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21698505886458284309814841 16273879414843713232361131)
    ·
      refine ⟨24410819122265569848541697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16273879414843713232361131 24410819122265569848541697)
      ·
        refine ⟨18308114341699177386406273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24410819122265569848541697 18308114341699177386406273)
        ·
          refine ⟨13731085756274383039804705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18308114341699177386406273 13731085756274383039804705)
          ·
            refine ⟨10298314317205787279853529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13731085756274383039804705 10298314317205787279853529)
            ·
              refine ⟨7723735737904340459890147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10298314317205787279853529 7723735737904340459890147)
              ·
                refine ⟨11585603606856510689835221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723735737904340459890147 11585603606856510689835221)
                ·
                  refine ⟨271537584535699469293013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11585603606856510689835221 271537584535699469293013)
                  ·
                    rfl

theorem cell23_4759358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_4759358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759358 prefixEnd_4759358 := by exact prefixLift 4759358
  have htrace : WordTrace (prefixWord ++ tailWord_4759358) baseStart_4759358 baseEnd_4759358 := by
    simpa [prefixWord, tailWord_4759358, baseEnd_4759358] using wordTrace_append hprefix tailTrace_4759358
  have hstable : (prefixWord ++ tailWord_4759358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759358).length < 2 ^ (prefixWord ++ tailWord_4759358).sum := by decide
  have hdescent : baseEnd_4759358 < baseStart_4759358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759391 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4759391 : Nat := 118140960795 + 4759391 * 2 ^ 59
def prefixEnd_4759391 : Nat := 4983230072969 + 3 ^ 40 * 4759391 * 2
def baseEnd_4759391 : Nat := 2443855205682893594524465

theorem tailTrace_4759391 : CollatzResearch.WordTrace tailWord_4759391 prefixEnd_4759391 2443855205682893594524465 := by
  unfold tailWord_4759391
  simp only [CollatzResearch.WordTrace]
  refine ⟨173589250700546721114470027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115726167133697814076313351 173589250700546721114470027)
  ·
    refine ⟨260383876050820081671705041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173589250700546721114470027 260383876050820081671705041)
    ·
      refine ⟨195287907038115061253778781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260383876050820081671705041 195287907038115061253778781)
      ·
        refine ⟨73232965139293147970167043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195287907038115061253778781 73232965139293147970167043)
        ·
          refine ⟨109849447708939721955250565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73232965139293147970167043 109849447708939721955250565)
          ·
            refine ⟨20596771445426197866609481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109849447708939721955250565 20596771445426197866609481)
            ·
              refine ⟨15447578584069648399957111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20596771445426197866609481 15447578584069648399957111)
              ·
                refine ⟨23171367876104472599935667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15447578584069648399957111 23171367876104472599935667)
                ·
                  refine ⟨34757051814156708899903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23171367876104472599935667 34757051814156708899903501)
                  ·
                    refine ⟨13033894430308765837463813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34757051814156708899903501 13033894430308765837463813)
                    ·
                      refine ⟨2443855205682893594524465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13033894430308765837463813 2443855205682893594524465)
                      ·
                        rfl

theorem cell23_4759391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4759391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759391 prefixEnd_4759391 := by exact prefixLift 4759391
  have htrace : WordTrace (prefixWord ++ tailWord_4759391) baseStart_4759391 baseEnd_4759391 := by
    simpa [prefixWord, tailWord_4759391, baseEnd_4759391] using wordTrace_append hprefix tailTrace_4759391
  have hstable : (prefixWord ++ tailWord_4759391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759391).length < 2 ^ (prefixWord ++ tailWord_4759391).sum := by decide
  have hdescent : baseEnd_4759391 < baseStart_4759391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759401 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_4759401 : Nat := 118140960795 + 4759401 * 2 ^ 59
def prefixEnd_4759401 : Nat := 4983230072969 + 3 ^ 40 * 4759401 * 2
def baseEnd_4759401 : Nat := 814620113496479518466473

theorem tailTrace_4759401 : CollatzResearch.WordTrace tailWord_4759401 prefixEnd_4759401 814620113496479518466473 := by
  unfold tailWord_4759401
  simp only [CollatzResearch.WordTrace]
  refine ⟨173589615430510492822334057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115726410287006995214889371 173589615430510492822334057)
  ·
    refine ⟨130192211572882869616750543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173589615430510492822334057 130192211572882869616750543)
    ·
      refine ⟨195288317359324304425125815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130192211572882869616750543 195288317359324304425125815)
      ·
        refine ⟨292932476038986456637688723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195288317359324304425125815 292932476038986456637688723)
        ·
          refine ⟨439398714058479684956533085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292932476038986456637688723 439398714058479684956533085)
          ·
            refine ⟨164774517771929881858699907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 439398714058479684956533085 164774517771929881858699907)
            ·
              refine ⟨247161776657894822788049861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164774517771929881858699907 247161776657894822788049861)
              ·
                refine ⟨46342833123355279272759349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247161776657894822788049861 46342833123355279272759349)
                ·
                  refine ⟨4344640605314557431821189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46342833123355279272759349 4344640605314557431821189)
                  ·
                    refine ⟨814620113496479518466473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344640605314557431821189 814620113496479518466473)
                    ·
                      rfl

theorem cell23_4759401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_4759401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759401 prefixEnd_4759401 := by exact prefixLift 4759401
  have htrace : WordTrace (prefixWord ++ tailWord_4759401) baseStart_4759401 baseEnd_4759401 := by
    simpa [prefixWord, tailWord_4759401, baseEnd_4759401] using wordTrace_append hprefix tailTrace_4759401
  have hstable : (prefixWord ++ tailWord_4759401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759401).length < 2 ^ (prefixWord ++ tailWord_4759401).sum := by decide
  have hdescent : baseEnd_4759401 < baseStart_4759401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759418 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_4759418 : Nat := 118140960795 + 4759418 * 2 ^ 59
def prefixEnd_4759418 : Nat := 4983230072969 + 3 ^ 40 * 4759418 * 2
def baseEnd_4759418 : Nat := 814623023220188329628947

theorem tailTrace_4759418 : CollatzResearch.WordTrace tailWord_4759418 prefixEnd_4759418 814623023220188329628947 := by
  unfold tailWord_4759418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43397558867862226181425727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115726823647632603150468605 43397558867862226181425727)
  ·
    refine ⟨65096338301793339272138591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43397558867862226181425727 65096338301793339272138591)
    ·
      refine ⟨97644507452690008908207887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65096338301793339272138591 97644507452690008908207887)
      ·
        refine ⟨146466761179035013362311831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97644507452690008908207887 146466761179035013362311831)
        ·
          refine ⟨219700141768552520043467747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146466761179035013362311831 219700141768552520043467747)
          ·
            refine ⟨329550212652828780065201621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219700141768552520043467747 329550212652828780065201621)
            ·
              refine ⟨7723833109050674532778163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 329550212652828780065201621 7723833109050674532778163)
              ·
                refine ⟨11585749663576011799167245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723833109050674532778163 11585749663576011799167245)
                ·
                  refine ⟨4344656123841004424687717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11585749663576011799167245 4344656123841004424687717)
                  ·
                    refine ⟨814623023220188329628947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344656123841004424687717 814623023220188329628947)
                    ·
                      rfl

theorem cell23_4759418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_4759418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759418 prefixEnd_4759418 := by exact prefixLift 4759418
  have htrace : WordTrace (prefixWord ++ tailWord_4759418) baseStart_4759418 baseEnd_4759418 := by
    simpa [prefixWord, tailWord_4759418, baseEnd_4759418] using wordTrace_append hprefix tailTrace_4759418
  have hstable : (prefixWord ++ tailWord_4759418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759418).length < 2 ^ (prefixWord ++ tailWord_4759418).sum := by decide
  have hdescent : baseEnd_4759418 < baseStart_4759418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759441 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_4759441 : Nat := 118140960795 + 4759441 * 2 ^ 59
def prefixEnd_4759441 : Nat := 4983230072969 + 3 ^ 40 * 4759441 * 2
def baseEnd_4759441 : Nat := 2443880879715618398899235

theorem tailTrace_4759441 : CollatzResearch.WordTrace tailWord_4759441 prefixEnd_4759441 2443880879715618398899235 := by
  unfold tailWord_4759441
  simp only [CollatzResearch.WordTrace]
  refine ⟨173591074350365579653790177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115727382900243719769193451 173591074350365579653790177)
  ·
    refine ⟨130193305762774184740342633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173591074350365579653790177 130193305762774184740342633)
    ·
      refine ⟨97644979322080638555256975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130193305762774184740342633 97644979322080638555256975)
      ·
        refine ⟨146467468983120957832885463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97644979322080638555256975 146467468983120957832885463)
        ·
          refine ⟨219701203474681436749328195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146467468983120957832885463 219701203474681436749328195)
          ·
            refine ⟨329551805212022155123992293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219701203474681436749328195 329551805212022155123992293)
            ·
              refine ⟨61790963477254154085748555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329551805212022155123992293 61790963477254154085748555)
              ·
                refine ⟨92686445215881231128622833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61790963477254154085748555 92686445215881231128622833)
                ·
                  refine ⟨69514833911910923346467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92686445215881231128622833 69514833911910923346467125)
                  ·
                    refine ⟨6517015679241649063731293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69514833911910923346467125 6517015679241649063731293)
                    ·
                      refine ⟨2443880879715618398899235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517015679241649063731293 2443880879715618398899235)
                      ·
                        rfl

theorem cell23_4759441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_4759441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759441 prefixEnd_4759441 := by exact prefixLift 4759441
  have htrace : WordTrace (prefixWord ++ tailWord_4759441) baseStart_4759441 baseEnd_4759441 := by
    simpa [prefixWord, tailWord_4759441, baseEnd_4759441] using wordTrace_append hprefix tailTrace_4759441
  have hstable : (prefixWord ++ tailWord_4759441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759441).length < 2 ^ (prefixWord ++ tailWord_4759441).sum := by decide
  have hdescent : baseEnd_4759441 < baseStart_4759441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759498 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_4759498 : Nat := 118140960795 + 4759498 * 2 ^ 59
def prefixEnd_4759498 : Nat := 4983230072969 + 3 ^ 40 * 4759498 * 2
def baseEnd_4759498 : Nat := 2443910148112924675886473

theorem tailTrace_4759498 : CollatzResearch.WordTrace tailWord_4759498 prefixEnd_4759498 2443910148112924675886473 := by
  unfold tailWord_4759498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43398288327789769597153787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115728768874106052259076765 43398288327789769597153787)
  ·
    refine ⟨65097432491684654395730681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43398288327789769597153787 65097432491684654395730681)
    ·
      refine ⟨48823074368763490796798011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65097432491684654395730681 48823074368763490796798011)
      ·
        refine ⟨73234611553145236195197017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48823074368763490796798011 73234611553145236195197017)
        ·
          refine ⟨54925958664858927146397763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73234611553145236195197017 54925958664858927146397763)
          ·
            refine ⟨82388937997288390719596645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54925958664858927146397763 82388937997288390719596645)
            ·
              refine ⟨15447925874491573259924371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82388937997288390719596645 15447925874491573259924371)
              ·
                refine ⟨23171888811737359889886557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15447925874491573259924371 23171888811737359889886557)
                ·
                  refine ⟨8689458304401509958707459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23171888811737359889886557 8689458304401509958707459)
                  ·
                    refine ⟨13034187456602264938061189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8689458304401509958707459 13034187456602264938061189)
                    ·
                      refine ⟨2443910148112924675886473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13034187456602264938061189 2443910148112924675886473)
                      ·
                        rfl

theorem cell23_4759498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_4759498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759498 prefixEnd_4759498 := by exact prefixLift 4759498
  have htrace : WordTrace (prefixWord ++ tailWord_4759498) baseStart_4759498 baseEnd_4759498 := by
    simpa [prefixWord, tailWord_4759498, baseEnd_4759498] using wordTrace_append hprefix tailTrace_4759498
  have hstable : (prefixWord ++ tailWord_4759498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759498).length < 2 ^ (prefixWord ++ tailWord_4759498).sum := by decide
  have hdescent : baseEnd_4759498 < baseStart_4759498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759508 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_4759508 : Nat := 118140960795 + 4759508 * 2 ^ 59
def prefixEnd_4759508 : Nat := 4983230072969 + 3 ^ 40 * 4759508 * 2
def baseEnd_4759508 : Nat := 814638427639823212253809

theorem tailTrace_4759508 : CollatzResearch.WordTrace tailWord_4759508 prefixEnd_4759508 814638427639823212253809 := by
  unfold tailWord_4759508
  simp only [CollatzResearch.WordTrace]
  refine ⟨86796759020561425048239589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115729012027415233397652785 86796759020561425048239589)
  ·
    refine ⟨16274392316355267196544923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86796759020561425048239589 16274392316355267196544923)
    ·
      refine ⟨24411588474532900794817385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16274392316355267196544923 24411588474532900794817385)
      ·
        refine ⟨18308691355899675596113039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24411588474532900794817385 18308691355899675596113039)
        ·
          refine ⟨27463037033849513394169559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18308691355899675596113039 27463037033849513394169559)
          ·
            refine ⟨41194555550774270091254339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27463037033849513394169559 41194555550774270091254339)
            ·
              refine ⟨61791833326161405136881509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41194555550774270091254339 61791833326161405136881509)
              ·
                refine ⟨11585968748655263463165283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61791833326161405136881509 11585968748655263463165283)
                ·
                  refine ⟨17378953122982895194747925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11585968748655263463165283 17378953122982895194747925)
                  ·
                    refine ⟨814638427639823212253809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17378953122982895194747925 814638427639823212253809)
                    ·
                      rfl

theorem cell23_4759508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_4759508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759508 prefixEnd_4759508 := by exact prefixLift 4759508
  have htrace : WordTrace (prefixWord ++ tailWord_4759508) baseStart_4759508 baseEnd_4759508 := by
    simpa [prefixWord, tailWord_4759508, baseEnd_4759508] using wordTrace_append hprefix tailTrace_4759508
  have hstable : (prefixWord ++ tailWord_4759508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759508).length < 2 ^ (prefixWord ++ tailWord_4759508).sum := by decide
  have hdescent : baseEnd_4759508 < baseStart_4759508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759509 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4759509 : Nat := 118140960795 + 4759509 * 2 ^ 59
def prefixEnd_4759509 : Nat := 4983230072969 + 3 ^ 40 * 4759509 * 2
def baseEnd_4759509 : Nat := 2443915796400124132848923

theorem tailTrace_4759509 : CollatzResearch.WordTrace tailWord_4759509 prefixEnd_4759509 2443915796400124132848923 := by
  unfold tailWord_4759509
  simp only [CollatzResearch.WordTrace]
  refine ⟨173593554514119227267265581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115729036342746151511510387 173593554514119227267265581)
  ·
    refine ⟨65097582942794710225224593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173593554514119227267265581 65097582942794710225224593)
    ·
      refine ⟨48823187207096032668918445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65097582942794710225224593 48823187207096032668918445)
      ·
        refine ⟨18308695202661012250844417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48823187207096032668918445 18308695202661012250844417)
        ·
          refine ⟨13731521401995759188133313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18308695202661012250844417 13731521401995759188133313)
          ·
            refine ⟨10298641051496819391099985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13731521401995759188133313 10298641051496819391099985)
            ·
              refine ⟨7723980788622614543324989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10298641051496819391099985 7723980788622614543324989)
              ·
                refine ⟨2896492795733480453746871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7723980788622614543324989 2896492795733480453746871)
                ·
                  refine ⟨4344739193600220680620307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896492795733480453746871 4344739193600220680620307)
                  ·
                    refine ⟨6517108790400331020930461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344739193600220680620307 6517108790400331020930461)
                    ·
                      refine ⟨2443915796400124132848923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517108790400331020930461 2443915796400124132848923)
                      ·
                        rfl

theorem cell23_4759509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4759509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759509 prefixEnd_4759509 := by exact prefixLift 4759509
  have htrace : WordTrace (prefixWord ++ tailWord_4759509) baseStart_4759509 baseEnd_4759509 := by
    simpa [prefixWord, tailWord_4759509, baseEnd_4759509] using wordTrace_append hprefix tailTrace_4759509
  have hstable : (prefixWord ++ tailWord_4759509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759509).length < 2 ^ (prefixWord ++ tailWord_4759509).sum := by decide
  have hdescent : baseEnd_4759509 < baseStart_4759509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759516 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 6]
def baseStart_4759516 : Nat := 118140960795 + 4759516 * 2 ^ 59
def prefixEnd_4759516 : Nat := 4983230072969 + 3 ^ 40 * 4759516 * 2
def baseEnd_4759516 : Nat := 271546598973856178384599

theorem tailTrace_4759516 : CollatzResearch.WordTrace tailWord_4759516 prefixEnd_4759516 271546598973856178384599 := by
  unfold tailWord_4759516
  simp only [CollatzResearch.WordTrace]
  refine ⟨86796904912546933731385201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115729206550062578308513601 86796904912546933731385201)
  ·
    refine ⟨65097678684410200298538901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86796904912546933731385201 65097678684410200298538901)
    ·
      refine ⟨3051453688331728138994011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65097678684410200298538901 3051453688331728138994011)
      ·
        refine ⟨4577180532497592208491017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051453688331728138994011 4577180532497592208491017)
        ·
          refine ⟨3432885399373194156368263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577180532497592208491017 3432885399373194156368263)
          ·
            refine ⟨5149328099059791234552395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432885399373194156368263 5149328099059791234552395)
            ·
              refine ⟨7723992148589686851828593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149328099059791234552395 7723992148589686851828593)
              ·
                refine ⟨5792994111442265138871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723992148589686851828593 5792994111442265138871445)
                ·
                  refine ⟨271546598973856178384599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5792994111442265138871445 271546598973856178384599)
                  ·
                    rfl

theorem cell23_4759516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_4759516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759516 prefixEnd_4759516 := by exact prefixLift 4759516
  have htrace : WordTrace (prefixWord ++ tailWord_4759516) baseStart_4759516 baseEnd_4759516 := by
    simpa [prefixWord, tailWord_4759516, baseEnd_4759516] using wordTrace_append hprefix tailTrace_4759516
  have hstable : (prefixWord ++ tailWord_4759516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759516).length < 2 ^ (prefixWord ++ tailWord_4759516).sum := by decide
  have hdescent : baseEnd_4759516 < baseStart_4759516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759542 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_4759542 : Nat := 118140960795 + 4759542 * 2 ^ 59
def prefixEnd_4759542 : Nat := 4983230072969 + 3 ^ 40 * 4759542 * 2
def baseEnd_4759542 : Nat := 814644247087240834578757

theorem tailTrace_4759542 : CollatzResearch.WordTrace tailWord_4759542 prefixEnd_4759542 814644247087240834578757 := by
  unfold tailWord_4759542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10849672382687479618951055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115729838748666449268811253 10849672382687479618951055)
  ·
    refine ⟨16274508574031219428426583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10849672382687479618951055 16274508574031219428426583)
    ·
      refine ⟨24411762861046829142639875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16274508574031219428426583 24411762861046829142639875)
      ·
        refine ⟨36617644291570243713959813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24411762861046829142639875 36617644291570243713959813)
        ·
          refine ⟨6865808304669420696367465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36617644291570243713959813 6865808304669420696367465)
          ·
            refine ⟨5149356228502065522275599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6865808304669420696367465 5149356228502065522275599)
            ·
              refine ⟨7724034342753098283413399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149356228502065522275599 7724034342753098283413399)
              ·
                refine ⟨11586051514129647425120099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724034342753098283413399 11586051514129647425120099)
                ·
                  refine ⟨17379077271194471137680149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586051514129647425120099 17379077271194471137680149)
                  ·
                    refine ⟨814644247087240834578757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17379077271194471137680149 814644247087240834578757)
                    ·
                      rfl

theorem cell23_4759542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_4759542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759542 prefixEnd_4759542 := by exact prefixLift 4759542
  have htrace : WordTrace (prefixWord ++ tailWord_4759542) baseStart_4759542 baseEnd_4759542 := by
    simpa [prefixWord, tailWord_4759542, baseEnd_4759542] using wordTrace_append hprefix tailTrace_4759542
  have hstable : (prefixWord ++ tailWord_4759542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759542).length < 2 ^ (prefixWord ++ tailWord_4759542).sum := by decide
  have hdescent : baseEnd_4759542 < baseStart_4759542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759545 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4759545 : Nat := 118140960795 + 4759545 * 2 ^ 59
def prefixEnd_4759545 : Nat := 4983230072969 + 3 ^ 40 * 4759545 * 2
def baseEnd_4759545 : Nat := 2443934281703685991998757

theorem tailTrace_4759545 : CollatzResearch.WordTrace tailWord_4759545 prefixEnd_4759545 2443934281703685991998757 := by
  unfold tailWord_4759545
  simp only [CollatzResearch.WordTrace]
  refine ⟨173594867541988805415576089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115729911694659203610384059 173594867541988805415576089)
  ·
    refine ⟨130196150656491604061682067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173594867541988805415576089 130196150656491604061682067)
    ·
      refine ⟨195294225984737406092523101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130196150656491604061682067 195294225984737406092523101)
      ·
        refine ⟨73235334744276527284696163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195294225984737406092523101 73235334744276527284696163)
        ·
          refine ⟨109853002116414790927044245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73235334744276527284696163 109853002116414790927044245)
          ·
            refine ⟨5149359474206943324705199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109853002116414790927044245 5149359474206943324705199)
            ·
              refine ⟨7724039211310414987057799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149359474206943324705199 7724039211310414987057799)
              ·
                refine ⟨11586058816965622480586699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724039211310414987057799 11586058816965622480586699)
                ·
                  refine ⟨17379088225448433720880049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586058816965622480586699 17379088225448433720880049)
                  ·
                    refine ⟨13034316169086325290660037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17379088225448433720880049 13034316169086325290660037)
                    ·
                      refine ⟨2443934281703685991998757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13034316169086325290660037 2443934281703685991998757)
                      ·
                        rfl

theorem cell23_4759545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4759545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759545 prefixEnd_4759545 := by exact prefixLift 4759545
  have htrace : WordTrace (prefixWord ++ tailWord_4759545) baseStart_4759545 baseEnd_4759545 := by
    simpa [prefixWord, tailWord_4759545, baseEnd_4759545] using wordTrace_append hprefix tailTrace_4759545
  have hstable : (prefixWord ++ tailWord_4759545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759545).length < 2 ^ (prefixWord ++ tailWord_4759545).sum := by decide
  have hdescent : baseEnd_4759545 < baseStart_4759545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759551 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 7]
def baseStart_4759551 : Nat := 118140960795 + 4759551 * 2 ^ 59
def prefixEnd_4759551 : Nat := 4983230072969 + 3 ^ 40 * 4759551 * 2
def baseEnd_4759551 : Nat := 814645787529204322841243

theorem tailTrace_4759551 : CollatzResearch.WordTrace tailWord_4759551 prefixEnd_4759551 814645787529204322841243 := by
  unfold tailWord_4759551
  simp only [CollatzResearch.WordTrace]
  refine ⟨173595086379967068440294507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115730057586644712293529671 173595086379967068440294507)
  ·
    refine ⟨260392629569950602660441761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173595086379967068440294507 260392629569950602660441761)
    ·
      refine ⟨195294472177462951995331321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260392629569950602660441761 195294472177462951995331321)
      ·
        refine ⟨146470854133097213996498491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195294472177462951995331321 146470854133097213996498491)
        ·
          refine ⟨219706281199645820994747737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146470854133097213996498491 219706281199645820994747737)
          ·
            refine ⟨164779710899734365746060803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219706281199645820994747737 164779710899734365746060803)
            ·
              refine ⟨247169566349601548619091205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164779710899734365746060803 247169566349601548619091205)
              ·
                refine ⟨46344293690550290366079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247169566349601548619091205 46344293690550290366079601)
                ·
                  refine ⟨34758220267912717774559701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46344293690550290366079601 34758220267912717774559701)
                  ·
                    refine ⟨814645787529204322841243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34758220267912717774559701 814645787529204322841243)
                    ·
                      rfl

theorem cell23_4759551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_4759551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759551 prefixEnd_4759551 := by exact prefixLift 4759551
  have htrace : WordTrace (prefixWord ++ tailWord_4759551) baseStart_4759551 baseEnd_4759551 := by
    simpa [prefixWord, tailWord_4759551, baseEnd_4759551] using wordTrace_append hprefix tailTrace_4759551
  have hstable : (prefixWord ++ tailWord_4759551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759551).length < 2 ^ (prefixWord ++ tailWord_4759551).sum := by decide
  have hdescent : baseEnd_4759551 < baseStart_4759551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759572 : List Nat := [2, 4, 3, 2, 1, 2, 9]
def baseStart_4759572 : Nat := 118140960795 + 4759572 * 2 ^ 59
def prefixEnd_4759572 : Nat := 4983230072969 + 3 ^ 40 * 4759572 * 2
def baseEnd_4759572 : Nat := 30172199329399473905693

theorem tailTrace_4759572 : CollatzResearch.WordTrace tailWord_4759572 prefixEnd_4759572 30172199329399473905693 := by
  unfold tailWord_4759572
  simp only [CollatzResearch.WordTrace]
  refine ⟨86797926156445494513404485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115730568208593992684539313 86797926156445494513404485)
  ·
    refine ⟨16274611154333530221263341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86797926156445494513404485 16274611154333530221263341)
    ·
      refine ⟨6102979182875073832973753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16274611154333530221263341 6102979182875073832973753)
      ·
        refine ⟨4577234387156305374730315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6102979182875073832973753 4577234387156305374730315)
        ·
          refine ⟨6865851580734458062095473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577234387156305374730315 6865851580734458062095473)
          ·
            refine ⟨5149388685550843546571605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6865851580734458062095473 5149388685550843546571605)
            ·
              refine ⟨30172199329399473905693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5149388685550843546571605 30172199329399473905693)
              ·
                rfl

theorem cell23_4759572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 9].length) (baseStart_4759572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759572 prefixEnd_4759572 := by exact prefixLift 4759572
  have htrace : WordTrace (prefixWord ++ tailWord_4759572) baseStart_4759572 baseEnd_4759572 := by
    simpa [prefixWord, tailWord_4759572, baseEnd_4759572] using wordTrace_append hprefix tailTrace_4759572
  have hstable : (prefixWord ++ tailWord_4759572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759572).length < 2 ^ (prefixWord ++ tailWord_4759572).sum := by decide
  have hdescent : baseEnd_4759572 < baseStart_4759572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759655 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_4759655 : Nat := 118140960795 + 4759655 * 2 ^ 59
def prefixEnd_4759655 : Nat := 4983230072969 + 3 ^ 40 * 4759655 * 2
def baseEnd_4759655 : Nat := 2443990764575680561623251

theorem tailTrace_4759655 : CollatzResearch.WordTrace tailWord_4759655 prefixEnd_4759655 2443990764575680561623251 := by
  unfold tailWord_4759655
  simp only [CollatzResearch.WordTrace]
  refine ⟨173598879571590294202080419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115732586381060196134720279 173598879571590294202080419)
  ·
    refine ⟨260398319357385441303120629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173598879571590294202080419 260398319357385441303120629)
    ·
      refine ⟨24412342439754885122167559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260398319357385441303120629 24412342439754885122167559)
      ·
        refine ⟨36618513659632327683251339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24412342439754885122167559 36618513659632327683251339)
        ·
          refine ⟨54927770489448491524877009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36618513659632327683251339 54927770489448491524877009)
          ·
            refine ⟨41195827867086368643657757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54927770489448491524877009 41195827867086368643657757)
            ·
              refine ⟨15448435450157388241371659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41195827867086368643657757 15448435450157388241371659)
              ·
                refine ⟨23172653175236082362057489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15448435450157388241371659 23172653175236082362057489)
                ·
                  refine ⟨17379489881427061771543117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23172653175236082362057489 17379489881427061771543117)
                  ·
                    refine ⟨6517308705535148164328669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17379489881427061771543117 6517308705535148164328669)
                    ·
                      refine ⟨2443990764575680561623251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517308705535148164328669 2443990764575680561623251)
                      ·
                        rfl

theorem cell23_4759655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_4759655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759655 prefixEnd_4759655 := by exact prefixLift 4759655
  have htrace : WordTrace (prefixWord ++ tailWord_4759655) baseStart_4759655 baseEnd_4759655 := by
    simpa [prefixWord, tailWord_4759655, baseEnd_4759655] using wordTrace_append hprefix tailTrace_4759655
  have hstable : (prefixWord ++ tailWord_4759655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759655).length < 2 ^ (prefixWord ++ tailWord_4759655).sum := by decide
  have hdescent : baseEnd_4759655 < baseStart_4759655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759665 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_4759665 : Nat := 118140960795 + 4759665 * 2 ^ 59
def prefixEnd_4759665 : Nat := 4983230072969 + 3 ^ 40 * 4759665 * 2
def baseEnd_4759665 : Nat := 2443995899382225522498205

theorem tailTrace_4759665 : CollatzResearch.WordTrace tailWord_4759665 prefixEnd_4759665 2443995899382225522498205 := by
  unfold tailWord_4759665
  simp only [CollatzResearch.WordTrace]
  refine ⟨173599244301554065909944449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115732829534369377273296299 173599244301554065909944449)
  ·
    refine ⟨130199433226165549432458337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173599244301554065909944449 130199433226165549432458337)
    ·
      refine ⟨97649574919624162074343753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130199433226165549432458337 97649574919624162074343753)
      ·
        refine ⟨73237181189718121555757815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97649574919624162074343753 73237181189718121555757815)
        ·
          refine ⟨109855771784577182333636723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73237181189718121555757815 109855771784577182333636723)
          ·
            refine ⟨164783657676865773500455085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109855771784577182333636723 164783657676865773500455085)
            ·
              refine ⟨61793871628824665062670657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164783657676865773500455085 61793871628824665062670657)
              ·
                refine ⟨46345403721618498797002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61793871628824665062670657 46345403721618498797002993)
                ·
                  refine ⟨34759052791213874097752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46345403721618498797002993 34759052791213874097752245)
                  ·
                    refine ⟨3258661199176300696664273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34759052791213874097752245 3258661199176300696664273)
                    ·
                      refine ⟨2443995899382225522498205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258661199176300696664273 2443995899382225522498205)
                      ·
                        rfl

theorem cell23_4759665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_4759665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759665 prefixEnd_4759665 := by exact prefixLift 4759665
  have htrace : WordTrace (prefixWord ++ tailWord_4759665) baseStart_4759665 baseEnd_4759665 := by
    simpa [prefixWord, tailWord_4759665, baseEnd_4759665] using wordTrace_append hprefix tailTrace_4759665
  have hstable : (prefixWord ++ tailWord_4759665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759665).length < 2 ^ (prefixWord ++ tailWord_4759665).sum := by decide
  have hdescent : baseEnd_4759665 < baseStart_4759665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759712 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2]
def baseStart_4759712 : Nat := 118140960795 + 4759712 * 2 ^ 59
def prefixEnd_4759712 : Nat := 4983230072969 + 3 ^ 40 * 4759712 * 2
def baseEnd_4759712 : Nat := 2444020032972986838610489

theorem tailTrace_4759712 : CollatzResearch.WordTrace tailWord_4759712 prefixEnd_4759712 2444020032972986838610489 := by
  unfold tailWord_4759712
  simp only [CollatzResearch.WordTrace]
  refine ⟨86800479266191896468452695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115733972354922528624603593 86800479266191896468452695)
  ·
    refine ⟨130200718899287844702679043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86800479266191896468452695 130200718899287844702679043)
    ·
      refine ⟨195301078348931767054018565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130200718899287844702679043 195301078348931767054018565)
      ·
        refine ⟨36618952190424706322628481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195301078348931767054018565 36618952190424706322628481)
        ·
          refine ⟨27464214142818529741971361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36618952190424706322628481 27464214142818529741971361)
          ·
            refine ⟨20598160607113897306478521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27464214142818529741971361 20598160607113897306478521)
            ·
              refine ⟨15448620455335422979858891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20598160607113897306478521 15448620455335422979858891)
              ·
                refine ⟨23172930683003134469788337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15448620455335422979858891 23172930683003134469788337)
                ·
                  refine ⟨17379698012252350852341253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23172930683003134469788337 17379698012252350852341253)
                  ·
                    refine ⟨3258693377297315784813985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17379698012252350852341253 3258693377297315784813985)
                    ·
                      refine ⟨2444020032972986838610489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258693377297315784813985 2444020032972986838610489)
                      ·
                        rfl

theorem cell23_4759712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_4759712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759712 prefixEnd_4759712 := by exact prefixLift 4759712
  have htrace : WordTrace (prefixWord ++ tailWord_4759712) baseStart_4759712 baseEnd_4759712 := by
    simpa [prefixWord, tailWord_4759712, baseEnd_4759712] using wordTrace_append hprefix tailTrace_4759712
  have hstable : (prefixWord ++ tailWord_4759712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759712).length < 2 ^ (prefixWord ++ tailWord_4759712).sum := by decide
  have hdescent : baseEnd_4759712 < baseStart_4759712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759746 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4759746 : Nat := 118140960795 + 4759746 * 2 ^ 59
def prefixEnd_4759746 : Nat := 4983230072969 + 3 ^ 40 * 4759746 * 2
def baseEnd_4759746 : Nat := 2444037491315239705585333

theorem tailTrace_4759746 : CollatzResearch.WordTrace tailWord_4759746 prefixEnd_4759746 2444037491315239705585333 := by
  unfold tailWord_4759746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43400549653565154185910773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115734799076173744495762061 43400549653565154185910773)
  ·
    refine ⟨4068801530021733204929135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43400549653565154185910773 4068801530021733204929135)
    ·
      refine ⟨6103202295032599807393703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068801530021733204929135 6103202295032599807393703)
      ·
        refine ⟨9154803442548899711090555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6103202295032599807393703 9154803442548899711090555)
        ·
          refine ⟨13732205163823349566635833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9154803442548899711090555 13732205163823349566635833)
          ·
            refine ⟨10299153872867512174976875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13732205163823349566635833 10299153872867512174976875)
            ·
              refine ⟨15448730809301268262465313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10299153872867512174976875 15448730809301268262465313)
              ·
                refine ⟨11586548106975951196848985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15448730809301268262465313 11586548106975951196848985)
                ·
                  refine ⟨8689911080231963397636739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11586548106975951196848985 8689911080231963397636739)
                  ·
                    refine ⟨13034866620347945096455109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8689911080231963397636739 13034866620347945096455109)
                    ·
                      refine ⟨2444037491315239705585333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13034866620347945096455109 2444037491315239705585333)
                      ·
                        rfl

theorem cell23_4759746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4759746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759746 prefixEnd_4759746 := by exact prefixLift 4759746
  have htrace : WordTrace (prefixWord ++ tailWord_4759746) baseStart_4759746 baseEnd_4759746 := by
    simpa [prefixWord, tailWord_4759746, baseEnd_4759746] using wordTrace_append hprefix tailTrace_4759746
  have hstable : (prefixWord ++ tailWord_4759746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759746).length < 2 ^ (prefixWord ++ tailWord_4759746).sum := by decide
  have hdescent : baseEnd_4759746 < baseStart_4759746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759756 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_4759756 : Nat := 118140960795 + 4759756 * 2 ^ 59
def prefixEnd_4759756 : Nat := 4983230072969 + 3 ^ 40 * 4759756 * 2
def baseEnd_4759756 : Nat := 814680875373928222153429

theorem tailTrace_4759756 : CollatzResearch.WordTrace tailWord_4759756 prefixEnd_4759756 814680875373928222153429 := by
  unfold tailWord_4759756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86801281672112194225753561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115735042229482925634338081 86801281672112194225753561)
  ·
    refine ⟨65100961254084145669315171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86801281672112194225753561 65100961254084145669315171)
    ·
      refine ⟨97651441881126218503972757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65100961254084145669315171 97651441881126218503972757)
      ·
        refine ⟨4577411338177791492373723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97651441881126218503972757 4577411338177791492373723)
        ·
          refine ⟨6866117007266687238560585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577411338177791492373723 6866117007266687238560585)
          ·
            refine ⟨5149587755450015428920439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866117007266687238560585 5149587755450015428920439)
            ·
              refine ⟨7724381633175023143380659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149587755450015428920439 7724381633175023143380659)
              ·
                refine ⟨11586572449762534715070989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724381633175023143380659 11586572449762534715070989)
                ·
                  refine ⟨4344964668660950518151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11586572449762534715070989 4344964668660950518151621)
                  ·
                    refine ⟨814680875373928222153429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344964668660950518151621 814680875373928222153429)
                    ·
                      rfl

theorem cell23_4759756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_4759756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759756 prefixEnd_4759756 := by exact prefixLift 4759756
  have htrace : WordTrace (prefixWord ++ tailWord_4759756) baseStart_4759756 baseEnd_4759756 := by
    simpa [prefixWord, tailWord_4759756, baseEnd_4759756] using wordTrace_append hprefix tailTrace_4759756
  have hstable : (prefixWord ++ tailWord_4759756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759756).length < 2 ^ (prefixWord ++ tailWord_4759756).sum := by decide
  have hdescent : baseEnd_4759756 < baseStart_4759756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759785 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_4759785 : Nat := 118140960795 + 4759785 * 2 ^ 59
def prefixEnd_4759785 : Nat := 4983230072969 + 3 ^ 40 * 4759785 * 2
def baseEnd_4759785 : Nat := 2444057517060765052997653

theorem tailTrace_4759785 : CollatzResearch.WordTrace tailWord_4759785 prefixEnd_4759785 2444057517060765052997653 := by
  unfold tailWord_4759785
  simp only [CollatzResearch.WordTrace]
  refine ⟨173603621061119326404312809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115735747374079550936208539 173603621061119326404312809)
  ·
    refine ⟨130202715795839494803234607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173603621061119326404312809 130202715795839494803234607)
    ·
      refine ⟨195304073693759242204851911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130202715795839494803234607 195304073693759242204851911)
      ·
        refine ⟨292956110540638863307277867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195304073693759242204851911 292956110540638863307277867)
        ·
          refine ⟨439434165810958294960916801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292956110540638863307277867 439434165810958294960916801)
          ·
            refine ⟨329575624358218721220687601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439434165810958294960916801 329575624358218721220687601)
            ·
              refine ⟨247181718268664040915515701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329575624358218721220687601 247181718268664040915515701)
              ·
                refine ⟨23173286087687253835829597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247181718268664040915515701 23173286087687253835829597)
                ·
                  refine ⟨8689982282882720188436099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23173286087687253835829597 8689982282882720188436099)
                  ·
                    refine ⟨13034973424324080282654149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8689982282882720188436099 13034973424324080282654149)
                    ·
                      refine ⟨2444057517060765052997653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13034973424324080282654149 2444057517060765052997653)
                      ·
                        rfl

theorem cell23_4759785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_4759785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759785 prefixEnd_4759785 := by exact prefixLift 4759785
  have htrace : WordTrace (prefixWord ++ tailWord_4759785) baseStart_4759785 baseEnd_4759785 := by
    simpa [prefixWord, tailWord_4759785, baseEnd_4759785] using wordTrace_append hprefix tailTrace_4759785
  have hstable : (prefixWord ++ tailWord_4759785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759785).length < 2 ^ (prefixWord ++ tailWord_4759785).sum := by decide
  have hdescent : baseEnd_4759785 < baseStart_4759785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759795 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 6]
def baseStart_4759795 : Nat := 118140960795 + 4759795 * 2 ^ 59
def prefixEnd_4759795 : Nat := 4983230072969 + 3 ^ 40 * 4759795 * 2
def baseEnd_4759795 : Nat := 814687550622436671290869

theorem tailTrace_4759795 : CollatzResearch.WordTrace tailWord_4759795 prefixEnd_4759795 814687550622436671290869 := by
  unfold tailWord_4759795
  simp only [CollatzResearch.WordTrace]
  refine ⟨173603985791083098112176839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115735990527388732074784559 173603985791083098112176839)
  ·
    refine ⟨260405978686624647168265259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173603985791083098112176839 260405978686624647168265259)
    ·
      refine ⟨390608968029936970752397889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260405978686624647168265259 390608968029936970752397889)
      ·
        refine ⟨292956726022452728064298417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390608968029936970752397889 292956726022452728064298417)
        ·
          refine ⟨219717544516839546048223813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292956726022452728064298417 219717544516839546048223813)
          ·
            refine ⟨41197039596907414884041965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219717544516839546048223813 41197039596907414884041965)
            ·
              refine ⟨15448889848840280581515737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41197039596907414884041965 15448889848840280581515737)
              ·
                refine ⟨11586667386630210436136803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15448889848840280581515737 11586667386630210436136803)
                ·
                  refine ⟨17380001079945315654205205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586667386630210436136803 17380001079945315654205205)
                  ·
                    refine ⟨814687550622436671290869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17380001079945315654205205 814687550622436671290869)
                    ·
                      rfl

theorem cell23_4759795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_4759795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759795 prefixEnd_4759795 := by exact prefixLift 4759795
  have htrace : WordTrace (prefixWord ++ tailWord_4759795) baseStart_4759795 baseEnd_4759795 := by
    simpa [prefixWord, tailWord_4759795, baseEnd_4759795] using wordTrace_append hprefix tailTrace_4759795
  have hstable : (prefixWord ++ tailWord_4759795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759795).length < 2 ^ (prefixWord ++ tailWord_4759795).sum := by decide
  have hdescent : baseEnd_4759795 < baseStart_4759795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759819 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 3, 2, 2]
def baseStart_4759819 : Nat := 118140960795 + 4759819 * 2 ^ 59
def prefixEnd_4759819 : Nat := 4983230072969 + 3 ^ 40 * 4759819 * 2
def baseEnd_4759819 : Nat := 2444074975403017919972497

theorem tailTrace_4759819 : CollatzResearch.WordTrace tailWord_4759819 prefixEnd_4759819 2444074975403017919972497 := by
  unfold tailWord_4759819
  simp only [CollatzResearch.WordTrace]
  refine ⟨173604861142996150211050511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115736574095330766807367007 173604861142996150211050511)
  ·
    refine ⟨260407291714494225316575767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173604861142996150211050511 260407291714494225316575767)
    ·
      refine ⟨390610937571741337974863651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260407291714494225316575767 390610937571741337974863651)
      ·
        refine ⟨585916406357612006962295477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390610937571741337974863651 585916406357612006962295477)
        ·
          refine ⟨54929663096026125652715201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 585916406357612006962295477 54929663096026125652715201)
          ·
            refine ⟨41197247322019594239536401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54929663096026125652715201 41197247322019594239536401)
            ·
              refine ⟨30897935491514695679652301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41197247322019594239536401 30897935491514695679652301)
              ·
                refine ⟨11586725809318010879869613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30897935491514695679652301 11586725809318010879869613)
                ·
                  refine ⟨4345022178494254079951105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11586725809318010879869613 4345022178494254079951105)
                  ·
                    refine ⟨3258766633870690559963329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345022178494254079951105 3258766633870690559963329)
                    ·
                      refine ⟨2444074975403017919972497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258766633870690559963329 2444074975403017919972497)
                      ·
                        rfl

theorem cell23_4759819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2, 2].length) (baseStart_4759819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759819 prefixEnd_4759819 := by exact prefixLift 4759819
  have htrace : WordTrace (prefixWord ++ tailWord_4759819) baseStart_4759819 baseEnd_4759819 := by
    simpa [prefixWord, tailWord_4759819, baseEnd_4759819] using wordTrace_append hprefix tailTrace_4759819
  have hstable : (prefixWord ++ tailWord_4759819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759819).length < 2 ^ (prefixWord ++ tailWord_4759819).sum := by decide
  have hdescent : baseEnd_4759819 < baseStart_4759819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759822 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4759822 : Nat := 118140960795 + 4759822 * 2 ^ 59
def prefixEnd_4759822 : Nat := 4983230072969 + 3 ^ 40 * 4759822 * 2
def baseEnd_4759822 : Nat := 2444076515844981408234983

theorem tailTrace_4759822 : CollatzResearch.WordTrace tailWord_4759822 prefixEnd_4759822 2444076515844981408234983 := by
  unfold tailWord_4759822
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700621320248160215426215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115736647041323521148939813 21700621320248160215426215)
  ·
    refine ⟨32550931980372240323139323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21700621320248160215426215 32550931980372240323139323)
    ·
      refine ⟨48826397970558360484708985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32550931980372240323139323 48826397970558360484708985)
      ·
        refine ⟨36619798477918770363531739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48826397970558360484708985 36619798477918770363531739)
        ·
          refine ⟨54929697716878155545297609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36619798477918770363531739 54929697716878155545297609)
          ·
            refine ⟨41197273287658616658973207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54929697716878155545297609 41197273287658616658973207)
            ·
              refine ⟨61795909931487924988459811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41197273287658616658973207 61795909931487924988459811)
              ·
                refine ⟨92693864897231887482689717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61795909931487924988459811 92693864897231887482689717)
                ·
                  refine ⟨8690049834115489451502161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92693864897231887482689717 8690049834115489451502161)
                  ·
                    refine ⟨6517537375586617088626621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8690049834115489451502161 6517537375586617088626621)
                    ·
                      refine ⟨2444076515844981408234983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517537375586617088626621 2444076515844981408234983)
                      ·
                        rfl

theorem cell23_4759822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4759822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759822 prefixEnd_4759822 := by exact prefixLift 4759822
  have htrace : WordTrace (prefixWord ++ tailWord_4759822) baseStart_4759822 baseEnd_4759822 := by
    simpa [prefixWord, tailWord_4759822, baseEnd_4759822] using wordTrace_append hprefix tailTrace_4759822
  have hstable : (prefixWord ++ tailWord_4759822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759822).length < 2 ^ (prefixWord ++ tailWord_4759822).sum := by decide
  have hdescent : baseEnd_4759822 < baseStart_4759822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759825 : List Nat := [1, 2, 2, 1, 1, 5, 3, 8]
def baseStart_4759825 : Nat := 118140960795 + 4759825 * 2 ^ 59
def prefixEnd_4759825 : Nat := 4983230072969 + 3 ^ 40 * 4759825 * 2
def baseEnd_4759825 : Nat := 90521409492109070240647

theorem tailTrace_4759825 : CollatzResearch.WordTrace tailWord_4759825 prefixEnd_4759825 90521409492109070240647 := by
  unfold tailWord_4759825
  simp only [CollatzResearch.WordTrace]
  refine ⟨173605079980974413235768929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115736719987316275490512619 173605079980974413235768929)
  ·
    refine ⟨130203809985730809926826697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173605079980974413235768929 130203809985730809926826697)
    ·
      refine ⟨97652857489298107445120023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130203809985730809926826697 97652857489298107445120023)
      ·
        refine ⟨146479286233947161167680035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97652857489298107445120023 146479286233947161167680035)
        ·
          refine ⟨219718929350920741751520053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146479286233947161167680035 219718929350920741751520053)
          ·
            refine ⟨20598649626648819539205005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219718929350920741751520053 20598649626648819539205005)
            ·
              refine ⟨7724493609993307327201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20598649626648819539205005 7724493609993307327201877)
              ·
                refine ⟨90521409492109070240647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7724493609993307327201877 90521409492109070240647)
                ·
                  rfl

theorem cell23_4759825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 8].length) (baseStart_4759825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759825 prefixEnd_4759825 := by exact prefixLift 4759825
  have htrace : WordTrace (prefixWord ++ tailWord_4759825) baseStart_4759825 baseEnd_4759825 := by
    simpa [prefixWord, tailWord_4759825, baseEnd_4759825] using wordTrace_append hprefix tailTrace_4759825
  have hstable : (prefixWord ++ tailWord_4759825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759825).length < 2 ^ (prefixWord ++ tailWord_4759825).sum := by decide
  have hdescent : baseEnd_4759825 < baseStart_4759825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759832 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4759832 : Nat := 118140960795 + 4759832 * 2 ^ 59
def prefixEnd_4759832 : Nat := 4983230072969 + 3 ^ 40 * 4759832 * 2
def baseEnd_4759832 : Nat := 2444081650651526369109937

theorem tailTrace_4759832 : CollatzResearch.WordTrace tailWord_4759832 prefixEnd_4759832 2444081650651526369109937 := by
  unfold tailWord_4759832
  simp only [CollatzResearch.WordTrace]
  refine ⟨86802667645974526715636875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115736890194632702287515833 86802667645974526715636875)
  ·
    refine ⟨130204001468961790073455313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86802667645974526715636875 130204001468961790073455313)
    ·
      refine ⟨97653001101721342555091485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130204001468961790073455313 97653001101721342555091485)
      ·
        refine ⟨36619875413145503458159307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97653001101721342555091485 36619875413145503458159307)
        ·
          refine ⟨54929813119718255187238961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36619875413145503458159307 54929813119718255187238961)
          ·
            refine ⟨41197359839788691390429221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54929813119718255187238961 41197359839788691390429221)
            ·
              refine ⟨7724504969960379635705479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41197359839788691390429221 7724504969960379635705479)
              ·
                refine ⟨11586757454940569453558219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724504969960379635705479 11586757454940569453558219)
                ·
                  refine ⟨17380136182410854180337329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586757454940569453558219 17380136182410854180337329)
                  ·
                    refine ⟨13035102136808140635252997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17380136182410854180337329 13035102136808140635252997)
                    ·
                      refine ⟨2444081650651526369109937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13035102136808140635252997 2444081650651526369109937)
                      ·
                        rfl

theorem cell23_4759832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4759832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759832 prefixEnd_4759832 := by exact prefixLift 4759832
  have htrace : WordTrace (prefixWord ++ tailWord_4759832) baseStart_4759832 baseEnd_4759832 := by
    simpa [prefixWord, tailWord_4759832, baseEnd_4759832] using wordTrace_append hprefix tailTrace_4759832
  have hstable : (prefixWord ++ tailWord_4759832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759832).length < 2 ^ (prefixWord ++ tailWord_4759832).sum := by decide
  have hdescent : baseEnd_4759832 < baseStart_4759832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759847 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4759847 : Nat := 118140960795 + 4759847 * 2 ^ 59
def prefixEnd_4759847 : Nat := 4983230072969 + 3 ^ 40 * 4759847 * 2
def baseEnd_4759847 : Nat := 2444089352861343810422369

theorem tailTrace_4759847 : CollatzResearch.WordTrace tailWord_4759847 prefixEnd_4759847 2444089352861343810422369 := by
  unfold tailWord_4759847
  simp only [CollatzResearch.WordTrace]
  refine ⟨173605882386894710993069795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115737254924596473995379863 173605882386894710993069795)
  ·
    refine ⟨260408823580342066489604693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173605882386894710993069795 260408823580342066489604693)
    ·
      refine ⟨3051665901332133591675055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 260408823580342066489604693 3051665901332133591675055)
      ·
        refine ⟨4577498851998200387512583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051665901332133591675055 4577498851998200387512583)
        ·
          refine ⟨6866248277997300581268875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577498851998200387512583 6866248277997300581268875)
          ·
            refine ⟨10299372416995950871903313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866248277997300581268875 10299372416995950871903313)
            ·
              refine ⟨7724529312746963153927485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10299372416995950871903313 7724529312746963153927485)
              ·
                refine ⟨2896698492280111182722807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7724529312746963153927485 2896698492280111182722807)
                ·
                  refine ⟨4345047738420166774084211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896698492280111182722807 4345047738420166774084211)
                  ·
                    refine ⟨6517571607630250161126317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4345047738420166774084211 6517571607630250161126317)
                    ·
                      refine ⟨2444089352861343810422369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517571607630250161126317 2444089352861343810422369)
                      ·
                        rfl

theorem cell23_4759847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4759847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759847 prefixEnd_4759847 := by exact prefixLift 4759847
  have htrace : WordTrace (prefixWord ++ tailWord_4759847) baseStart_4759847 baseEnd_4759847 := by
    simpa [prefixWord, tailWord_4759847, baseEnd_4759847] using wordTrace_append hprefix tailTrace_4759847
  have hstable : (prefixWord ++ tailWord_4759847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759847).length < 2 ^ (prefixWord ++ tailWord_4759847).sum := by decide
  have hdescent : baseEnd_4759847 < baseStart_4759847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759852 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_4759852 : Nat := 118140960795 + 4759852 * 2 ^ 59
def prefixEnd_4759852 : Nat := 4983230072969 + 3 ^ 40 * 4759852 * 2
def baseEnd_4759852 : Nat := 2444091920264616290859845

theorem tailTrace_4759852 : CollatzResearch.WordTrace tailWord_4759852 prefixEnd_4759852 2444091920264616290859845 := by
  unfold tailWord_4759852
  simp only [CollatzResearch.WordTrace]
  refine ⟨86803032375938298423500905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115737376501251064564667873 86803032375938298423500905)
  ·
    refine ⟨65102274281953723817625679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86803032375938298423500905 65102274281953723817625679)
    ·
      refine ⟨97653411422930585726438519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65102274281953723817625679 97653411422930585726438519)
      ·
        refine ⟨146480117134395878589657779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97653411422930585726438519 146480117134395878589657779)
        ·
          refine ⟨219720175701593817884486669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146480117134395878589657779 219720175701593817884486669)
          ·
            refine ⟨82395065888097681706682501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219720175701593817884486669 82395065888097681706682501)
            ·
              refine ⟨15449074854018315320002969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82395065888097681706682501 15449074854018315320002969)
              ·
                refine ⟨11586806140513736490002227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15449074854018315320002969 11586806140513736490002227)
                ·
                  refine ⟨17380209210770604735003341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586806140513736490002227 17380209210770604735003341)
                  ·
                    refine ⟨6517578454038976775626253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17380209210770604735003341 6517578454038976775626253)
                    ·
                      refine ⟨2444091920264616290859845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517578454038976775626253 2444091920264616290859845)
                      ·
                        rfl

theorem cell23_4759852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_4759852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759852 prefixEnd_4759852 := by exact prefixLift 4759852
  have htrace : WordTrace (prefixWord ++ tailWord_4759852) baseStart_4759852 baseEnd_4759852 := by
    simpa [prefixWord, tailWord_4759852, baseEnd_4759852] using wordTrace_append hprefix tailTrace_4759852
  have hstable : (prefixWord ++ tailWord_4759852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759852).length < 2 ^ (prefixWord ++ tailWord_4759852).sum := by decide
  have hdescent : baseEnd_4759852 < baseStart_4759852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759875 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4759875 : Nat := 118140960795 + 4759875 * 2 ^ 59
def prefixEnd_4759875 : Nat := 4983230072969 + 3 ^ 40 * 4759875 * 2
def baseEnd_4759875 : Nat := 2444103730319669700872239

theorem tailTrace_4759875 : CollatzResearch.WordTrace tailWord_4759875 prefixEnd_4759875 2444103730319669700872239 := by
  unfold tailWord_4759875
  simp only [CollatzResearch.WordTrace]
  refine ⟨173606903630793271775089079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115737935753862181183392719 173606903630793271775089079)
  ·
    refine ⟨260410355446189907662633619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173606903630793271775089079 260410355446189907662633619)
    ·
      refine ⟨390615533169284861493950429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260410355446189907662633619 390615533169284861493950429)
      ·
        refine ⟨146480824938481823060231411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390615533169284861493950429 146480824938481823060231411)
        ·
          refine ⟨219721237407722734590347117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146480824938481823060231411 219721237407722734590347117)
          ·
            refine ⟨82395464027896025471380169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219721237407722734590347117 82395464027896025471380169)
            ·
              refine ⟨61796598020922019103535127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82395464027896025471380169 61796598020922019103535127)
              ·
                refine ⟨92694897031383028655302691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61796598020922019103535127 92694897031383028655302691)
                ·
                  refine ⟨139042345547074542982954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92694897031383028655302691 139042345547074542982954037)
                  ·
                    refine ⟨13035219895038238404651941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139042345547074542982954037 13035219895038238404651941)
                    ·
                      refine ⟨2444103730319669700872239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13035219895038238404651941 2444103730319669700872239)
                      ·
                        rfl

theorem cell23_4759875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4759875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759875 prefixEnd_4759875 := by exact prefixLift 4759875
  have htrace : WordTrace (prefixWord ++ tailWord_4759875) baseStart_4759875 baseEnd_4759875 := by
    simpa [prefixWord, tailWord_4759875, baseEnd_4759875] using wordTrace_append hprefix tailTrace_4759875
  have hstable : (prefixWord ++ tailWord_4759875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759875).length < 2 ^ (prefixWord ++ tailWord_4759875).sum := by decide
  have hdescent : baseEnd_4759875 < baseStart_4759875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759912 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4759912 : Nat := 118140960795 + 4759912 * 2 ^ 59
def prefixEnd_4759912 : Nat := 4983230072969 + 3 ^ 40 * 4759912 * 2
def baseEnd_4759912 : Nat := 2444122729103886056109569

theorem tailTrace_4759912 : CollatzResearch.WordTrace tailWord_4759912 prefixEnd_4759912 2444122729103886056109569 := by
  unfold tailWord_4759912
  simp only [CollatzResearch.WordTrace]
  refine ⟨86804126565829613547092995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115738835421106151396123993 86804126565829613547092995)
  ·
    refine ⟨130206189848744420320639493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86804126565829613547092995 130206189848744420320639493)
    ·
      refine ⟨24413660596639578810119905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130206189848744420320639493 24413660596639578810119905)
      ·
        refine ⟨18310245447479684107589929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24413660596639578810119905 18310245447479684107589929)
        ·
          refine ⟨13732684085609763080692447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18310245447479684107589929 13732684085609763080692447)
          ·
            refine ⟨20599026128414644621038671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13732684085609763080692447 20599026128414644621038671)
            ·
              refine ⟨30898539192621966931558007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20599026128414644621038671 30898539192621966931558007)
              ·
                refine ⟨46347808788932950397337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30898539192621966931558007 46347808788932950397337011)
                ·
                  refine ⟨69521713183399425596005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46347808788932950397337011 69521713183399425596005517)
                  ·
                    refine ⟨26070642443774784598502069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69521713183399425596005517 26070642443774784598502069)
                    ·
                      refine ⟨2444122729103886056109569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26070642443774784598502069 2444122729103886056109569)
                      ·
                        rfl

theorem cell23_4759912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4759912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759912 prefixEnd_4759912 := by exact prefixLift 4759912
  have htrace : WordTrace (prefixWord ++ tailWord_4759912) baseStart_4759912 baseEnd_4759912 := by
    simpa [prefixWord, tailWord_4759912, baseEnd_4759912] using wordTrace_append hprefix tailTrace_4759912
  have hstable : (prefixWord ++ tailWord_4759912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759912).length < 2 ^ (prefixWord ++ tailWord_4759912).sum := by decide
  have hdescent : baseEnd_4759912 < baseStart_4759912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759972 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_4759972 : Nat := 118140960795 + 4759972 * 2 ^ 59
def prefixEnd_4759972 : Nat := 4983230072969 + 3 ^ 40 * 4759972 * 2
def baseEnd_4759972 : Nat := 2444153537943155821359293

theorem tailTrace_4759972 : CollatzResearch.WordTrace tailWord_4759972 prefixEnd_4759972 2444153537943155821359293 := by
  unfold tailWord_4759972
  simp only [CollatzResearch.WordTrace]
  refine ⟨86805220755720928670685085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115740294340961238227580113 86805220755720928670685085)
  ·
    refine ⟨32551957783395348251506907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86805220755720928670685085 32551957783395348251506907)
    ·
      refine ⟨48827936675093022377260361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32551957783395348251506907 48827936675093022377260361)
      ·
        refine ⟨36620952506319766782945271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48827936675093022377260361 36620952506319766782945271)
        ·
          refine ⟨54931428759479650174417907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36620952506319766782945271 54931428759479650174417907)
          ·
            refine ⟨82397143139219475261626861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54931428759479650174417907 82397143139219475261626861)
            ·
              refine ⟨30898928677207303223110073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82397143139219475261626861 30898928677207303223110073)
              ·
                refine ⟨23174196507905477417332555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30898928677207303223110073 23174196507905477417332555)
                ·
                  refine ⟨34761294761858216125998833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23174196507905477417332555 34761294761858216125998833)
                  ·
                    refine ⟨26070971071393662094499125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34761294761858216125998833 26070971071393662094499125)
                    ·
                      refine ⟨2444153537943155821359293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26070971071393662094499125 2444153537943155821359293)
                      ·
                        rfl

theorem cell23_4759972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_4759972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4759972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4759972 prefixEnd_4759972 := by exact prefixLift 4759972
  have htrace : WordTrace (prefixWord ++ tailWord_4759972) baseStart_4759972 baseEnd_4759972 := by
    simpa [prefixWord, tailWord_4759972, baseEnd_4759972] using wordTrace_append hprefix tailTrace_4759972
  have hstable : (prefixWord ++ tailWord_4759972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759972).length < 2 ^ (prefixWord ++ tailWord_4759972).sum := by decide
  have hdescent : baseEnd_4759972 < baseStart_4759972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760069 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_4760069 : Nat := 118140960795 + 4760069 * 2 ^ 59
def prefixEnd_4760069 : Nat := 4983230072969 + 3 ^ 40 * 4760069 * 2
def baseEnd_4760069 : Nat := 814734448522213980615449

theorem tailTrace_4760069 : CollatzResearch.WordTrace tailWord_4760069 prefixEnd_4760069 814734448522213980615449 := by
  unfold tailWord_4760069
  simp only [CollatzResearch.WordTrace]
  refine ⟨173613979392090442907651261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115742652928060295271767507 173613979392090442907651261)
  ·
    refine ⟨65105242272033916090369223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173613979392090442907651261 65105242272033916090369223)
    ·
      refine ⟨97657863408050874135553835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65105242272033916090369223 97657863408050874135553835)
      ·
        refine ⟨146486795112076311203330753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97657863408050874135553835 146486795112076311203330753)
        ·
          refine ⟨109865096334057233402498065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146486795112076311203330753 109865096334057233402498065)
          ·
            refine ⟨82398822250542925051873549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109865096334057233402498065 82398822250542925051873549)
            ·
              refine ⟨30899558343953596894452581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82398822250542925051873549 30899558343953596894452581)
              ·
                refine ⟨5793667189491299417709859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30899558343953596894452581 5793667189491299417709859)
                ·
                  refine ⟨8690500784236949126564789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793667189491299417709859 8690500784236949126564789)
                  ·
                    refine ⟨814734448522213980615449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8690500784236949126564789 814734448522213980615449)
                    ·
                      rfl

theorem cell23_4760069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_4760069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760069 prefixEnd_4760069 := by exact prefixLift 4760069
  have htrace : WordTrace (prefixWord ++ tailWord_4760069) baseStart_4760069 baseEnd_4760069 := by
    simpa [prefixWord, tailWord_4760069, baseEnd_4760069] using wordTrace_append hprefix tailTrace_4760069
  have hstable : (prefixWord ++ tailWord_4760069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760069).length < 2 ^ (prefixWord ++ tailWord_4760069).sum := by decide
  have hdescent : baseEnd_4760069 < baseStart_4760069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760070 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4760070 : Nat := 118140960795 + 4760070 * 2 ^ 59
def prefixEnd_4760070 : Nat := 4983230072969 + 3 ^ 40 * 4760070 * 2
def baseEnd_4760070 : Nat := 2444203859047296437933843

theorem tailTrace_4760070 : CollatzResearch.WordTrace tailWord_4760070 prefixEnd_4760070 2444203859047296437933843 := by
  unfold tailWord_4760070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425437995783963127451177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115742677243391213385625109 5425437995783963127451177)
  ·
    refine ⟨4069078496837972345588383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5425437995783963127451177 4069078496837972345588383)
    ·
      refine ⟨6103617745256958518382575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4069078496837972345588383 6103617745256958518382575)
      ·
        refine ⟨9155426617885437777573863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6103617745256958518382575 9155426617885437777573863)
        ·
          refine ⟨13733139926828156666360795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9155426617885437777573863 13733139926828156666360795)
          ·
            refine ⟨20599709890242234999541193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733139926828156666360795 20599709890242234999541193)
            ·
              refine ⟨15449782417681676249655895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20599709890242234999541193 15449782417681676249655895)
              ·
                refine ⟨23174673626522514374483843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15449782417681676249655895 23174673626522514374483843)
                ·
                  refine ⟨34762010439783771561725765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23174673626522514374483843 34762010439783771561725765)
                  ·
                    refine ⟨6517876957459457167823581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34762010439783771561725765 6517876957459457167823581)
                    ·
                      refine ⟨2444203859047296437933843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517876957459457167823581 2444203859047296437933843)
                      ·
                        rfl

theorem cell23_4760070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4760070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760070 prefixEnd_4760070 := by exact prefixLift 4760070
  have htrace : WordTrace (prefixWord ++ tailWord_4760070) baseStart_4760070 baseEnd_4760070 := by
    simpa [prefixWord, tailWord_4760070, baseEnd_4760070] using wordTrace_append hprefix tailTrace_4760070
  have hstable : (prefixWord ++ tailWord_4760070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760070).length < 2 ^ (prefixWord ++ tailWord_4760070).sum := by decide
  have hdescent : baseEnd_4760070 < baseStart_4760070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760076 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_4760076 : Nat := 118140960795 + 4760076 * 2 ^ 59
def prefixEnd_4760076 : Nat := 4983230072969 + 3 ^ 40 * 4760076 * 2
def baseEnd_4760076 : Nat := 2444206939931223414458815

theorem tailTrace_4760076 : CollatzResearch.WordTrace tailWord_4760076 prefixEnd_4760076 2444206939931223414458815 := by
  unfold tailWord_4760076
  simp only [CollatzResearch.WordTrace]
  refine ⟨86807117351532541551578041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115742823135376722068770721 86807117351532541551578041)
  ·
    refine ⟨65105338013649406163683531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86807117351532541551578041 65105338013649406163683531)
    ·
      refine ⟨97658007020474109245525297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65105338013649406163683531 97658007020474109245525297)
      ·
        refine ⟨73243505265355581934143973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97658007020474109245525297 73243505265355581934143973)
        ·
          refine ⟨13733157237254171612651995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73243505265355581934143973 13733157237254171612651995)
          ·
            refine ⟨20599735855881257418977993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733157237254171612651995 20599735855881257418977993)
            ·
              refine ⟨15449801891910943064233495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20599735855881257418977993 15449801891910943064233495)
              ·
                refine ⟨23174702837866414596350243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15449801891910943064233495 23174702837866414596350243)
                ·
                  refine ⟨34762054256799621894525365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23174702837866414596350243 34762054256799621894525365)
                  ·
                    refine ⟨3258942586574964552611753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34762054256799621894525365 3258942586574964552611753)
                    ·
                      refine ⟨2444206939931223414458815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258942586574964552611753 2444206939931223414458815)
                      ·
                        rfl

theorem cell23_4760076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_4760076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760076 prefixEnd_4760076 := by exact prefixLift 4760076
  have htrace : WordTrace (prefixWord ++ tailWord_4760076) baseStart_4760076 baseEnd_4760076 := by
    simpa [prefixWord, tailWord_4760076, baseEnd_4760076] using wordTrace_append hprefix tailTrace_4760076
  have hstable : (prefixWord ++ tailWord_4760076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760076).length < 2 ^ (prefixWord ++ tailWord_4760076).sum := by decide
  have hdescent : baseEnd_4760076 < baseStart_4760076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760077 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4760077 : Nat := 118140960795 + 4760077 * 2 ^ 59
def prefixEnd_4760077 : Nat := 4983230072969 + 3 ^ 40 * 4760077 * 2
def baseEnd_4760077 : Nat := 814735817803959303515437

theorem tailTrace_4760077 : CollatzResearch.WordTrace tailWord_4760077 prefixEnd_4760077 814735817803959303515437 := by
  unfold tailWord_4760077
  simp only [CollatzResearch.WordTrace]
  refine ⟨173614271176061460273942485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115742847450707640182628323 173614271176061460273942485)
  ·
    refine ⟨4069084480688940475170527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 173614271176061460273942485 4069084480688940475170527)
    ·
      refine ⟨6103626721033410712755791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4069084480688940475170527 6103626721033410712755791)
      ·
        refine ⟨9155440081550116069133687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6103626721033410712755791 9155440081550116069133687)
        ·
          refine ⟨13733160122325174103700531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9155440081550116069133687 13733160122325174103700531)
          ·
            refine ⟨20599740183487761155550797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733160122325174103700531 20599740183487761155550797)
            ·
              refine ⟨7724902568807910433331549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20599740183487761155550797 7724902568807910433331549)
              ·
                refine ⟨2896838463302966412499331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7724902568807910433331549 2896838463302966412499331)
                ·
                  refine ⟨4345257694954449618748997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896838463302966412499331 4345257694954449618748997)
                  ·
                    refine ⟨814735817803959303515437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345257694954449618748997 814735817803959303515437)
                    ·
                      rfl

theorem cell23_4760077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4760077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760077 prefixEnd_4760077 := by exact prefixLift 4760077
  have htrace : WordTrace (prefixWord ++ tailWord_4760077) baseStart_4760077 baseEnd_4760077 := by
    simpa [prefixWord, tailWord_4760077, baseEnd_4760077] using wordTrace_append hprefix tailTrace_4760077
  have hstable : (prefixWord ++ tailWord_4760077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760077).length < 2 ^ (prefixWord ++ tailWord_4760077).sum := by decide
  have hdescent : baseEnd_4760077 < baseStart_4760077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760089 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 8, 2]
def baseStart_4760089 : Nat := 118140960795 + 4760089 * 2 ^ 59
def prefixEnd_4760089 : Nat := 4983230072969 + 3 ^ 40 * 4760089 * 2
def baseEnd_4760089 : Nat := 2444213615179731863596255

theorem tailTrace_4760089 : CollatzResearch.WordTrace tailWord_4760089 prefixEnd_4760089 2444213615179731863596255 := by
  unfold tailWord_4760089
  simp only [CollatzResearch.WordTrace]
  refine ⟨173614708852017986323379321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115743139234678657548919547 173614708852017986323379321)
  ·
    refine ⟨130211031639013489742534491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173614708852017986323379321 130211031639013489742534491)
    ·
      refine ⟨195316547458520234613801737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130211031639013489742534491 195316547458520234613801737)
      ·
        refine ⟨146487410593890175960351303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195316547458520234613801737 146487410593890175960351303)
        ·
          refine ⟨219731115890835263940526955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146487410593890175960351303 219731115890835263940526955)
          ·
            refine ⟨329596673836252895910790433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219731115890835263940526955 329596673836252895910790433)
            ·
              refine ⟨247197505377189671933092825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329596673836252895910790433 247197505377189671933092825)
              ·
                refine ⟨185398129032892253949819619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247197505377189671933092825 185398129032892253949819619)
                ·
                  refine ⟨278097193549338380924729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185398129032892253949819619 278097193549338380924729429)
                  ·
                    refine ⟨3258951486906309151461673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 278097193549338380924729429 3258951486906309151461673)
                    ·
                      refine ⟨2444213615179731863596255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258951486906309151461673 2444213615179731863596255)
                      ·
                        rfl

theorem cell23_4760089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_4760089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760089 prefixEnd_4760089 := by exact prefixLift 4760089
  have htrace : WordTrace (prefixWord ++ tailWord_4760089) baseStart_4760089 baseEnd_4760089 := by
    simpa [prefixWord, tailWord_4760089, baseEnd_4760089] using wordTrace_append hprefix tailTrace_4760089
  have hstable : (prefixWord ++ tailWord_4760089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760089).length < 2 ^ (prefixWord ++ tailWord_4760089).sum := by decide
  have hdescent : baseEnd_4760089 < baseStart_4760089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760093 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4760093 : Nat := 118140960795 + 4760093 * 2 ^ 59
def prefixEnd_4760093 : Nat := 4983230072969 + 3 ^ 40 * 4760093 * 2
def baseEnd_4760093 : Nat := 2444215669102349847946237

theorem tailTrace_4760093 : CollatzResearch.WordTrace tailWord_4760093 prefixEnd_4760093 2444215669102349847946237 := by
  unfold tailWord_4760093
  simp only [CollatzResearch.WordTrace]
  refine ⟨173614854744003495006524933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115743236496002330004349955 173614854744003495006524933)
  ·
    refine ⟨32552785264500655313723425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173614854744003495006524933 32552785264500655313723425)
    ·
      refine ⟨24414588948375491485292569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32552785264500655313723425 24414588948375491485292569)
      ·
        refine ⟨18310941711281618613969427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24414588948375491485292569 18310941711281618613969427)
        ·
          refine ⟨27466412566922427920954141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18310941711281618613969427 27466412566922427920954141)
          ·
            refine ⟨10299904712595910470357803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27466412566922427920954141 10299904712595910470357803)
            ·
              refine ⟨15449857068893865705536705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10299904712595910470357803 15449857068893865705536705)
              ·
                refine ⟨11587392801670399279152529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15449857068893865705536705 11587392801670399279152529)
                ·
                  refine ⟨8690544601252799459364397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11587392801670399279152529 8690544601252799459364397)
                  ·
                    refine ⟨3258954225469799797261649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8690544601252799459364397 3258954225469799797261649)
                    ·
                      refine ⟨2444215669102349847946237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258954225469799797261649 2444215669102349847946237)
                      ·
                        rfl

theorem cell23_4760093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4760093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760093 prefixEnd_4760093 := by exact prefixLift 4760093
  have htrace : WordTrace (prefixWord ++ tailWord_4760093) baseStart_4760093 baseEnd_4760093 := by
    simpa [prefixWord, tailWord_4760093, baseEnd_4760093] using wordTrace_append hprefix tailTrace_4760093
  have hstable : (prefixWord ++ tailWord_4760093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760093).length < 2 ^ (prefixWord ++ tailWord_4760093).sum := by decide
  have hdescent : baseEnd_4760093 < baseStart_4760093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760112 : List Nat := [2, 1, 1, 1, 2, 3, 3, 10]
def baseStart_4760112 : Nat := 118140960795 + 4760112 * 2 ^ 59
def prefixEnd_4760112 : Nat := 4983230072969 + 3 ^ 40 * 4760112 * 2
def baseEnd_4760112 : Nat := 90526867601288343466987

theorem tailTrace_4760112 : CollatzResearch.WordTrace tailWord_4760112 prefixEnd_4760112 90526867601288343466987 := by
  unfold tailWord_4760112
  simp only [CollatzResearch.WordTrace]
  refine ⟨86807773865467330625733295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115743698487289774167644393 86807773865467330625733295)
  ·
    refine ⟨130211660798200995938599943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86807773865467330625733295 130211660798200995938599943)
    ·
      refine ⟨195317491197301493907899915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130211660798200995938599943 195317491197301493907899915)
      ·
        refine ⟨292976236795952240861849873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195317491197301493907899915 292976236795952240861849873)
        ·
          refine ⟨219732177596964180646387405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292976236795952240861849873 219732177596964180646387405)
          ·
            refine ⟨82399566598861567742395277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219732177596964180646387405 82399566598861567742395277)
            ·
              refine ⟨30899837474573087903398229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82399566598861567742395277 30899837474573087903398229)
              ·
                refine ⟨90526867601288343466987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30899837474573087903398229 90526867601288343466987)
                ·
                  rfl

theorem cell23_4760112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_4760112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760112 prefixEnd_4760112 := by exact prefixLift 4760112
  have htrace : WordTrace (prefixWord ++ tailWord_4760112) baseStart_4760112 baseEnd_4760112 := by
    simpa [prefixWord, tailWord_4760112, baseEnd_4760112] using wordTrace_append hprefix tailTrace_4760112
  have hstable : (prefixWord ++ tailWord_4760112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760112).length < 2 ^ (prefixWord ++ tailWord_4760112).sum := by decide
  have hdescent : baseEnd_4760112 < baseStart_4760112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760119 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_4760119 : Nat := 118140960795 + 4760119 * 2 ^ 59
def prefixEnd_4760119 : Nat := 4983230072969 + 3 ^ 40 * 4760119 * 2
def baseEnd_4760119 : Nat := 2444229019599366746221117

theorem tailTrace_4760119 : CollatzResearch.WordTrace tailWord_4760119 prefixEnd_4760119 2444229019599366746221117 := by
  unfold tailWord_4760119
  simp only [CollatzResearch.WordTrace]
  refine ⟨173615803041909301446971411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115743868694606200964647607 173615803041909301446971411)
  ·
    refine ⟨260423704562863952170457117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173615803041909301446971411 260423704562863952170457117)
    ·
      refine ⟨97658889211073982063921419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260423704562863952170457117 97658889211073982063921419)
      ·
        refine ⟨146488333816610973095882129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97658889211073982063921419 146488333816610973095882129)
        ·
          refine ⟨109866250362458229821911597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146488333816610973095882129 109866250362458229821911597)
          ·
            refine ⟨41199843885921836183216849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109866250362458229821911597 41199843885921836183216849)
            ·
              refine ⟨30899882914441377137412637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41199843885921836183216849 30899882914441377137412637)
              ·
                refine ⟨11587456092915516426529739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30899882914441377137412637 11587456092915516426529739)
                ·
                  refine ⟨17381184139373274639794609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11587456092915516426529739 17381184139373274639794609)
                  ·
                    refine ⟨13035888104529955979845957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17381184139373274639794609 13035888104529955979845957)
                    ·
                      refine ⟨2444229019599366746221117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13035888104529955979845957 2444229019599366746221117)
                      ·
                        rfl

theorem cell23_4760119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_4760119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760119 prefixEnd_4760119 := by exact prefixLift 4760119
  have htrace : WordTrace (prefixWord ++ tailWord_4760119) baseStart_4760119 baseEnd_4760119 := by
    simpa [prefixWord, tailWord_4760119, baseEnd_4760119] using wordTrace_append hprefix tailTrace_4760119
  have hstable : (prefixWord ++ tailWord_4760119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760119).length < 2 ^ (prefixWord ++ tailWord_4760119).sum := by decide
  have hdescent : baseEnd_4760119 < baseStart_4760119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760129 : List Nat := [1, 2, 5, 1, 1, 2, 2, 9]
def baseStart_4760129 : Nat := 118140960795 + 4760129 * 2 ^ 59
def prefixEnd_4760129 : Nat := 4983230072969 + 3 ^ 40 * 4760129 * 2
def baseEnd_4760129 : Nat := 90527190903922655818373

theorem tailTrace_4760129 : CollatzResearch.WordTrace tailWord_4760129 prefixEnd_4760129 90527190903922655818373 := by
  unfold tailWord_4760129
  simp only [CollatzResearch.WordTrace]
  refine ⟨173616167771873073154835441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115744111847915382103223627 173616167771873073154835441)
  ·
    refine ⟨130212125828904804866126581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173616167771873073154835441 130212125828904804866126581)
    ·
      refine ⟨12207386796459825456199367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130212125828904804866126581 12207386796459825456199367)
      ·
        refine ⟨18311080194689738184299051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12207386796459825456199367 18311080194689738184299051)
        ·
          refine ⟨27466620292034607276448577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18311080194689738184299051 27466620292034607276448577)
          ·
            refine ⟨20599965219025955457336433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27466620292034607276448577 20599965219025955457336433)
            ·
              refine ⟨15449973914269466593002325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20599965219025955457336433 15449973914269466593002325)
              ·
                refine ⟨90527190903922655818373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15449973914269466593002325 90527190903922655818373)
                ·
                  rfl

theorem cell23_4760129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 9].length) (baseStart_4760129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760129 prefixEnd_4760129 := by exact prefixLift 4760129
  have htrace : WordTrace (prefixWord ++ tailWord_4760129) baseStart_4760129 baseEnd_4760129 := by
    simpa [prefixWord, tailWord_4760129, baseEnd_4760129] using wordTrace_append hprefix tailTrace_4760129
  have hstable : (prefixWord ++ tailWord_4760129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760129).length < 2 ^ (prefixWord ++ tailWord_4760129).sum := by decide
  have hdescent : baseEnd_4760129 < baseStart_4760129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760139 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3]
def baseStart_4760139 : Nat := 118140960795 + 4760139 * 2 ^ 59
def prefixEnd_4760139 : Nat := 4983230072969 + 3 ^ 40 * 4760139 * 2
def baseEnd_4760139 : Nat := 2444239289212456667971025

theorem tailTrace_4760139 : CollatzResearch.WordTrace tailWord_4760139 prefixEnd_4760139 2444239289212456667971025 := by
  unfold tailWord_4760139
  simp only [CollatzResearch.WordTrace]
  refine ⟨173616532501836844862699471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115744355001224563241799647 173616532501836844862699471)
  ·
    refine ⟨260424798752755267294049207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173616532501836844862699471 260424798752755267294049207)
    ·
      refine ⟨390637198129132900941073811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260424798752755267294049207 390637198129132900941073811)
      ·
        refine ⟨585955797193699351411610717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390637198129132900941073811 585955797193699351411610717)
        ·
          refine ⟨219733423947637256779354019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 585955797193699351411610717 219733423947637256779354019)
          ·
            refine ⟨329600135921455885169031029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219733423947637256779354019 329600135921455885169031029)
            ·
              refine ⟨30900012742636489234596659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329600135921455885169031029 30900012742636489234596659)
              ·
                refine ⟨46350019113954733851894989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30900012742636489234596659 46350019113954733851894989)
                ·
                  refine ⟨17381257167733025194460621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46350019113954733851894989 17381257167733025194460621)
                  ·
                    refine ⟨6517971437899884447922733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17381257167733025194460621 6517971437899884447922733)
                    ·
                      refine ⟨2444239289212456667971025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6517971437899884447922733 2444239289212456667971025)
                      ·
                        rfl

theorem cell23_4760139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].length) (baseStart_4760139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760139 prefixEnd_4760139 := by exact prefixLift 4760139
  have htrace : WordTrace (prefixWord ++ tailWord_4760139) baseStart_4760139 baseEnd_4760139 := by
    simpa [prefixWord, tailWord_4760139, baseEnd_4760139] using wordTrace_append hprefix tailTrace_4760139
  have hstable : (prefixWord ++ tailWord_4760139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760139).length < 2 ^ (prefixWord ++ tailWord_4760139).sum := by decide
  have hdescent : baseEnd_4760139 < baseStart_4760139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760140 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_4760140 : Nat := 118140960795 + 4760140 * 2 ^ 59
def prefixEnd_4760140 : Nat := 4983230072969 + 3 ^ 40 * 4760140 * 2
def baseEnd_4760140 : Nat := 2444239802693111164058521

theorem tailTrace_4760140 : CollatzResearch.WordTrace tailWord_4760140 prefixEnd_4760140 2444239802693111164058521 := by
  unfold tailWord_4760140
  simp only [CollatzResearch.WordTrace]
  refine ⟨86808284487416611016742937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115744379316555481355657249 86808284487416611016742937)
  ·
    refine ⟨65106213365562458262557203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86808284487416611016742937 65106213365562458262557203)
    ·
      refine ⟨97659320048343687393835805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65106213365562458262557203 97659320048343687393835805)
      ·
        refine ⟨36622245018128882772688427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97659320048343687393835805 36622245018128882772688427)
        ·
          refine ⟨54933367527193324159032641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36622245018128882772688427 54933367527193324159032641)
          ·
            refine ⟨41200025645394993119274481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54933367527193324159032641 41200025645394993119274481)
            ·
              refine ⟨30900019234046244839455861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41200025645394993119274481 30900019234046244839455861)
              ·
                refine ⟨2896876803191835453698987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30900019234046244839455861 2896876803191835453698987)
                ·
                  refine ⟨4345315204787753180548481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896876803191835453698987 4345315204787753180548481)
                  ·
                    refine ⟨3258986403590814885411361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345315204787753180548481 3258986403590814885411361)
                    ·
                      refine ⟨2444239802693111164058521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3258986403590814885411361 2444239802693111164058521)
                      ·
                        rfl

theorem cell23_4760140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_4760140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760140 prefixEnd_4760140 := by exact prefixLift 4760140
  have htrace : WordTrace (prefixWord ++ tailWord_4760140) baseStart_4760140 baseEnd_4760140 := by
    simpa [prefixWord, tailWord_4760140, baseEnd_4760140] using wordTrace_append hprefix tailTrace_4760140
  have hstable : (prefixWord ++ tailWord_4760140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760140).length < 2 ^ (prefixWord ++ tailWord_4760140).sum := by decide
  have hdescent : baseEnd_4760140 < baseStart_4760140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760173 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4760173 : Nat := 118140960795 + 4760173 * 2 ^ 59
def prefixEnd_4760173 : Nat := 4983230072969 + 3 ^ 40 * 4760173 * 2
def baseEnd_4760173 : Nat := 2444256747554709534945869

theorem tailTrace_4760173 : CollatzResearch.WordTrace tailWord_4760173 prefixEnd_4760173 2444256747554709534945869 := by
  unfold tailWord_4760173
  simp only [CollatzResearch.WordTrace]
  refine ⟨173617772583713668669437173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115745181722475779112958115 173617772583713668669437173)
  ·
    refine ⟨16276666179723156437759735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173617772583713668669437173 16276666179723156437759735)
    ·
      refine ⟨24414999269584734656639603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16276666179723156437759735 24414999269584734656639603)
      ·
        refine ⟨36622498904377101984959405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24414999269584734656639603 36622498904377101984959405)
        ·
          refine ⟨13733437089141413244359777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36622498904377101984959405 13733437089141413244359777)
          ·
            refine ⟨10300077816856059933269833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13733437089141413244359777 10300077816856059933269833)
            ·
              refine ⟨7725058362642044949952375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10300077816856059933269833 7725058362642044949952375)
              ·
                refine ⟨11587587543963067424928563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725058362642044949952375 11587587543963067424928563)
                ·
                  refine ⟨17381381315944601137392845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11587587543963067424928563 17381381315944601137392845)
                  ·
                    refine ⟨6518017993479225426522317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17381381315944601137392845 6518017993479225426522317)
                    ·
                      refine ⟨2444256747554709534945869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6518017993479225426522317 2444256747554709534945869)
                      ·
                        rfl

theorem cell23_4760173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4760173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760173 prefixEnd_4760173 := by exact prefixLift 4760173
  have htrace : WordTrace (prefixWord ++ tailWord_4760173) baseStart_4760173 baseEnd_4760173 := by
    simpa [prefixWord, tailWord_4760173, baseEnd_4760173] using wordTrace_append hprefix tailTrace_4760173
  have hstable : (prefixWord ++ tailWord_4760173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760173).length < 2 ^ (prefixWord ++ tailWord_4760173).sum := by decide
  have hdescent : baseEnd_4760173 < baseStart_4760173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760194 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4760194 : Nat := 118140960795 + 4760194 * 2 ^ 59
def prefixEnd_4760194 : Nat := 4983230072969 + 3 ^ 40 * 4760194 * 2
def baseEnd_4760194 : Nat := 2444267530648453952783273

theorem tailTrace_4760194 : CollatzResearch.WordTrace tailWord_4760194 prefixEnd_4760194 2444267530648453952783273 := by
  unfold tailWord_4760194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43404634629159397313987909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115745692344425059503967757 43404634629159397313987909)
  ·
    refine ⟨8138368992967386996372733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43404634629159397313987909 8138368992967386996372733)
    ·
      refine ⟨3051888372362770123639775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8138368992967386996372733 3051888372362770123639775)
      ·
        refine ⟨4577832558544155185459663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051888372362770123639775 4577832558544155185459663)
        ·
          refine ⟨6866748837816232778189495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577832558544155185459663 6866748837816232778189495)
          ·
            refine ⟨10300123256724349167284243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866748837816232778189495 10300123256724349167284243)
            ·
              refine ⟨15450184885086523750926365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10300123256724349167284243 15450184885086523750926365)
              ·
                refine ⟨5793819331907446406597387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15450184885086523750926365 5793819331907446406597387)
                ·
                  refine ⟨8690728997861169609896081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793819331907446406597387 8690728997861169609896081)
                  ·
                    refine ⟨6518046748395877207422061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8690728997861169609896081 6518046748395877207422061)
                    ·
                      refine ⟨2444267530648453952783273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6518046748395877207422061 2444267530648453952783273)
                      ·
                        rfl

theorem cell23_4760194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4760194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760194 prefixEnd_4760194 := by exact prefixLift 4760194
  have htrace : WordTrace (prefixWord ++ tailWord_4760194) baseStart_4760194 baseEnd_4760194 := by
    simpa [prefixWord, tailWord_4760194, baseEnd_4760194] using wordTrace_append hprefix tailTrace_4760194
  have hstable : (prefixWord ++ tailWord_4760194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760194).length < 2 ^ (prefixWord ++ tailWord_4760194).sum := by decide
  have hdescent : baseEnd_4760194 < baseStart_4760194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760199 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4760199 : Nat := 118140960795 + 4760199 * 2 ^ 59
def prefixEnd_4760199 : Nat := 4983230072969 + 3 ^ 40 * 4760199 * 2
def baseEnd_4760199 : Nat := 2444270098051726433220749

theorem tailTrace_4760199 : CollatzResearch.WordTrace tailWord_4760199 prefixEnd_4760199 2444270098051726433220749 := by
  unfold tailWord_4760199
  simp only [CollatzResearch.WordTrace]
  refine ⟨173618720881619475109883651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115745813921079650073255767 173618720881619475109883651)
  ·
    refine ⟨260428081322429212664825477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173618720881619475109883651 260428081322429212664825477)
    ·
      refine ⟨48830265247955477374654777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260428081322429212664825477 48830265247955477374654777)
      ·
        refine ⟨36622698935966608030991083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48830265247955477374654777 36622698935966608030991083)
        ·
          refine ⟨54934048403949912046486625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36622698935966608030991083 54934048403949912046486625)
          ·
            refine ⟨41200536302962434034864969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54934048403949912046486625 41200536302962434034864969)
            ·
              refine ⟨30900402227221825526148727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41200536302962434034864969 30900402227221825526148727)
              ·
                refine ⟨46350603340832738289223091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30900402227221825526148727 46350603340832738289223091)
                ·
                  refine ⟨69525905011249107433834637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46350603340832738289223091 69525905011249107433834637)
                  ·
                    refine ⟨26072214379218415287687989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69525905011249107433834637 26072214379218415287687989)
                    ·
                      refine ⟨2444270098051726433220749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26072214379218415287687989 2444270098051726433220749)
                      ·
                        rfl

theorem cell23_4760199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4760199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760199 prefixEnd_4760199 := by exact prefixLift 4760199
  have htrace : WordTrace (prefixWord ++ tailWord_4760199) baseStart_4760199 baseEnd_4760199 := by
    simpa [prefixWord, tailWord_4760199, baseEnd_4760199] using wordTrace_append hprefix tailTrace_4760199
  have hstable : (prefixWord ++ tailWord_4760199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760199).length < 2 ^ (prefixWord ++ tailWord_4760199).sum := by decide
  have hdescent : baseEnd_4760199 < baseStart_4760199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760234 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4760234 : Nat := 118140960795 + 4760234 * 2 ^ 59
def prefixEnd_4760234 : Nat := 4983230072969 + 3 ^ 40 * 4760234 * 2
def baseEnd_4760234 : Nat := 2444288069874633796283089

theorem tailTrace_4760234 : CollatzResearch.WordTrace tailWord_4760234 prefixEnd_4760234 2444288069874633796283089 := by
  unfold tailWord_4760234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43404999359123169021851939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115746664957661784058271837 43404999359123169021851939)
  ·
    refine ⟨65107499038684753532777909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43404999359123169021851939 65107499038684753532777909)
    ·
      refine ⟨6103828034876695643697929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65107499038684753532777909 6103828034876695643697929)
      ·
        refine ⟨4577871026157521732773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103828034876695643697929 4577871026157521732773447)
        ·
          refine ⟨6866806539236282599160171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577871026157521732773447 6866806539236282599160171)
          ·
            refine ⟨10300209808854423898740257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866806539236282599160171 10300209808854423898740257)
            ·
              refine ⟨7725157356640817924055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10300209808854423898740257 7725157356640817924055193)
              ·
                refine ⟨5793868017480613443041395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7725157356640817924055193 5793868017480613443041395)
                ·
                  refine ⟨8690802026220920164562093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793868017480613443041395 8690802026220920164562093)
                  ·
                    refine ⟨3259050759832845061710785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8690802026220920164562093 3259050759832845061710785)
                    ·
                      refine ⟨2444288069874633796283089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259050759832845061710785 2444288069874633796283089)
                      ·
                        rfl

theorem cell23_4760234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4760234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760234 prefixEnd_4760234 := by exact prefixLift 4760234
  have htrace : WordTrace (prefixWord ++ tailWord_4760234) baseStart_4760234 baseEnd_4760234 := by
    simpa [prefixWord, tailWord_4760234, baseEnd_4760234] using wordTrace_append hprefix tailTrace_4760234
  have hstable : (prefixWord ++ tailWord_4760234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760234).length < 2 ^ (prefixWord ++ tailWord_4760234).sum := by decide
  have hdescent : baseEnd_4760234 < baseStart_4760234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760253 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 5]
def baseStart_4760253 : Nat := 118140960795 + 4760253 * 2 ^ 59
def prefixEnd_4760253 : Nat := 4983230072969 + 3 ^ 40 * 4760253 * 2
def baseEnd_4760253 : Nat := 271588647334118802438389

theorem tailTrace_4760253 : CollatzResearch.WordTrace tailWord_4760253 prefixEnd_4760253 271588647334118802438389 := by
  unfold tailWord_4760253
  simp only [CollatzResearch.WordTrace]
  refine ⟨173620690423423842332349413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115747126948949228221566275 173620690423423842332349413)
  ·
    refine ⟨32553879454391970437315515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173620690423423842332349413 32553879454391970437315515)
    ·
      refine ⟨48830819181587955655973273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32553879454391970437315515 48830819181587955655973273)
      ·
        refine ⟨36623114386190966741979955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48830819181587955655973273 36623114386190966741979955)
        ·
          refine ⟨54934671579286450112969933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36623114386190966741979955 54934671579286450112969933)
          ·
            refine ⟨20600501842232418792363725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54934671579286450112969933 20600501842232418792363725)
            ·
              refine ⟨7725188190837157047136397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20600501842232418792363725 7725188190837157047136397)
              ·
                refine ⟨2896945571563933892676149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7725188190837157047136397 2896945571563933892676149)
                ·
                  refine ⟨271588647334118802438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896945571563933892676149 271588647334118802438389)
                  ·
                    rfl

theorem cell23_4760253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_4760253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760253 prefixEnd_4760253 := by exact prefixLift 4760253
  have htrace : WordTrace (prefixWord ++ tailWord_4760253) baseStart_4760253 baseEnd_4760253 := by
    simpa [prefixWord, tailWord_4760253, baseEnd_4760253] using wordTrace_append hprefix tailTrace_4760253
  have hstable : (prefixWord ++ tailWord_4760253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760253).length < 2 ^ (prefixWord ++ tailWord_4760253).sum := by decide
  have hdescent : baseEnd_4760253 < baseStart_4760253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760266 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_4760266 : Nat := 118140960795 + 4760266 * 2 ^ 59
def prefixEnd_4760266 : Nat := 4983230072969 + 3 ^ 40 * 4760266 * 2
def baseEnd_4760266 : Nat := 814768167085192557027647

theorem tailTrace_4760266 : CollatzResearch.WordTrace tailWord_4760266 prefixEnd_4760266 814768167085192557027647 := by
  unfold tailWord_4760266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43405291143094186388143163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115747443048251163701715101 43405291143094186388143163)
  ·
    refine ⟨65107936714641279582214745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43405291143094186388143163 65107936714641279582214745)
    ·
      refine ⟨48830952535980959686661059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65107936714641279582214745 48830952535980959686661059)
      ·
        refine ⟨73246428803971439529991589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48830952535980959686661059 73246428803971439529991589)
        ·
          refine ⟨13733705400744644911873423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73246428803971439529991589 13733705400744644911873423)
          ·
            refine ⟨20600558101116967367810135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733705400744644911873423 20600558101116967367810135)
            ·
              refine ⟨30900837151675451051715203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20600558101116967367810135 30900837151675451051715203)
              ·
                refine ⟨46351255727513176577572805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30900837151675451051715203 46351255727513176577572805)
                ·
                  refine ⟨8690860448908720608294901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46351255727513176577572805 8690860448908720608294901)
                  ·
                    refine ⟨814768167085192557027647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8690860448908720608294901 814768167085192557027647)
                    ·
                      rfl

theorem cell23_4760266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_4760266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760266 prefixEnd_4760266 := by exact prefixLift 4760266
  have htrace : WordTrace (prefixWord ++ tailWord_4760266) baseStart_4760266 baseEnd_4760266 := by
    simpa [prefixWord, tailWord_4760266, baseEnd_4760266] using wordTrace_append hprefix tailTrace_4760266
  have hstable : (prefixWord ++ tailWord_4760266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760266).length < 2 ^ (prefixWord ++ tailWord_4760266).sum := by decide
  have hdescent : baseEnd_4760266 < baseStart_4760266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760270 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_4760270 : Nat := 118140960795 + 4760270 * 2 ^ 59
def prefixEnd_4760270 : Nat := 4983230072969 + 3 ^ 40 * 4760270 * 2
def baseEnd_4760270 : Nat := 271589617242021739492547

theorem tailTrace_4760270 : CollatzResearch.WordTrace tailWord_4760270 prefixEnd_4760270 271589617242021739492547 := by
  unfold tailWord_4760270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21702663808045281779464783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115747540309574836157145509 21702663808045281779464783)
  ·
    refine ⟨32553995712067922669197175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21702663808045281779464783 32553995712067922669197175)
    ·
      refine ⟨48830993568101884003795763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32553995712067922669197175 48830993568101884003795763)
      ·
        refine ⟨73246490352152826005693645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48830993568101884003795763 73246490352152826005693645)
        ·
          refine ⟨27467433882057309752135117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73246490352152826005693645 27467433882057309752135117)
          ·
            refine ⟨10300287705771491157050669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27467433882057309752135117 10300287705771491157050669)
            ·
              refine ⟨3862607889664309183894001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10300287705771491157050669 3862607889664309183894001)
              ·
                refine ⟨2896955917248231887920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862607889664309183894001 2896955917248231887920501)
                ·
                  refine ⟨271589617242021739492547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896955917248231887920501 271589617242021739492547)
                  ·
                    rfl

theorem cell23_4760270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_4760270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760270 prefixEnd_4760270 := by exact prefixLift 4760270
  have htrace : WordTrace (prefixWord ++ tailWord_4760270) baseStart_4760270 baseEnd_4760270 := by
    simpa [prefixWord, tailWord_4760270, baseEnd_4760270] using wordTrace_append hprefix tailTrace_4760270
  have hstable : (prefixWord ++ tailWord_4760270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760270).length < 2 ^ (prefixWord ++ tailWord_4760270).sum := by decide
  have hdescent : baseEnd_4760270 < baseStart_4760270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760299 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_4760299 : Nat := 118140960795 + 4760299 * 2 ^ 59
def prefixEnd_4760299 : Nat := 4983230072969 + 3 ^ 40 * 4760299 * 2
def baseEnd_4760299 : Nat := 2444321446117176041970289

theorem tailTrace_4760299 : CollatzResearch.WordTrace tailWord_4760299 prefixEnd_4760299 2444321446117176041970289 := by
  unfold tailWord_4760299
  simp only [CollatzResearch.WordTrace]
  refine ⟨173622368181257192188523951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115748245454171461459015967 173622368181257192188523951)
  ·
    refine ⟨260433552271885788282785927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173622368181257192188523951 260433552271885788282785927)
    ·
      refine ⟨390650328407828682424178891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260433552271885788282785927 390650328407828682424178891)
      ·
        refine ⟨585975492611743023636268337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390650328407828682424178891 585975492611743023636268337)
        ·
          refine ⟨439481619458807267727201253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585975492611743023636268337 439481619458807267727201253)
          ·
            refine ⟨82402803648526362698850235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 439481619458807267727201253 82402803648526362698850235)
            ·
              refine ⟨123604205472789544048275353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82402803648526362698850235 123604205472789544048275353)
              ·
                refine ⟨92703154104592158036206515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123604205472789544048275353 92703154104592158036206515)
                ·
                  refine ⟨139054731156888237054309773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92703154104592158036206515 139054731156888237054309773)
                  ·
                    refine ⟨52145524183833088895366165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139054731156888237054309773 52145524183833088895366165)
                    ·
                      refine ⟨2444321446117176041970289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52145524183833088895366165 2444321446117176041970289)
                      ·
                        rfl

theorem cell23_4760299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_4760299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760299 prefixEnd_4760299 := by exact prefixLift 4760299
  have htrace : WordTrace (prefixWord ++ tailWord_4760299) baseStart_4760299 baseEnd_4760299 := by
    simpa [prefixWord, tailWord_4760299, baseEnd_4760299] using wordTrace_append hprefix tailTrace_4760299
  have hstable : (prefixWord ++ tailWord_4760299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760299).length < 2 ^ (prefixWord ++ tailWord_4760299).sum := by decide
  have hdescent : baseEnd_4760299 < baseStart_4760299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760303 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_4760303 : Nat := 118140960795 + 4760303 * 2 ^ 59
def prefixEnd_4760303 : Nat := 4983230072969 + 3 ^ 40 * 4760303 * 2
def baseEnd_4760303 : Nat := 2444323500039794026320271

theorem tailTrace_4760303 : CollatzResearch.WordTrace tailWord_4760303 prefixEnd_4760303 2444323500039794026320271 := by
  unfold tailWord_4760303
  simp only [CollatzResearch.WordTrace]
  refine ⟨173622514073242700871669563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115748342715495133914446375 173622514073242700871669563)
  ·
    refine ⟨260433771109864051307504345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173622514073242700871669563 260433771109864051307504345)
    ·
      refine ⟨195325328332398038480628259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260433771109864051307504345 195325328332398038480628259)
      ·
        refine ⟨292987992498597057720942389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195325328332398038480628259 292987992498597057720942389)
        ·
          refine ⟨27467624296743474161338349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292987992498597057720942389 27467624296743474161338349)
          ·
            refine ⟨10300359111278802810501881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27467624296743474161338349 10300359111278802810501881)
            ·
              refine ⟨7725269333459102107876411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10300359111278802810501881 7725269333459102107876411)
              ·
                refine ⟨11587904000188653161814617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725269333459102107876411 11587904000188653161814617)
                ·
                  refine ⟨8690928000141489871360963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11587904000188653161814617 8690928000141489871360963)
                  ·
                    refine ⟨13036392000212234807041445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8690928000141489871360963 13036392000212234807041445)
                    ·
                      refine ⟨2444323500039794026320271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13036392000212234807041445 2444323500039794026320271)
                      ·
                        rfl

theorem cell23_4760303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_4760303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760303 prefixEnd_4760303 := by exact prefixLift 4760303
  have htrace : WordTrace (prefixWord ++ tailWord_4760303) baseStart_4760303 baseEnd_4760303 := by
    simpa [prefixWord, tailWord_4760303, baseEnd_4760303] using wordTrace_append hprefix tailTrace_4760303
  have hstable : (prefixWord ++ tailWord_4760303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760303).length < 2 ^ (prefixWord ++ tailWord_4760303).sum := by decide
  have hdescent : baseEnd_4760303 < baseStart_4760303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760330 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_4760330 : Nat := 118140960795 + 4760330 * 2 ^ 59
def prefixEnd_4760330 : Nat := 4983230072969 + 3 ^ 40 * 4760330 * 2
def baseEnd_4760330 : Nat := 814779121339155140227549

theorem tailTrace_4760330 : CollatzResearch.WordTrace tailWord_4760330 prefixEnd_4760330 814779121339155140227549 := by
  unfold tailWord_4760330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43405874711036221120725611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115748999229429922988601629 43405874711036221120725611)
  ·
    refine ⟨65108812066554331681088417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43405874711036221120725611 65108812066554331681088417)
    ·
      refine ⟨48831609049915748760816313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65108812066554331681088417 48831609049915748760816313)
      ·
        refine ⟨36623706787436811570612235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48831609049915748760816313 36623706787436811570612235)
        ·
          refine ⟨54935560181155217355918353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36623706787436811570612235 54935560181155217355918353)
          ·
            refine ⟨41201670135866413016938765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54935560181155217355918353 41201670135866413016938765)
            ·
              refine ⟨15450626300949904881352037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41201670135866413016938765 15450626300949904881352037)
              ·
                refine ⟨2896992431428107165253507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15450626300949904881352037 2896992431428107165253507)
                ·
                  refine ⟨4345488647142160747880261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896992431428107165253507 4345488647142160747880261)
                  ·
                    refine ⟨814779121339155140227549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345488647142160747880261 814779121339155140227549)
                    ·
                      rfl

theorem cell23_4760330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_4760330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760330 prefixEnd_4760330 := by exact prefixLift 4760330
  have htrace : WordTrace (prefixWord ++ tailWord_4760330) baseStart_4760330 baseEnd_4760330 := by
    simpa [prefixWord, tailWord_4760330, baseEnd_4760330] using wordTrace_append hprefix tailTrace_4760330
  have hstable : (prefixWord ++ tailWord_4760330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760330).length < 2 ^ (prefixWord ++ tailWord_4760330).sum := by decide
  have hdescent : baseEnd_4760330 < baseStart_4760330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760403 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 2, 4]
def baseStart_4760403 : Nat := 118140960795 + 4760403 * 2 ^ 59
def prefixEnd_4760403 : Nat := 4983230072969 + 3 ^ 40 * 4760403 * 2
def baseEnd_4760403 : Nat := 814791616035081211689937

theorem tailTrace_4760403 : CollatzResearch.WordTrace tailWord_4760403 prefixEnd_4760403 814791616035081211689937 := by
  unfold tailWord_4760403
  simp only [CollatzResearch.WordTrace]
  refine ⟨173626161372880417950309863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115750774248586945300206575 173626161372880417950309863)
  ·
    refine ⟨260439242059320626925464795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173626161372880417950309863 260439242059320626925464795)
    ·
      refine ⟨390658863088980940388197193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260439242059320626925464795 390658863088980940388197193)
      ·
        refine ⟨292994147316735705291147895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390658863088980940388197193 292994147316735705291147895)
        ·
          refine ⟨439491220975103557936721843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292994147316735705291147895 439491220975103557936721843)
          ·
            refine ⟨659236831462655336905082765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439491220975103557936721843 659236831462655336905082765)
            ·
              refine ⟨247213811798495751339406037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 659236831462655336905082765 247213811798495751339406037)
              ·
                refine ⟨5794073714027244172017329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 247213811798495751339406037 5794073714027244172017329)
                ·
                  refine ⟨4345555285520433129012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794073714027244172017329 4345555285520433129012997)
                  ·
                    refine ⟨814791616035081211689937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345555285520433129012997 814791616035081211689937)
                    ·
                      rfl

theorem cell23_4760403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 4].length) (baseStart_4760403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760403 prefixEnd_4760403 := by exact prefixLift 4760403
  have htrace : WordTrace (prefixWord ++ tailWord_4760403) baseStart_4760403 baseEnd_4760403 := by
    simpa [prefixWord, tailWord_4760403, baseEnd_4760403] using wordTrace_append hprefix tailTrace_4760403
  have hstable : (prefixWord ++ tailWord_4760403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760403).length < 2 ^ (prefixWord ++ tailWord_4760403).sum := by decide
  have hdescent : baseEnd_4760403 < baseStart_4760403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760410 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_4760410 : Nat := 118140960795 + 4760410 * 2 ^ 59
def prefixEnd_4760410 : Nat := 4983230072969 + 3 ^ 40 * 4760410 * 2
def baseEnd_4760410 : Nat := 2444378442469825107682279

theorem tailTrace_4760410 : CollatzResearch.WordTrace tailWord_4760410 prefixEnd_4760410 2444378442469825107682279 := by
  unfold tailWord_4760410
  simp only [CollatzResearch.WordTrace]
  refine ⟨43406604170963764536453671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115750944455903372097209789 43406604170963764536453671)
  ·
    refine ⟨65109906256445646804680507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43406604170963764536453671 65109906256445646804680507)
    ·
      refine ⟨97664859384668470207020761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65109906256445646804680507 97664859384668470207020761)
      ·
        refine ⟨73248644538501352655265571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97664859384668470207020761 73248644538501352655265571)
        ·
          refine ⟨109872966807752028982898357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73248644538501352655265571 109872966807752028982898357)
          ·
            refine ⟨10300590638226752717146721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109872966807752028982898357 10300590638226752717146721)
            ·
              refine ⟨7725442978670064537860041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10300590638226752717146721 7725442978670064537860041)
              ·
                refine ⟨5794082234002548403395031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7725442978670064537860041 5794082234002548403395031)
                ·
                  refine ⟨8691123351003822605092547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5794082234002548403395031 8691123351003822605092547)
                  ·
                    refine ⟨13036685026505733907638821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8691123351003822605092547 13036685026505733907638821)
                    ·
                      refine ⟨2444378442469825107682279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13036685026505733907638821 2444378442469825107682279)
                      ·
                        rfl

theorem cell23_4760410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_4760410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760410 prefixEnd_4760410 := by exact prefixLift 4760410
  have htrace : WordTrace (prefixWord ++ tailWord_4760410) baseStart_4760410 baseEnd_4760410 := by
    simpa [prefixWord, tailWord_4760410, baseEnd_4760410] using wordTrace_append hprefix tailTrace_4760410
  have hstable : (prefixWord ++ tailWord_4760410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760410).length < 2 ^ (prefixWord ++ tailWord_4760410).sum := by decide
  have hdescent : baseEnd_4760410 < baseStart_4760410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760416 : List Nat := [2, 1, 1, 3, 3, 1, 3, 9]
def baseStart_4760416 : Nat := 118140960795 + 4760416 * 2 ^ 59
def prefixEnd_4760416 : Nat := 4983230072969 + 3 ^ 40 * 4760416 * 2
def baseEnd_4760416 : Nat := 90532649013101929044713

theorem tailTrace_4760416 : CollatzResearch.WordTrace tailWord_4760416 prefixEnd_4760416 90532649013101929044713 := by
  unfold tailWord_4760416
  simp only [CollatzResearch.WordTrace]
  refine ⟨86813317760916660585266551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115751090347888880780355401 86813317760916660585266551)
  ·
    refine ⟨130219976641374990877899827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86813317760916660585266551 130219976641374990877899827)
    ·
      refine ⟨195329964962062486316849741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130219976641374990877899827 195329964962062486316849741)
      ·
        refine ⟨73248736860773432368818653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195329964962062486316849741 73248736860773432368818653)
        ·
          refine ⟨27468276322790037138306995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73248736860773432368818653 27468276322790037138306995)
          ·
            refine ⟨41202414484185055707460493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27468276322790037138306995 41202414484185055707460493)
            ·
              refine ⟨15450905431569395890297685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41202414484185055707460493 15450905431569395890297685)
              ·
                refine ⟨90532649013101929044713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15450905431569395890297685 90532649013101929044713)
                ·
                  rfl

theorem cell23_4760416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_4760416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760416 prefixEnd_4760416 := by exact prefixLift 4760416
  have htrace : WordTrace (prefixWord ++ tailWord_4760416) baseStart_4760416 baseEnd_4760416 := by
    simpa [prefixWord, tailWord_4760416, baseEnd_4760416] using wordTrace_append hprefix tailTrace_4760416
  have hstable : (prefixWord ++ tailWord_4760416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760416).length < 2 ^ (prefixWord ++ tailWord_4760416).sum := by decide
  have hdescent : baseEnd_4760416 < baseStart_4760416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760503 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_4760503 : Nat := 118140960795 + 4760503 * 2 ^ 59
def prefixEnd_4760503 : Nat := 4983230072969 + 3 ^ 40 * 4760503 * 2
def baseEnd_4760503 : Nat := 2444426196170693243819351

theorem tailTrace_4760503 : CollatzResearch.WordTrace tailWord_4760503 prefixEnd_4760503 2444426196170693243819351 := by
  unfold tailWord_4760503
  simp only [CollatzResearch.WordTrace]
  refine ⟨173629808672518135028950163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115753205781678756685966775 173629808672518135028950163)
  ·
    refine ⟨260444713008777202543425245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173629808672518135028950163 260444713008777202543425245)
    ·
      refine ⟨97666767378291450953784467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260444713008777202543425245 97666767378291450953784467)
      ·
        refine ⟨146500151067437176430676701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97666767378291450953784467 146500151067437176430676701)
        ·
          refine ⟨54937556650288941161503763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146500151067437176430676701 54937556650288941161503763)
          ·
            refine ⟨82406334975433411742255645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54937556650288941161503763 82406334975433411742255645)
            ·
              refine ⟨30902375615787529403345867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82406334975433411742255645 30902375615787529403345867)
              ·
                refine ⟨46353563423681294105018801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30902375615787529403345867 46353563423681294105018801)
                ·
                  refine ⟨34765172567760970578764101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46353563423681294105018801 34765172567760970578764101)
                  ·
                    refine ⟨6518469856455181983518269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34765172567760970578764101 6518469856455181983518269)
                    ·
                      refine ⟨2444426196170693243819351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6518469856455181983518269 2444426196170693243819351)
                      ·
                        rfl

theorem cell23_4760503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_4760503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760503 prefixEnd_4760503 := by exact prefixLift 4760503
  have htrace : WordTrace (prefixWord ++ tailWord_4760503) baseStart_4760503 baseEnd_4760503 := by
    simpa [prefixWord, tailWord_4760503, baseEnd_4760503] using wordTrace_append hprefix tailTrace_4760503
  have hstable : (prefixWord ++ tailWord_4760503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760503).length < 2 ^ (prefixWord ++ tailWord_4760503).sum := by decide
  have hdescent : baseEnd_4760503 < baseStart_4760503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760523 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 7]
def baseStart_4760523 : Nat := 118140960795 + 4760523 * 2 ^ 59
def prefixEnd_4760523 : Nat := 4983230072969 + 3 ^ 40 * 4760523 * 2
def baseEnd_4760523 : Nat := 271604051753753685063251

theorem tailTrace_4760523 : CollatzResearch.WordTrace tailWord_4760523 prefixEnd_4760523 271604051753753685063251 := by
  unfold tailWord_4760523
  simp only [CollatzResearch.WordTrace]
  refine ⟨173630538132445678444678223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115753692088297118963118815 173630538132445678444678223)
  ·
    refine ⟨260445807198668517667017335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173630538132445678444678223 260445807198668517667017335)
    ·
      refine ⟨390668710798002776500526003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260445807198668517667017335 390668710798002776500526003)
      ·
        refine ⟨586003066197004164750789005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390668710798002776500526003 586003066197004164750789005)
        ·
          refine ⟨219751149823876561781545877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 586003066197004164750789005 219751149823876561781545877)
          ·
            refine ⟨10300835147994213833509963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219751149823876561781545877 10300835147994213833509963)
            ·
              refine ⟨15451252721991320750264945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10300835147994213833509963 15451252721991320750264945)
              ·
                refine ⟨11588439541493490562698709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15451252721991320750264945 11588439541493490562698709)
                ·
                  refine ⟨271604051753753685063251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11588439541493490562698709 271604051753753685063251)
                  ·
                    rfl

theorem cell23_4760523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 7].length) (baseStart_4760523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760523 prefixEnd_4760523 := by exact prefixLift 4760523
  have htrace : WordTrace (prefixWord ++ tailWord_4760523) baseStart_4760523 baseEnd_4760523 := by
    simpa [prefixWord, tailWord_4760523, baseEnd_4760523] using wordTrace_append hprefix tailTrace_4760523
  have hstable : (prefixWord ++ tailWord_4760523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760523).length < 2 ^ (prefixWord ++ tailWord_4760523).sum := by decide
  have hdescent : baseEnd_4760523 < baseStart_4760523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760534 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4760534 : Nat := 118140960795 + 4760534 * 2 ^ 59
def prefixEnd_4760534 : Nat := 4983230072969 + 3 ^ 40 * 4760534 * 2
def baseEnd_4760534 : Nat := 2444442114070982622531709

theorem tailTrace_4760534 : CollatzResearch.WordTrace tailWord_4760534 prefixEnd_4760534 2444442114070982622531709 := by
  unfold tailWord_4760534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851933708462864207708041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115753959556937218215552437 10851933708462864207708041)
  ·
    refine ⟨8138950281347148155781031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10851933708462864207708041 8138950281347148155781031)
    ·
      refine ⟨12208425422020722233671547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8138950281347148155781031 12208425422020722233671547)
      ·
        refine ⟨18312638133031083350507321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12208425422020722233671547 18312638133031083350507321)
        ·
          refine ⟨13734478599773312512880491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18312638133031083350507321 13734478599773312512880491)
          ·
            refine ⟨20601717899659968769320737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13734478599773312512880491 20601717899659968769320737)
            ·
              refine ⟨15451288424744976576990553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20601717899659968769320737 15451288424744976576990553)
              ·
                refine ⟨11588466318558732432742915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15451288424744976576990553 11588466318558732432742915)
                ·
                  refine ⟨17382699477838098649114373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11588466318558732432742915 17382699477838098649114373)
                  ·
                    refine ⟨3259256152094643496708945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17382699477838098649114373 3259256152094643496708945)
                    ·
                      refine ⟨2444442114070982622531709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259256152094643496708945 2444442114070982622531709)
                      ·
                        rfl

theorem cell23_4760534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4760534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760534 prefixEnd_4760534 := by exact prefixLift 4760534
  have htrace : WordTrace (prefixWord ++ tailWord_4760534) baseStart_4760534 baseEnd_4760534 := by
    simpa [prefixWord, tailWord_4760534, baseEnd_4760534] using wordTrace_append hprefix tailTrace_4760534
  have hstable : (prefixWord ++ tailWord_4760534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760534).length < 2 ^ (prefixWord ++ tailWord_4760534).sum := by decide
  have hdescent : baseEnd_4760534 < baseStart_4760534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760551 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4760551 : Nat := 118140960795 + 4760551 * 2 ^ 59
def prefixEnd_4760551 : Nat := 4983230072969 + 3 ^ 40 * 4760551 * 2
def baseEnd_4760551 : Nat := 2444450843242109056019131

theorem tailTrace_4760551 : CollatzResearch.WordTrace tailWord_4760551 prefixEnd_4760551 2444450843242109056019131 := by
  unfold tailWord_4760551
  simp only [CollatzResearch.WordTrace]
  refine ⟨173631559376344239226697507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115754372917562826151131671 173631559376344239226697507)
  ·
    refine ⟨260447339064516358840046261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173631559376344239226697507 260447339064516358840046261)
    ·
      refine ⟨24416938037298408641254337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260447339064516358840046261 24416938037298408641254337)
      ·
        refine ⟨18312703527973806480940753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24416938037298408641254337 18312703527973806480940753)
        ·
          refine ⟨13734527645980354860705565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18312703527973806480940753 13734527645980354860705565)
          ·
            refine ⟨5150447867242633072764587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13734527645980354860705565 5150447867242633072764587)
            ·
              refine ⟨7725671800863949609146881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150447867242633072764587 7725671800863949609146881)
              ·
                refine ⟨5794253850647962206860161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7725671800863949609146881 5794253850647962206860161)
                ·
                  refine ⟨4345690387985971655145121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794253850647962206860161 4345690387985971655145121)
                  ·
                    refine ⟨3259267790989478741358841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345690387985971655145121 3259267790989478741358841)
                    ·
                      refine ⟨2444450843242109056019131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259267790989478741358841 2444450843242109056019131)
                      ·
                        rfl

theorem cell23_4760551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4760551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760551 prefixEnd_4760551 := by exact prefixLift 4760551
  have htrace : WordTrace (prefixWord ++ tailWord_4760551) baseStart_4760551 baseEnd_4760551 := by
    simpa [prefixWord, tailWord_4760551, baseEnd_4760551] using wordTrace_append hprefix tailTrace_4760551
  have hstable : (prefixWord ++ tailWord_4760551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760551).length < 2 ^ (prefixWord ++ tailWord_4760551).sum := by decide
  have hdescent : baseEnd_4760551 < baseStart_4760551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760583 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 8]
def baseStart_4760583 : Nat := 118140960795 + 4760583 * 2 ^ 59
def prefixEnd_4760583 : Nat := 4983230072969 + 3 ^ 40 * 4760583 * 2
def baseEnd_4760583 : Nat := 814822424874350976939661

theorem tailTrace_4760583 : CollatzResearch.WordTrace tailWord_4760583 prefixEnd_4760583 814822424874350976939661 := by
  unfold tailWord_4760583
  simp only [CollatzResearch.WordTrace]
  refine ⟨173632726512228308691862403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115755151008152205794574935 173632726512228308691862403)
  ·
    refine ⟨260449089768342463037793605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173632726512228308691862403 260449089768342463037793605)
    ·
      refine ⟨48834204331564211819586301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260449089768342463037793605 48834204331564211819586301)
      ·
        refine ⟨18312826624336579432344863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48834204331564211819586301 18312826624336579432344863)
        ·
          refine ⟨27469239936504869148517295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18312826624336579432344863 27469239936504869148517295)
          ·
            refine ⟨41203859904757303722775943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27469239936504869148517295 41203859904757303722775943)
            ·
              refine ⟨61805789857135955584163915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41203859904757303722775943 61805789857135955584163915)
              ·
                refine ⟨92708684785703933376245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61805789857135955584163915 92708684785703933376245873)
                ·
                  refine ⟨69531513589277950032184405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92708684785703933376245873 69531513589277950032184405)
                  ·
                    refine ⟨814822424874350976939661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69531513589277950032184405 814822424874350976939661)
                    ·
                      rfl

theorem cell23_4760583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_4760583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760583 prefixEnd_4760583 := by exact prefixLift 4760583
  have htrace : WordTrace (prefixWord ++ tailWord_4760583) baseStart_4760583 baseEnd_4760583 := by
    simpa [prefixWord, tailWord_4760583, baseEnd_4760583] using wordTrace_append hprefix tailTrace_4760583
  have hstable : (prefixWord ++ tailWord_4760583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760583).length < 2 ^ (prefixWord ++ tailWord_4760583).sum := by decide
  have hdescent : baseEnd_4760583 < baseStart_4760583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760590 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4760590 : Nat := 118140960795 + 4760590 * 2 ^ 59
def prefixEnd_4760590 : Nat := 4983230072969 + 3 ^ 40 * 4760590 * 2
def baseEnd_4760590 : Nat := 2444470868987634403431451

theorem tailTrace_4760590 : CollatzResearch.WordTrace tailWord_4760590 prefixEnd_4760590 2444470868987634403431451 := by
  unfold tailWord_4760590
  simp only [CollatzResearch.WordTrace]
  refine ⟨21704122727900368610920903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115755321215468632591578149 21704122727900368610920903)
  ·
    refine ⟨32556184091850552916381355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21704122727900368610920903 32556184091850552916381355)
    ·
      refine ⟨48834276137775829374572033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32556184091850552916381355 48834276137775829374572033)
      ·
        refine ⟨36625707103331872030929025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48834276137775829374572033 36625707103331872030929025)
        ·
          refine ⟨27469280327498904023196769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36625707103331872030929025 27469280327498904023196769)
          ·
            refine ⟨20601960245624178017397577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27469280327498904023196769 20601960245624178017397577)
            ·
              refine ⟨15451470184218133513048183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20601960245624178017397577 15451470184218133513048183)
              ·
                refine ⟨23177205276327200269572275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15451470184218133513048183 23177205276327200269572275)
                ·
                  refine ⟨34765807914490800404358413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23177205276327200269572275 34765807914490800404358413)
                  ·
                    refine ⟨13037177967934050151634405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34765807914490800404358413 13037177967934050151634405)
                    ·
                      refine ⟨2444470868987634403431451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13037177967934050151634405 2444470868987634403431451)
                      ·
                        rfl

theorem cell23_4760590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4760590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760590 prefixEnd_4760590 := by exact prefixLift 4760590
  have htrace : WordTrace (prefixWord ++ tailWord_4760590) baseStart_4760590 baseEnd_4760590 := by
    simpa [prefixWord, tailWord_4760590, baseEnd_4760590] using wordTrace_append hprefix tailTrace_4760590
  have hstable : (prefixWord ++ tailWord_4760590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760590).length < 2 ^ (prefixWord ++ tailWord_4760590).sum := by decide
  have hdescent : baseEnd_4760590 < baseStart_4760590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760613 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 8]
def baseStart_4760613 : Nat := 118140960795 + 4760613 * 2 ^ 59
def prefixEnd_4760613 : Nat := 4983230072969 + 3 ^ 40 * 4760613 * 2
def baseEnd_4760613 : Nat := 271609186560298645938205

theorem tailTrace_4760613 : CollatzResearch.WordTrace tailWord_4760613 prefixEnd_4760613 271609186560298645938205 := by
  unfold tailWord_4760613
  simp only [CollatzResearch.WordTrace]
  refine ⟨173633820702119623815454493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115755880468079749210302995 173633820702119623815454493)
  ·
    refine ⟨65112682763294858930795435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173633820702119623815454493 65112682763294858930795435)
    ·
      refine ⟨97669024144942288396193153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65112682763294858930795435 97669024144942288396193153)
      ·
        refine ⟨73251768108706716297144865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97669024144942288396193153 73251768108706716297144865)
        ·
          refine ⟨54938826081530037222858649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73251768108706716297144865 54938826081530037222858649)
          ·
            refine ⟨41204119561147527917143987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54938826081530037222858649 41204119561147527917143987)
            ·
              refine ⟨61806179341721291875715981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41204119561147527917143987 61806179341721291875715981)
              ·
                refine ⟨23177317253145484453393493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61806179341721291875715981 23177317253145484453393493)
                ·
                  refine ⟨271609186560298645938205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23177317253145484453393493 271609186560298645938205)
                  ·
                    rfl

theorem cell23_4760613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_4760613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760613 prefixEnd_4760613 := by exact prefixLift 4760613
  have htrace : WordTrace (prefixWord ++ tailWord_4760613) baseStart_4760613 baseEnd_4760613 := by
    simpa [prefixWord, tailWord_4760613, baseEnd_4760613] using wordTrace_append hprefix tailTrace_4760613
  have hstable : (prefixWord ++ tailWord_4760613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760613).length < 2 ^ (prefixWord ++ tailWord_4760613).sum := by decide
  have hdescent : baseEnd_4760613 < baseStart_4760613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760714 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_4760714 : Nat := 118140960795 + 4760714 * 2 ^ 59
def prefixEnd_4760714 : Nat := 4983230072969 + 3 ^ 40 * 4760714 * 2
def baseEnd_4760714 : Nat := 2444534540588791918280881

theorem tailTrace_4760714 : CollatzResearch.WordTrace tailWord_4760714 prefixEnd_4760714 2444534540588791918280881 := by
  unfold tailWord_4760714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43409376118688429516220299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115758336316502478709920797 43409376118688429516220299)
  ·
    refine ⟨65114064178032644274330449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43409376118688429516220299 65114064178032644274330449)
    ·
      refine ⟨48835548133524483205747837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65114064178032644274330449 48835548133524483205747837)
      ·
        refine ⟨18313330550071681202155439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48835548133524483205747837 18313330550071681202155439)
        ·
          refine ⟨27469995825107521803233159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18313330550071681202155439 27469995825107521803233159)
          ·
            refine ⟨41204993737661282704849739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27469995825107521803233159 41204993737661282704849739)
            ·
              refine ⟨61807490606491924057274609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41204993737661282704849739 61807490606491924057274609)
              ·
                refine ⟨46355617954868943042955957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61807490606491924057274609 46355617954868943042955957)
                ·
                  refine ⟨4345839183268963410277121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46355617954868943042955957 4345839183268963410277121)
                  ·
                    refine ⟨3259379387451722557707841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345839183268963410277121 3259379387451722557707841)
                    ·
                      refine ⟨2444534540588791918280881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259379387451722557707841 2444534540588791918280881)
                      ·
                        rfl

theorem cell23_4760714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_4760714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760714 prefixEnd_4760714 := by exact prefixLift 4760714
  have htrace : WordTrace (prefixWord ++ tailWord_4760714) baseStart_4760714 baseEnd_4760714 := by
    simpa [prefixWord, tailWord_4760714, baseEnd_4760714] using wordTrace_append hprefix tailTrace_4760714
  have hstable : (prefixWord ++ tailWord_4760714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760714).length < 2 ^ (prefixWord ++ tailWord_4760714).sum := by decide
  have hdescent : baseEnd_4760714 < baseStart_4760714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760734 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4760734 : Nat := 118140960795 + 4760734 * 2 ^ 59
def prefixEnd_4760734 : Nat := 4983230072969 + 3 ^ 40 * 4760734 * 2
def baseEnd_4760734 : Nat := 2444544810201881840030789

theorem tailTrace_4760734 : CollatzResearch.WordTrace tailWord_4760734 prefixEnd_4760734 2444544810201881840030789 := by
  unfold tailWord_4760734
  simp only [CollatzResearch.WordTrace]
  refine ⟨21704779241835157685076157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115758822623120840987072837 21704779241835157685076157)
  ·
    refine ⟨8139292215688184131903559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21704779241835157685076157 8139292215688184131903559)
    ·
      refine ⟨12208938323532276197855339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8139292215688184131903559 12208938323532276197855339)
      ·
        refine ⟨18313407485298414296783009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12208938323532276197855339 18313407485298414296783009)
        ·
          refine ⟨13735055613973810722587257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18313407485298414296783009 13735055613973810722587257)
          ·
            refine ⟨10301291710480358041940443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13735055613973810722587257 10301291710480358041940443)
            ·
              refine ⟨15451937565720537062910665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10301291710480358041940443 15451937565720537062910665)
              ·
                refine ⟨11588953174290402797182999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15451937565720537062910665 11588953174290402797182999)
                ·
                  refine ⟨17383429761435604195774499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11588953174290402797182999 17383429761435604195774499)
                  ·
                    refine ⟨26075144642153406293661749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17383429761435604195774499 26075144642153406293661749)
                    ·
                      refine ⟨2444544810201881840030789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26075144642153406293661749 2444544810201881840030789)
                      ·
                        rfl

theorem cell23_4760734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4760734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760734 prefixEnd_4760734 := by exact prefixLift 4760734
  have htrace : WordTrace (prefixWord ++ tailWord_4760734) baseStart_4760734 baseEnd_4760734 := by
    simpa [prefixWord, tailWord_4760734, baseEnd_4760734] using wordTrace_append hprefix tailTrace_4760734
  have hstable : (prefixWord ++ tailWord_4760734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760734).length < 2 ^ (prefixWord ++ tailWord_4760734).sum := by decide
  have hdescent : baseEnd_4760734 < baseStart_4760734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760764 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4760764 : Nat := 118140960795 + 4760764 * 2 ^ 59
def prefixEnd_4760764 : Nat := 4983230072969 + 3 ^ 40 * 4760764 * 2
def baseEnd_4760764 : Nat := 2444560214621516722655651

theorem tailTrace_4760764 : CollatzResearch.WordTrace tailWord_4760764 prefixEnd_4760764 2444560214621516722655651 := by
  unfold tailWord_4760764
  simp only [CollatzResearch.WordTrace]
  refine ⟨86819664062286288302100673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115759552083048384402800897 86819664062286288302100673)
  ·
    refine ⟨65114748046714716226575505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86819664062286288302100673 65114748046714716226575505)
    ·
      refine ⟨48836061035036037169931629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65114748046714716226575505 48836061035036037169931629)
      ·
        refine ⟨18313522888138513938724361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48836061035036037169931629 18313522888138513938724361)
        ·
          refine ⟨13735142166103885454043271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18313522888138513938724361 13735142166103885454043271)
          ·
            refine ⟨20602713249155828181064907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13735142166103885454043271 20602713249155828181064907)
            ·
              refine ⟨30904069873733742271597361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20602713249155828181064907 30904069873733742271597361)
              ·
                refine ⟨23178052405300306703698021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30904069873733742271597361 23178052405300306703698021)
                ·
                  refine ⟨4345884825993807506943379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23178052405300306703698021 4345884825993807506943379)
                  ·
                    refine ⟨6518827238990711260415069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4345884825993807506943379 6518827238990711260415069)
                    ·
                      refine ⟨2444560214621516722655651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6518827238990711260415069 2444560214621516722655651)
                      ·
                        rfl

theorem cell23_4760764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4760764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760764 prefixEnd_4760764 := by exact prefixLift 4760764
  have htrace : WordTrace (prefixWord ++ tailWord_4760764) baseStart_4760764 baseEnd_4760764 := by
    simpa [prefixWord, tailWord_4760764, baseEnd_4760764] using wordTrace_append hprefix tailTrace_4760764
  have hstable : (prefixWord ++ tailWord_4760764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760764).length < 2 ^ (prefixWord ++ tailWord_4760764).sum := by decide
  have hdescent : baseEnd_4760764 < baseStart_4760764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760787 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 4, 2]
def baseStart_4760787 : Nat := 118140960795 + 4760787 * 2 ^ 59
def prefixEnd_4760787 : Nat := 4983230072969 + 3 ^ 40 * 4760787 * 2
def baseEnd_4760787 : Nat := 2444572024676570132668045

theorem tailTrace_4760787 : CollatzResearch.WordTrace tailWord_4760787 prefixEnd_4760787 2444572024676570132668045 := by
  unfold tailWord_4760787
  simp only [CollatzResearch.WordTrace]
  refine ⟨173640167003489251532288615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115760111335659501021525743 173640167003489251532288615)
  ·
    refine ⟨260460250505233877298432923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173640167003489251532288615 260460250505233877298432923)
    ·
      refine ⟨390690375757850815947649385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260460250505233877298432923 390690375757850815947649385)
      ·
        refine ⟨293017781818388111960737039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390690375757850815947649385 293017781818388111960737039)
        ·
          refine ⟨439526672727582167941105559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293017781818388111960737039 439526672727582167941105559)
          ·
            refine ⟨659290009091373251911658339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439526672727582167941105559 659290009091373251911658339)
            ·
              refine ⟨988935013637059877867487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659290009091373251911658339 988935013637059877867487509)
              ·
                refine ⟨46356328764237181775038477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 988935013637059877867487509 46356328764237181775038477)
                ·
                  refine ⟨17383623286588943165639429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46356328764237181775038477 17383623286588943165639429)
                  ·
                    refine ⟨3259429366235426843557393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17383623286588943165639429 3259429366235426843557393)
                    ·
                      refine ⟨2444572024676570132668045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259429366235426843557393 2444572024676570132668045)
                      ·
                        rfl

theorem cell23_4760787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4, 2].length) (baseStart_4760787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760787 prefixEnd_4760787 := by exact prefixLift 4760787
  have htrace : WordTrace (prefixWord ++ tailWord_4760787) baseStart_4760787 baseEnd_4760787 := by
    simpa [prefixWord, tailWord_4760787, baseEnd_4760787] using wordTrace_append hprefix tailTrace_4760787
  have hstable : (prefixWord ++ tailWord_4760787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760787).length < 2 ^ (prefixWord ++ tailWord_4760787).sum := by decide
  have hdescent : baseEnd_4760787 < baseStart_4760787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760837 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_4760837 : Nat := 118140960795 + 4760837 * 2 ^ 59
def prefixEnd_4760837 : Nat := 4983230072969 + 3 ^ 40 * 4760837 * 2
def baseEnd_4760837 : Nat := 2444597698709294937042815

theorem tailTrace_4760837 : CollatzResearch.WordTrace tailWord_4760837 prefixEnd_4760837 2444597698709294937042815 := by
  unfold tailWord_4760837
  simp only [CollatzResearch.WordTrace]
  refine ⟨173641990653308110071608765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115761327102205406714405843 173641990653308110071608765)
  ·
    refine ⟨65115746494990541276853287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173641990653308110071608765 65115746494990541276853287)
    ·
      refine ⟨97673619742485811915279931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65115746494990541276853287 97673619742485811915279931)
      ·
        refine ⟨146510429613728717872919897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97673619742485811915279931 146510429613728717872919897)
        ·
          refine ⟨109882822210296538404689923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146510429613728717872919897 109882822210296538404689923)
          ·
            refine ⟨164824233315444807607034885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109882822210296538404689923 164824233315444807607034885)
            ·
              refine ⟨30904543746645901426319041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164824233315444807607034885 30904543746645901426319041)
              ·
                refine ⟨23178407809984426069739281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30904543746645901426319041 23178407809984426069739281)
                ·
                  refine ⟨17383805857488319552304461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23178407809984426069739281 17383805857488319552304461)
                  ·
                    refine ⟨6518927196558119832114173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17383805857488319552304461 6518927196558119832114173)
                    ·
                      refine ⟨2444597698709294937042815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6518927196558119832114173 2444597698709294937042815)
                      ·
                        rfl

theorem cell23_4760837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_4760837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760837 prefixEnd_4760837 := by exact prefixLift 4760837
  have htrace : WordTrace (prefixWord ++ tailWord_4760837) baseStart_4760837 baseEnd_4760837 := by
    simpa [prefixWord, tailWord_4760837, baseEnd_4760837] using wordTrace_append hprefix tailTrace_4760837
  have hstable : (prefixWord ++ tailWord_4760837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760837).length < 2 ^ (prefixWord ++ tailWord_4760837).sum := by decide
  have hdescent : baseEnd_4760837 < baseStart_4760837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760844 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 5]
def baseStart_4760844 : Nat := 118140960795 + 4760844 * 2 ^ 59
def prefixEnd_4760844 : Nat := 4983230072969 + 3 ^ 40 * 4760844 * 2
def baseEnd_4760844 : Nat := 271622365897097378850587

theorem tailTrace_4760844 : CollatzResearch.WordTrace tailWord_4760844 prefixEnd_4760844 271622365897097378850587 := by
  unfold tailWord_4760844
  simp only [CollatzResearch.WordTrace]
  refine ⟨86821122982141375133556793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115761497309521833511409057 86821122982141375133556793)
  ·
    refine ⟨65115842236606031350167595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86821122982141375133556793 65115842236606031350167595)
    ·
      refine ⟨97673763354909047025251393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65115842236606031350167595 97673763354909047025251393)
      ·
        refine ⟨73255322516181785268938545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97673763354909047025251393 73255322516181785268938545)
        ·
          refine ⟨54941491887136338951703909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73255322516181785268938545 54941491887136338951703909)
          ·
            refine ⟨10301529728838063553444483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54941491887136338951703909 10301529728838063553444483)
            ·
              refine ⟨15452294593257095330166725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10301529728838063553444483 15452294593257095330166725)
              ·
                refine ⟨2897305236235705374406261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15452294593257095330166725 2897305236235705374406261)
                ·
                  refine ⟨271622365897097378850587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2897305236235705374406261 271622365897097378850587)
                  ·
                    rfl

theorem cell23_4760844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_4760844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760844 prefixEnd_4760844 := by exact prefixLift 4760844
  have htrace : WordTrace (prefixWord ++ tailWord_4760844) baseStart_4760844 baseEnd_4760844 := by
    simpa [prefixWord, tailWord_4760844, baseEnd_4760844] using wordTrace_append hprefix tailTrace_4760844
  have hstable : (prefixWord ++ tailWord_4760844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760844).length < 2 ^ (prefixWord ++ tailWord_4760844).sum := by decide
  have hdescent : baseEnd_4760844 < baseStart_4760844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760874 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4760874 : Nat := 118140960795 + 4760874 * 2 ^ 59
def prefixEnd_4760874 : Nat := 4983230072969 + 3 ^ 40 * 4760874 * 2
def baseEnd_4760874 : Nat := 814872232497837097426715

theorem tailTrace_4760874 : CollatzResearch.WordTrace tailWord_4760874 prefixEnd_4760874 814872232497837097426715 := by
  unfold tailWord_4760874
  simp only [CollatzResearch.WordTrace]
  refine ⟨43410835038543516347676419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115762226769449376927137117 43410835038543516347676419)
  ·
    refine ⟨65116252557815274521514629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43410835038543516347676419 65116252557815274521514629)
    ·
      refine ⟨12209297354590363972783993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65116252557815274521514629 12209297354590363972783993)
      ·
        refine ⟨9156973015942772979587995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12209297354590363972783993 9156973015942772979587995)
        ·
          refine ⟨13735459523914159469381993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9156973015942772979587995 13735459523914159469381993)
          ·
            refine ⟨10301594642935619602036495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13735459523914159469381993 10301594642935619602036495)
            ·
              refine ⟨15452391964403429403054743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10301594642935619602036495 15452391964403429403054743)
              ·
                refine ⟨23178587946605144104582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15452391964403429403054743 23178587946605144104582115)
                ·
                  refine ⟨34767881919907716156873173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23178587946605144104582115 34767881919907716156873173)
                  ·
                    refine ⟨814872232497837097426715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34767881919907716156873173 814872232497837097426715)
                    ·
                      rfl

theorem cell23_4760874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4760874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760874 prefixEnd_4760874 := by exact prefixLift 4760874
  have htrace : WordTrace (prefixWord ++ tailWord_4760874) baseStart_4760874 baseEnd_4760874 := by
    simpa [prefixWord, tailWord_4760874, baseEnd_4760874] using wordTrace_append hprefix tailTrace_4760874
  have hstable : (prefixWord ++ tailWord_4760874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760874).length < 2 ^ (prefixWord ++ tailWord_4760874).sum := by decide
  have hdescent : baseEnd_4760874 < baseStart_4760874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760894 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4760894 : Nat := 118140960795 + 4760894 * 2 ^ 59
def prefixEnd_4760894 : Nat := 4983230072969 + 3 ^ 40 * 4760894 * 2
def baseEnd_4760894 : Nat := 2444626967106601214030053

theorem tailTrace_4760894 : CollatzResearch.WordTrace tailWord_4760894 prefixEnd_4760894 2444626967106601214030053 := by
  unfold tailWord_4760894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21705508701762701100804217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115762713076067739204289157 21705508701762701100804217)
  ·
    refine ⟨16279131526322025825603163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21705508701762701100804217 16279131526322025825603163)
    ·
      refine ⟨24418697289483038738404745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16279131526322025825603163 24418697289483038738404745)
      ·
        refine ⟨18314022967112279053803559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24418697289483038738404745 18314022967112279053803559)
        ·
          refine ⟨27471034450668418580705339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18314022967112279053803559 27471034450668418580705339)
          ·
            refine ⟨41206551676002627871058009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27471034450668418580705339 41206551676002627871058009)
            ·
              refine ⟨30904913757001970903293507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41206551676002627871058009 30904913757001970903293507)
              ·
                refine ⟨46357370635502956354940261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30904913757001970903293507 46357370635502956354940261)
                ·
                  refine ⟨8692006994156804316551299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46357370635502956354940261 8692006994156804316551299)
                  ·
                    refine ⟨13038010491235206474826949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8692006994156804316551299 13038010491235206474826949)
                    ·
                      refine ⟨2444626967106601214030053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13038010491235206474826949 2444626967106601214030053)
                      ·
                        rfl

theorem cell23_4760894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4760894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760894 prefixEnd_4760894 := by exact prefixLift 4760894
  have htrace : WordTrace (prefixWord ++ tailWord_4760894) baseStart_4760894 baseEnd_4760894 := by
    simpa [prefixWord, tailWord_4760894, baseEnd_4760894] using wordTrace_append hprefix tailTrace_4760894
  have hstable : (prefixWord ++ tailWord_4760894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760894).length < 2 ^ (prefixWord ++ tailWord_4760894).sum := by decide
  have hdescent : baseEnd_4760894 < baseStart_4760894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760927 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_4760927 : Nat := 118140960795 + 4760927 * 2 ^ 59
def prefixEnd_4760927 : Nat := 4983230072969 + 3 ^ 40 * 4760927 * 2
def baseEnd_4760927 : Nat := 2444643911968199584917401

theorem tailTrace_4760927 : CollatzResearch.WordTrace tailWord_4760927 prefixEnd_4760927 2444643911968199584917401 := by
  unfold tailWord_4760927
  simp only [CollatzResearch.WordTrace]
  refine ⟨173645273222982055442385035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115763515481988036961590023 173645273222982055442385035)
  ·
    refine ⟨260467909834473083163577553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173645273222982055442385035 260467909834473083163577553)
    ·
      refine ⟨195350932375854812372683165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260467909834473083163577553 195350932375854812372683165)
      ·
        refine ⟨73256599640945554639756187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195350932375854812372683165 73256599640945554639756187)
        ·
          refine ⟨109884899461418331959634281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73256599640945554639756187 109884899461418331959634281)
          ·
            refine ⟨82413674596063748969725711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109884899461418331959634281 82413674596063748969725711)
            ·
              refine ⟨123620511894095623454588567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82413674596063748969725711 123620511894095623454588567)
              ·
                refine ⟨185430767841143435181882851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123620511894095623454588567 185430767841143435181882851)
                ·
                  refine ⟨278146151761715152772824277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185430767841143435181882851 278146151761715152772824277)
                  ·
                    refine ⟨6519050431915198893113069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 278146151761715152772824277 6519050431915198893113069)
                    ·
                      refine ⟨2444643911968199584917401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519050431915198893113069 2444643911968199584917401)
                      ·
                        rfl

theorem cell23_4760927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_4760927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760927 prefixEnd_4760927 := by exact prefixLift 4760927
  have htrace : WordTrace (prefixWord ++ tailWord_4760927) baseStart_4760927 baseEnd_4760927 := by
    simpa [prefixWord, tailWord_4760927, baseEnd_4760927] using wordTrace_append hprefix tailTrace_4760927
  have hstable : (prefixWord ++ tailWord_4760927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760927).length < 2 ^ (prefixWord ++ tailWord_4760927).sum := by decide
  have hdescent : baseEnd_4760927 < baseStart_4760927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760994 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4760994 : Nat := 118140960795 + 4760994 * 2 ^ 59
def prefixEnd_4760994 : Nat := 4983230072969 + 3 ^ 40 * 4760994 * 2
def baseEnd_4760994 : Nat := 814892771724016940926531

theorem tailTrace_4760994 : CollatzResearch.WordTrace tailWord_4760994 prefixEnd_4760994 814892771724016940926531 := by
  unfold tailWord_4760994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43411929228434831471268509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115765144609159550590049357 43411929228434831471268509)
  ·
    refine ⟨16279473460663061801725691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43411929228434831471268509 16279473460663061801725691)
    ·
      refine ⟨24419210190994592702588537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16279473460663061801725691 24419210190994592702588537)
      ·
        refine ⟨18314407643245944526941403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24419210190994592702588537 18314407643245944526941403)
        ·
          refine ⟨27471611464868916790412105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18314407643245944526941403 27471611464868916790412105)
          ·
            refine ⟨20603708598651687592809079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27471611464868916790412105 20603708598651687592809079)
            ·
              refine ⟨30905562897977531389213619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20603708598651687592809079 30905562897977531389213619)
              ·
                refine ⟨46358344346966297083820429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30905562897977531389213619 46358344346966297083820429)
                ·
                  refine ⟨17384379130112361406432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46358344346966297083820429 17384379130112361406432661)
                  ·
                    refine ⟨814892771724016940926531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17384379130112361406432661 814892771724016940926531)
                    ·
                      rfl

theorem cell23_4760994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4760994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760994 prefixEnd_4760994 := by exact prefixLift 4760994
  have htrace : WordTrace (prefixWord ++ tailWord_4760994) baseStart_4760994 baseEnd_4760994 := by
    simpa [prefixWord, tailWord_4760994, baseEnd_4760994] using wordTrace_append hprefix tailTrace_4760994
  have hstable : (prefixWord ++ tailWord_4760994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760994).length < 2 ^ (prefixWord ++ tailWord_4760994).sum := by decide
  have hdescent : baseEnd_4760994 < baseStart_4760994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4760997 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_4760997 : Nat := 118140960795 + 4760997 * 2 ^ 59
def prefixEnd_4760997 : Nat := 4983230072969 + 3 ^ 40 * 4760997 * 2
def baseEnd_4760997 : Nat := 2444679855614014311042079

theorem tailTrace_4760997 : CollatzResearch.WordTrace tailWord_4760997 prefixEnd_4760997 2444679855614014311042079 := by
  unfold tailWord_4760997
  simp only [CollatzResearch.WordTrace]
  refine ⟨173647826332728457397433245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115765217555152304931622163 173647826332728457397433245)
  ·
    refine ⟨65117934874773171524037467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173647826332728457397433245 65117934874773171524037467)
    ·
      refine ⟨97676902312159757286056201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65117934874773171524037467 97676902312159757286056201)
      ·
        refine ⟨73257676734119817964542151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97676902312159757286056201 73257676734119817964542151)
        ·
          refine ⟨109886515101179726946813227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73257676734119817964542151 109886515101179726946813227)
          ·
            refine ⟨164829772651769590420219841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109886515101179726946813227 164829772651769590420219841)
            ·
              refine ⟨123622329488827192815164881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164829772651769590420219841 123622329488827192815164881)
              ·
                refine ⟨92716747116620394611373661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123622329488827192815164881 92716747116620394611373661)
                ·
                  refine ⟨34768780168732647979265123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92716747116620394611373661 34768780168732647979265123)
                  ·
                    refine ⟨52153170253098971968897685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34768780168732647979265123 52153170253098971968897685)
                    ·
                      refine ⟨2444679855614014311042079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52153170253098971968897685 2444679855614014311042079)
                      ·
                        rfl

theorem cell23_4760997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_4760997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4760997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4760997 prefixEnd_4760997 := by exact prefixLift 4760997
  have htrace : WordTrace (prefixWord ++ tailWord_4760997) baseStart_4760997 baseEnd_4760997 := by
    simpa [prefixWord, tailWord_4760997, baseEnd_4760997] using wordTrace_append hprefix tailTrace_4760997
  have hstable : (prefixWord ++ tailWord_4760997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4760997).length < 2 ^ (prefixWord ++ tailWord_4760997).sum := by decide
  have hdescent : baseEnd_4760997 < baseStart_4760997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4760997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761004 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_4761004 : Nat := 118140960795 + 4761004 * 2 ^ 59
def prefixEnd_4761004 : Nat := 4983230072969 + 3 ^ 40 * 4761004 * 2
def baseEnd_4761004 : Nat := 2444683449978595783654547

theorem tailTrace_4761004 : CollatzResearch.WordTrace tailWord_4761004 prefixEnd_4761004 2444683449978595783654547 := by
  unfold tailWord_4761004
  simp only [CollatzResearch.WordTrace]
  refine ⟨86824040821851548796469033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115765387762468731728625377 86824040821851548796469033)
  ·
    refine ⟨65118030616388661597351775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86824040821851548796469033 65118030616388661597351775)
    ·
      refine ⟨97677045924582992396027663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65118030616388661597351775 97677045924582992396027663)
      ·
        refine ⟨146515568886874488594041495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97677045924582992396027663 146515568886874488594041495)
        ·
          refine ⟨219773353330311732891062243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146515568886874488594041495 219773353330311732891062243)
          ·
            refine ⟨329660029995467599336593365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219773353330311732891062243 329660029995467599336593365)
            ·
              refine ⟨7726406953018771859451407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 329660029995467599336593365 7726406953018771859451407)
              ·
                refine ⟨11589610429528157789177111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7726406953018771859451407 11589610429528157789177111)
                ·
                  refine ⟨17384415644292236683765667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11589610429528157789177111 17384415644292236683765667)
                  ·
                    refine ⟨26076623466438355025648501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17384415644292236683765667 26076623466438355025648501)
                    ·
                      refine ⟨2444683449978595783654547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26076623466438355025648501 2444683449978595783654547)
                      ·
                        rfl

theorem cell23_4761004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_4761004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761004 prefixEnd_4761004 := by exact prefixLift 4761004
  have htrace : WordTrace (prefixWord ++ tailWord_4761004) baseStart_4761004 baseEnd_4761004 := by
    simpa [prefixWord, tailWord_4761004, baseEnd_4761004] using wordTrace_append hprefix tailTrace_4761004
  have hstable : (prefixWord ++ tailWord_4761004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761004).length < 2 ^ (prefixWord ++ tailWord_4761004).sum := by decide
  have hdescent : baseEnd_4761004 < baseStart_4761004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761027 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4761027 : Nat := 118140960795 + 4761027 * 2 ^ 59
def prefixEnd_4761027 : Nat := 4983230072969 + 3 ^ 40 * 4761027 * 2
def baseEnd_4761027 : Nat := 2444695260033649193666941

theorem tailTrace_4761027 : CollatzResearch.WordTrace tailWord_4761027 prefixEnd_4761027 2444695260033649193666941 := by
  unfold tailWord_4761027
  simp only [CollatzResearch.WordTrace]
  refine ⟨173648920522619772521025335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115765947015079848347350223 173648920522619772521025335)
  ·
    refine ⟨260473380783929658781538003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173648920522619772521025335 260473380783929658781538003)
    ·
      refine ⟨390710071175894488172307005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260473380783929658781538003 390710071175894488172307005)
      ·
        refine ⟨146516276690960433064615127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390710071175894488172307005 146516276690960433064615127)
        ·
          refine ⟨219774415036440649596922691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146516276690960433064615127 219774415036440649596922691)
          ·
            refine ⟨329661622554660974395384037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219774415036440649596922691 329661622554660974395384037)
            ·
              refine ⟨61811554228998932699134507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329661622554660974395384037 61811554228998932699134507)
              ·
                refine ⟨92717331343498399048701761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61811554228998932699134507 92717331343498399048701761)
                ·
                  refine ⟨69537998507623799286526321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92717331343498399048701761 69537998507623799286526321)
                  ·
                    refine ⟨52153498880717849464894741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69537998507623799286526321 52153498880717849464894741)
                    ·
                      refine ⟨2444695260033649193666941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52153498880717849464894741 2444695260033649193666941)
                      ·
                        rfl

theorem cell23_4761027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4761027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761027 prefixEnd_4761027 := by exact prefixLift 4761027
  have htrace : WordTrace (prefixWord ++ tailWord_4761027) baseStart_4761027 baseEnd_4761027 := by
    simpa [prefixWord, tailWord_4761027, baseEnd_4761027] using wordTrace_append hprefix tailTrace_4761027
  have hstable : (prefixWord ++ tailWord_4761027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761027).length < 2 ^ (prefixWord ++ tailWord_4761027).sum := by decide
  have hdescent : baseEnd_4761027 < baseStart_4761027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761028 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4761028 : Nat := 118140960795 + 4761028 * 2 ^ 59
def prefixEnd_4761028 : Nat := 4983230072969 + 3 ^ 40 * 4761028 * 2
def baseEnd_4761028 : Nat := 814898591171434563251479

theorem tailTrace_4761028 : CollatzResearch.WordTrace tailWord_4761028 prefixEnd_4761028 814898591171434563251479 := by
  unfold tailWord_4761028
  simp only [CollatzResearch.WordTrace]
  refine ⟨86824478497808074845905869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115765971330410766461207825 86824478497808074845905869)
  ·
    refine ⟨32559179436678028067214701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86824478497808074845905869 32559179436678028067214701)
    ·
      refine ⟨12209692288754260525205513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32559179436678028067214701 12209692288754260525205513)
      ·
        refine ⟨9157269216565695393904135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12209692288754260525205513 9157269216565695393904135)
        ·
          refine ⟨13735903824848543090856203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9157269216565695393904135 13735903824848543090856203)
          ·
            refine ⟨20603855737272814636284305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13735903824848543090856203 20603855737272814636284305)
            ·
              refine ⟨15452891802954610977213229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20603855737272814636284305 15452891802954610977213229)
              ·
                refine ⟨5794834426107979116454961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15452891802954610977213229 5794834426107979116454961)
                ·
                  refine ⟨4346125819580984337341221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794834426107979116454961 4346125819580984337341221)
                  ·
                    refine ⟨814898591171434563251479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4346125819580984337341221 814898591171434563251479)
                    ·
                      rfl

theorem cell23_4761028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4761028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761028 prefixEnd_4761028 := by exact prefixLift 4761028
  have htrace : WordTrace (prefixWord ++ tailWord_4761028) baseStart_4761028 baseEnd_4761028 := by
    simpa [prefixWord, tailWord_4761028, baseEnd_4761028] using wordTrace_append hprefix tailTrace_4761028
  have hstable : (prefixWord ++ tailWord_4761028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761028).length < 2 ^ (prefixWord ++ tailWord_4761028).sum := by decide
  have hdescent : baseEnd_4761028 < baseStart_4761028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761084 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_4761084 : Nat := 118140960795 + 4761084 * 2 ^ 59
def prefixEnd_4761084 : Nat := 4983230072969 + 3 ^ 40 * 4761084 * 2
def baseEnd_4761084 : Nat := 814908176143651823551393

theorem tailTrace_4761084 : CollatzResearch.WordTrace tailWord_4761084 prefixEnd_4761084 814908176143651823551393 := by
  unfold tailWord_4761084
  simp only [CollatzResearch.WordTrace]
  refine ⟨86825499741706635627925153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115767332988942180837233537 86825499741706635627925153)
  ·
    refine ⟨65119124806279976720943865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86825499741706635627925153 65119124806279976720943865)
    ·
      refine ⟨48839343604709982540707899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65119124806279976720943865 48839343604709982540707899)
      ·
        refine ⟨73259015407064973811061849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48839343604709982540707899 73259015407064973811061849)
        ·
          refine ⟨54944261555298730358296387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73259015407064973811061849 54944261555298730358296387)
          ·
            refine ⟨82416392332948095537444581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54944261555298730358296387 82416392332948095537444581)
            ·
              refine ⟨15453073562427767913270859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82416392332948095537444581 15453073562427767913270859)
              ·
                refine ⟨23179610343641651869906289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15453073562427767913270859 23179610343641651869906289)
                ·
                  refine ⟨17384707757731238902429717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23179610343641651869906289 17384707757731238902429717)
                  ·
                    refine ⟨814908176143651823551393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17384707757731238902429717 814908176143651823551393)
                    ·
                      rfl

theorem cell23_4761084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_4761084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761084 prefixEnd_4761084 := by exact prefixLift 4761084
  have htrace : WordTrace (prefixWord ++ tailWord_4761084) baseStart_4761084 baseEnd_4761084 := by
    simpa [prefixWord, tailWord_4761084, baseEnd_4761084] using wordTrace_append hprefix tailTrace_4761084
  have hstable : (prefixWord ++ tailWord_4761084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761084).length < 2 ^ (prefixWord ++ tailWord_4761084).sum := by decide
  have hdescent : baseEnd_4761084 < baseStart_4761084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761085 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_4761085 : Nat := 118140960795 + 4761085 * 2 ^ 59
def prefixEnd_4761085 : Nat := 4983230072969 + 3 ^ 40 * 4761085 * 2
def baseEnd_4761085 : Nat := 2444725041911609966741675

theorem tailTrace_4761085 : CollatzResearch.WordTrace tailWord_4761085 prefixEnd_4761085 2444725041911609966741675 := by
  unfold tailWord_4761085
  simp only [CollatzResearch.WordTrace]
  refine ⟨173651035956409648426636709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115767357304273098951091139 173651035956409648426636709)
  ·
    refine ⟨32559569241826809079994383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173651035956409648426636709 32559569241826809079994383)
    ·
      refine ⟨48839353862740213619991575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32559569241826809079994383 48839353862740213619991575)
      ·
        refine ⟨73259030794110320429987363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48839353862740213619991575 73259030794110320429987363)
        ·
          refine ⟨109888546191165480644981045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73259030794110320429987363 109888546191165480644981045)
          ·
            refine ⟨10302051205421763810466973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109888546191165480644981045 10302051205421763810466973)
            ·
              refine ⟨3863269202033161428925115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10302051205421763810466973 3863269202033161428925115)
              ·
                refine ⟨5794903803049742143387673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863269202033161428925115 5794903803049742143387673)
                ·
                  refine ⟨4346177852287306607540755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794903803049742143387673 4346177852287306607540755)
                  ·
                    refine ⟨6519266778430959911311133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346177852287306607540755 6519266778430959911311133)
                    ·
                      refine ⟨2444725041911609966741675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519266778430959911311133 2444725041911609966741675)
                      ·
                        rfl

theorem cell23_4761085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_4761085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761085 prefixEnd_4761085 := by exact prefixLift 4761085
  have htrace : WordTrace (prefixWord ++ tailWord_4761085) baseStart_4761085 baseEnd_4761085 := by
    simpa [prefixWord, tailWord_4761085, baseEnd_4761085] using wordTrace_append hprefix tailTrace_4761085
  have hstable : (prefixWord ++ tailWord_4761085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761085).length < 2 ^ (prefixWord ++ tailWord_4761085).sum := by decide
  have hdescent : baseEnd_4761085 < baseStart_4761085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761091 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 4, 2]
def baseStart_4761091 : Nat := 118140960795 + 4761091 * 2 ^ 59
def prefixEnd_4761091 : Nat := 4983230072969 + 3 ^ 40 * 4761091 * 2
def baseEnd_4761091 : Nat := 2444728122795536943266647

theorem tailTrace_4761091 : CollatzResearch.WordTrace tailWord_4761091 prefixEnd_4761091 2444728122795536943266647 := by
  unfold tailWord_4761091
  simp only [CollatzResearch.WordTrace]
  refine ⟨173651254794387911451355127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115767503196258607634236751 173651254794387911451355127)
  ·
    refine ⟨260476882191581867177032691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173651254794387911451355127 260476882191581867177032691)
    ·
      refine ⟨390715323287372800765549037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260476882191581867177032691 390715323287372800765549037)
      ·
        refine ⟨146518246232764800287080889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390715323287372800765549037 146518246232764800287080889)
        ·
          refine ⟨109888684674573600215310667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146518246232764800287080889 109888684674573600215310667)
          ·
            refine ⟨164833027011860400322966001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109888684674573600215310667 164833027011860400322966001)
            ·
              refine ⟨123624770258895300242224501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164833027011860400322966001 123624770258895300242224501)
              ·
                refine ⟨11589822211771434397708547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123624770258895300242224501 11589822211771434397708547)
                ·
                  refine ⟨17384733317657151596562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11589822211771434397708547 17384733317657151596562821)
                  ·
                    refine ⟨3259637497060715924355529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17384733317657151596562821 3259637497060715924355529)
                    ·
                      refine ⟨2444728122795536943266647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259637497060715924355529 2444728122795536943266647)
                      ·
                        rfl

theorem cell23_4761091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_4761091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761091 prefixEnd_4761091 := by exact prefixLift 4761091
  have htrace : WordTrace (prefixWord ++ tailWord_4761091) baseStart_4761091 baseEnd_4761091 := by
    simpa [prefixWord, tailWord_4761091, baseEnd_4761091] using wordTrace_append hprefix tailTrace_4761091
  have hstable : (prefixWord ++ tailWord_4761091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761091).length < 2 ^ (prefixWord ++ tailWord_4761091).sum := by decide
  have hdescent : baseEnd_4761091 < baseStart_4761091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761095 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4761095 : Nat := 118140960795 + 4761095 * 2 ^ 59
def prefixEnd_4761095 : Nat := 4983230072969 + 3 ^ 40 * 4761095 * 2
def baseEnd_4761095 : Nat := 2444730176718154927616629

theorem tailTrace_4761095 : CollatzResearch.WordTrace tailWord_4761095 prefixEnd_4761095 2444730176718154927616629 := by
  unfold tailWord_4761095
  simp only [CollatzResearch.WordTrace]
  refine ⟨173651400686373420134500739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115767600457582280089667159 173651400686373420134500739)
  ·
    refine ⟨260477101029560130201751109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173651400686373420134500739 260477101029560130201751109)
    ·
      refine ⟨48839456443042524412828333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260477101029560130201751109 48839456443042524412828333)
      ·
        refine ⟨18314796166140946654810625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48839456443042524412828333 18314796166140946654810625)
        ·
          refine ⟨13736097124605709991107969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18314796166140946654810625 13736097124605709991107969)
          ·
            refine ⟨10302072843454282493330977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13736097124605709991107969 10302072843454282493330977)
            ·
              refine ⟨7726554632590711869998233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10302072843454282493330977 7726554632590711869998233)
              ·
                refine ⟨5794915974443033902498675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7726554632590711869998233 5794915974443033902498675)
                ·
                  refine ⟨8692373961664550853748013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5794915974443033902498675 8692373961664550853748013)
                  ·
                    refine ⟨3259640235624206570155505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8692373961664550853748013 3259640235624206570155505)
                    ·
                      refine ⟨2444730176718154927616629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259640235624206570155505 2444730176718154927616629)
                      ·
                        rfl

theorem cell23_4761095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4761095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761095 prefixEnd_4761095 := by exact prefixLift 4761095
  have htrace : WordTrace (prefixWord ++ tailWord_4761095) baseStart_4761095 baseEnd_4761095 := by
    simpa [prefixWord, tailWord_4761095, baseEnd_4761095] using wordTrace_append hprefix tailTrace_4761095
  have hstable : (prefixWord ++ tailWord_4761095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761095).length < 2 ^ (prefixWord ++ tailWord_4761095).sum := by decide
  have hdescent : baseEnd_4761095 < baseStart_4761095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761184 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_4761184 : Nat := 118140960795 + 4761184 * 2 ^ 59
def prefixEnd_4761184 : Nat := 4983230072969 + 3 ^ 40 * 4761184 * 2
def baseEnd_4761184 : Nat := 2444775876496405079403719

theorem tailTrace_4761184 : CollatzResearch.WordTrace tailWord_4761184 prefixEnd_4761184 2444775876496405079403719 := by
  unfold tailWord_4761184
  simp only [CollatzResearch.WordTrace]
  refine ⟨86827323391525494167245303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115769764522033992222993737 86827323391525494167245303)
  ·
    refine ⟨130240985087288241250867955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86827323391525494167245303 130240985087288241250867955)
    ·
      refine ⟨195361477630932361876301933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130240985087288241250867955 195361477630932361876301933)
      ·
        refine ⟨73260554111599635703613225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195361477630932361876301933 73260554111599635703613225)
        ·
          refine ⟨54945415583699726777709919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73260554111599635703613225 54945415583699726777709919)
          ·
            refine ⟨82418123375549590166564879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54945415583699726777709919 82418123375549590166564879)
            ·
              refine ⟨123627185063324385249847319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82418123375549590166564879 123627185063324385249847319)
              ·
                refine ⟨185440777594986577874770979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123627185063324385249847319 185440777594986577874770979)
                ·
                  refine ⟨278161166392479866812156469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185440777594986577874770979 278161166392479866812156469)
                  ·
                    refine ⟨26077609349294987513639669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 278161166392479866812156469 26077609349294987513639669)
                    ·
                      refine ⟨2444775876496405079403719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26077609349294987513639669 2444775876496405079403719)
                      ·
                        rfl

theorem cell23_4761184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_4761184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761184 prefixEnd_4761184 := by exact prefixLift 4761184
  have htrace : WordTrace (prefixWord ++ tailWord_4761184) baseStart_4761184 baseEnd_4761184 := by
    simpa [prefixWord, tailWord_4761184, baseEnd_4761184] using wordTrace_append hprefix tailTrace_4761184
  have hstable : (prefixWord ++ tailWord_4761184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761184).length < 2 ^ (prefixWord ++ tailWord_4761184).sum := by decide
  have hdescent : baseEnd_4761184 < baseStart_4761184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761201 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_4761201 : Nat := 118140960795 + 4761201 * 2 ^ 59
def prefixEnd_4761201 : Nat := 4983230072969 + 3 ^ 40 * 4761201 * 2
def baseEnd_4761201 : Nat := 2444784605667531512891141

theorem tailTrace_4761201 : CollatzResearch.WordTrace tailWord_4761201 prefixEnd_4761201 2444784605667531512891141 := by
  unfold tailWord_4761201
  simp only [CollatzResearch.WordTrace]
  refine ⟨173655266823989400237859457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115770177882659600158572971 173655266823989400237859457)
  ·
    refine ⟨130241450117992050178394593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173655266823989400237859457 130241450117992050178394593)
    ·
      refine ⟨97681087588494037633795945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130241450117992050178394593 97681087588494037633795945)
      ·
        refine ⟨73260815691370528225346959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97681087588494037633795945 73260815691370528225346959)
        ·
          refine ⟨109891223537055792338020439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73260815691370528225346959 109891223537055792338020439)
          ·
            refine ⟨164836835305583688507030659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109891223537055792338020439 164836835305583688507030659)
            ·
              refine ⟨247255252958375532760545989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164836835305583688507030659 247255252958375532760545989)
              ·
                refine ⟨46360359929695412392602373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247255252958375532760545989 46360359929695412392602373)
                ·
                  refine ⟨8692567486817889823612945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46360359929695412392602373 8692567486817889823612945)
                  ·
                    refine ⟨6519425615113417367709709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8692567486817889823612945 6519425615113417367709709)
                    ·
                      refine ⟨2444784605667531512891141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519425615113417367709709 2444784605667531512891141)
                      ·
                        rfl

theorem cell23_4761201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_4761201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761201 prefixEnd_4761201 := by exact prefixLift 4761201
  have htrace : WordTrace (prefixWord ++ tailWord_4761201) baseStart_4761201 baseEnd_4761201 := by
    simpa [prefixWord, tailWord_4761201, baseEnd_4761201] using wordTrace_append hprefix tailTrace_4761201
  have hstable : (prefixWord ++ tailWord_4761201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761201).length < 2 ^ (prefixWord ++ tailWord_4761201).sum := by decide
  have hdescent : baseEnd_4761201 < baseStart_4761201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761288 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_4761288 : Nat := 118140960795 + 4761288 * 2 ^ 59
def prefixEnd_4761288 : Nat := 4983230072969 + 3 ^ 40 * 4761288 * 2
def baseEnd_4761288 : Nat := 2444829278484472672503241

theorem tailTrace_4761288 : CollatzResearch.WordTrace tailWord_4761288 prefixEnd_4761288 2444829278484472672503241 := by
  unfold tailWord_4761288
  simp only [CollatzResearch.WordTrace]
  refine ⟨86829219987337107048138259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115772293316449476064184345 86829219987337107048138259)
  ·
    refine ⟨130243829981005660572207389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86829219987337107048138259 130243829981005660572207389)
    ·
      refine ⟨48841436242877122714577771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130243829981005660572207389 48841436242877122714577771)
      ·
        refine ⟨73262154364315684071866657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48841436242877122714577771 73262154364315684071866657)
        ·
          refine ⟨54946615773236763053899993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73262154364315684071866657 54946615773236763053899993)
          ·
            refine ⟨41209961829927572290424995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54946615773236763053899993 41209961829927572290424995)
            ·
              refine ⟨61814942744891358435637493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41209961829927572290424995 61814942744891358435637493)
              ·
                refine ⟨5795150882333564853341015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61814942744891358435637493 5795150882333564853341015)
                ·
                  refine ⟨8692726323500347280011523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795150882333564853341015 8692726323500347280011523)
                  ·
                    refine ⟨13039089485250520920017285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8692726323500347280011523 13039089485250520920017285)
                    ·
                      refine ⟨2444829278484472672503241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13039089485250520920017285 2444829278484472672503241)
                      ·
                        rfl

theorem cell23_4761288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_4761288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761288 prefixEnd_4761288 := by exact prefixLift 4761288
  have htrace : WordTrace (prefixWord ++ tailWord_4761288) baseStart_4761288 baseEnd_4761288 := by
    simpa [prefixWord, tailWord_4761288, baseEnd_4761288] using wordTrace_append hprefix tailTrace_4761288
  have hstable : (prefixWord ++ tailWord_4761288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761288).length < 2 ^ (prefixWord ++ tailWord_4761288).sum := by decide
  have hdescent : baseEnd_4761288 < baseStart_4761288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761292 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4761292 : Nat := 118140960795 + 4761292 * 2 ^ 59
def prefixEnd_4761292 : Nat := 4983230072969 + 3 ^ 40 * 4761292 * 2
def baseEnd_4761292 : Nat := 2444831332407090656853223

theorem tailTrace_4761292 : CollatzResearch.WordTrace tailWord_4761292 prefixEnd_4761292 2444831332407090656853223 := by
  unfold tailWord_4761292
  simp only [CollatzResearch.WordTrace]
  refine ⟨86829292933329861389711065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115772390577773148519614753 86829292933329861389711065)
  ·
    refine ⟨65121969699997396042283299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86829292933329861389711065 65121969699997396042283299)
    ·
      refine ⟨97682954549996094063424949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65121969699997396042283299 97682954549996094063424949)
      ·
        refine ⟨9157776989062133818446089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97682954549996094063424949 9157776989062133818446089)
        ·
          refine ⟨6868332741796600363834567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9157776989062133818446089 6868332741796600363834567)
          ·
            refine ⟨10302499112694900545751851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868332741796600363834567 10302499112694900545751851)
            ·
              refine ⟨15453748669042350818627777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302499112694900545751851 15453748669042350818627777)
              ·
                refine ⟨11590311501781763113970833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15453748669042350818627777 11590311501781763113970833)
                ·
                  refine ⟨8692733626336322335478125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11590311501781763113970833 8692733626336322335478125)
                  ·
                    refine ⟨3259775109876120875804297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8692733626336322335478125 3259775109876120875804297)
                    ·
                      refine ⟨2444831332407090656853223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259775109876120875804297 2444831332407090656853223)
                      ·
                        rfl

theorem cell23_4761292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4761292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761292 prefixEnd_4761292 := by exact prefixLift 4761292
  have htrace : WordTrace (prefixWord ++ tailWord_4761292) baseStart_4761292 baseEnd_4761292 := by
    simpa [prefixWord, tailWord_4761292, baseEnd_4761292] using wordTrace_append hprefix tailTrace_4761292
  have hstable : (prefixWord ++ tailWord_4761292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761292).length < 2 ^ (prefixWord ++ tailWord_4761292).sum := by decide
  have hdescent : baseEnd_4761292 < baseStart_4761292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761311 : List Nat := [1, 1, 2, 3, 2, 2, 4, 8]
def baseStart_4761311 : Nat := 118140960795 + 4761311 * 2 ^ 59
def prefixEnd_4761311 : Nat := 4983230072969 + 3 ^ 40 * 4761311 * 2
def baseEnd_4761311 : Nat := 90549669945908373426505

theorem tailTrace_4761311 : CollatzResearch.WordTrace tailWord_4761311 prefixEnd_4761311 90549669945908373426505 := by
  unfold tailWord_4761311
  simp only [CollatzResearch.WordTrace]
  refine ⟨173659278853590889024363787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115772852569060592682909191 173659278853590889024363787)
  ·
    refine ⟨260488918280386333536545681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173659278853590889024363787 260488918280386333536545681)
    ·
      refine ⟨195366688710289750152409261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260488918280386333536545681 195366688710289750152409261)
      ·
        refine ⟨73262508266358656307153473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195366688710289750152409261 73262508266358656307153473)
        ·
          refine ⟨54946881199768992230365105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73262508266358656307153473 54946881199768992230365105)
          ·
            refine ⟨41210160899826744172773829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54946881199768992230365105 41210160899826744172773829)
            ·
              refine ⟨7726905168717514532395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41210160899826744172773829 7726905168717514532395093)
              ·
                refine ⟨90549669945908373426505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7726905168717514532395093 90549669945908373426505)
                ·
                  rfl

theorem cell23_4761311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 8].length) (baseStart_4761311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761311 prefixEnd_4761311 := by exact prefixLift 4761311
  have htrace : WordTrace (prefixWord ++ tailWord_4761311) baseStart_4761311 baseEnd_4761311 := by
    simpa [prefixWord, tailWord_4761311, baseEnd_4761311] using wordTrace_append hprefix tailTrace_4761311
  have hstable : (prefixWord ++ tailWord_4761311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761311).length < 2 ^ (prefixWord ++ tailWord_4761311).sum := by decide
  have hdescent : baseEnd_4761311 < baseStart_4761311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761319 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 1, 5]
def baseStart_4761319 : Nat := 118140960795 + 4761319 * 2 ^ 59
def prefixEnd_4761319 : Nat := 4983230072969 + 3 ^ 40 * 4761319 * 2
def baseEnd_4761319 : Nat := 814948398794920683738533

theorem tailTrace_4761319 : CollatzResearch.WordTrace tailWord_4761319 prefixEnd_4761319 814948398794920683738533 := by
  unfold tailWord_4761319
  simp only [CollatzResearch.WordTrace]
  refine ⟨173659570637561906390655011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115773047091707937593770007 173659570637561906390655011)
  ·
    refine ⟨260489355956342859585982517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173659570637561906390655011 260489355956342859585982517)
    ·
      refine ⟨24420877120907143086185861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260489355956342859585982517 24420877120907143086185861)
      ·
        refine ⟨4578914460170089328659849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24420877120907143086185861 4578914460170089328659849)
        ·
          refine ⟨3434185845127566996494887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4578914460170089328659849 3434185845127566996494887)
          ·
            refine ⟨5151278767691350494742331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434185845127566996494887 5151278767691350494742331)
            ·
              refine ⟨7726918151537025742113497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151278767691350494742331 7726918151537025742113497)
              ·
                refine ⟨5795188613652769306585123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7726918151537025742113497 5795188613652769306585123)
                ·
                  refine ⟨8692782920479153959877685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795188613652769306585123 8692782920479153959877685)
                  ·
                    refine ⟨814948398794920683738533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8692782920479153959877685 814948398794920683738533)
                    ·
                      rfl

theorem cell23_4761319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_4761319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761319 prefixEnd_4761319 := by exact prefixLift 4761319
  have htrace : WordTrace (prefixWord ++ tailWord_4761319) baseStart_4761319 baseEnd_4761319 := by
    simpa [prefixWord, tailWord_4761319, baseEnd_4761319] using wordTrace_append hprefix tailTrace_4761319
  have hstable : (prefixWord ++ tailWord_4761319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761319).length < 2 ^ (prefixWord ++ tailWord_4761319).sum := by decide
  have hdescent : baseEnd_4761319 < baseStart_4761319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761325 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4761325 : Nat := 118140960795 + 4761325 * 2 ^ 59
def prefixEnd_4761325 : Nat := 4983230072969 + 3 ^ 40 * 4761325 * 2
def baseEnd_4761325 : Nat := 2444848277268689027740571

theorem tailTrace_4761325 : CollatzResearch.WordTrace tailWord_4761325 prefixEnd_4761325 2444848277268689027740571 := by
  unfold tailWord_4761325
  simp only [CollatzResearch.WordTrace]
  refine ⟨173659789475540169415373429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115773192983693446276915619 173659789475540169415373429)
  ·
    refine ⟨16280605263331890882691259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173659789475540169415373429 16280605263331890882691259)
    ·
      refine ⟨24420907894997836324036889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16280605263331890882691259 24420907894997836324036889)
      ·
        refine ⟨18315680921248377243027667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24420907894997836324036889 18315680921248377243027667)
        ·
          refine ⟨27473521381872565864541501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18315680921248377243027667 27473521381872565864541501)
          ·
            refine ⟨10302570518202212199203063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27473521381872565864541501 10302570518202212199203063)
            ·
              refine ⟨15453855777303318298804595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302570518202212199203063 15453855777303318298804595)
              ·
                refine ⟨23180783665954977448206893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15453855777303318298804595 23180783665954977448206893)
                ·
                  refine ⟨8692793874733116543077585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23180783665954977448206893 8692793874733116543077585)
                  ·
                    refine ⟨6519595406049837407308189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8692793874733116543077585 6519595406049837407308189)
                    ·
                      refine ⟨2444848277268689027740571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519595406049837407308189 2444848277268689027740571)
                      ·
                        rfl

theorem cell23_4761325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4761325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761325 prefixEnd_4761325 := by exact prefixLift 4761325
  have htrace : WordTrace (prefixWord ++ tailWord_4761325) baseStart_4761325 baseEnd_4761325 := by
    simpa [prefixWord, tailWord_4761325, baseEnd_4761325] using wordTrace_append hprefix tailTrace_4761325
  have hstable : (prefixWord ++ tailWord_4761325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761325).length < 2 ^ (prefixWord ++ tailWord_4761325).sum := by decide
  have hdescent : baseEnd_4761325 < baseStart_4761325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761332 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4761332 : Nat := 118140960795 + 4761332 * 2 ^ 59
def prefixEnd_4761332 : Nat := 4983230072969 + 3 ^ 40 * 4761332 * 2
def baseEnd_4761332 : Nat := 814950623877756833451013

theorem tailTrace_4761332 : CollatzResearch.WordTrace tailWord_4761332 prefixEnd_4761332 814950623877756833451013 := by
  unfold tailWord_4761332
  simp only [CollatzResearch.WordTrace]
  refine ⟨86830022393257404805439125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115773363191009873073918833 86830022393257404805439125)
  ·
    refine ⟨4070157299683940850254959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86830022393257404805439125 4070157299683940850254959)
    ·
      refine ⟨6105235949525911275382439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4070157299683940850254959 6105235949525911275382439)
      ·
        refine ⟨9157853924288866913073659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105235949525911275382439 9157853924288866913073659)
        ·
          refine ⟨13736780886433300369610489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9157853924288866913073659 13736780886433300369610489)
          ·
            refine ⟨10302585664824975277207867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13736780886433300369610489 10302585664824975277207867)
            ·
              refine ⟨15453878497237462915811801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302585664824975277207867 15453878497237462915811801)
              ·
                refine ⟨11590408872928097186858851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15453878497237462915811801 11590408872928097186858851)
                ·
                  refine ⟨17385613309392145780288277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11590408872928097186858851 17385613309392145780288277)
                  ·
                    refine ⟨814950623877756833451013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17385613309392145780288277 814950623877756833451013)
                    ·
                      rfl

theorem cell23_4761332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4761332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761332 prefixEnd_4761332 := by exact prefixLift 4761332
  have htrace : WordTrace (prefixWord ++ tailWord_4761332) baseStart_4761332 baseEnd_4761332 := by
    simpa [prefixWord, tailWord_4761332, baseEnd_4761332] using wordTrace_append hprefix tailTrace_4761332
  have hstable : (prefixWord ++ tailWord_4761332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761332).length < 2 ^ (prefixWord ++ tailWord_4761332).sum := by decide
  have hdescent : baseEnd_4761332 < baseStart_4761332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761342 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4761342 : Nat := 118140960795 + 4761342 * 2 ^ 59
def prefixEnd_4761342 : Nat := 4983230072969 + 3 ^ 40 * 4761342 * 2
def baseEnd_4761342 : Nat := 2444857006439815461227993

theorem tailTrace_4761342 : CollatzResearch.WordTrace tailWord_4761342 prefixEnd_4761342 2444857006439815461227993 := by
  unfold tailWord_4761342
  simp only [CollatzResearch.WordTrace]
  refine ⟨21707551189559822664842785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115773606344319054212494853 21707551189559822664842785)
  ·
    refine ⟨16280663392169866998632089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21707551189559822664842785 16280663392169866998632089)
    ·
      refine ⟨12210497544127400248974067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16280663392169866998632089 12210497544127400248974067)
      ·
        refine ⟨18315746316191100373461101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12210497544127400248974067 18315746316191100373461101)
        ·
          refine ⟨6868404868571662640047913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18315746316191100373461101 6868404868571662640047913)
          ·
            refine ⟨5151303651428746980035935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6868404868571662640047913 5151303651428746980035935)
            ·
              refine ⟨7726955477143120470053903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151303651428746980035935 7726955477143120470053903)
              ·
                refine ⟨11590433215714680705080855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7726955477143120470053903 11590433215714680705080855)
                ·
                  refine ⟨17385649823572021057621283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11590433215714680705080855 17385649823572021057621283)
                  ·
                    refine ⟨26078474735358031586431925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17385649823572021057621283 26078474735358031586431925)
                    ·
                      refine ⟨2444857006439815461227993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26078474735358031586431925 2444857006439815461227993)
                      ·
                        rfl

theorem cell23_4761342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4761342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761342 prefixEnd_4761342 := by exact prefixLift 4761342
  have htrace : WordTrace (prefixWord ++ tailWord_4761342) baseStart_4761342 baseEnd_4761342 := by
    simpa [prefixWord, tailWord_4761342, baseEnd_4761342] using wordTrace_append hprefix tailTrace_4761342
  have hstable : (prefixWord ++ tailWord_4761342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761342).length < 2 ^ (prefixWord ++ tailWord_4761342).sum := by decide
  have hdescent : baseEnd_4761342 < baseStart_4761342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761355 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 3]
def baseStart_4761355 : Nat := 118140960795 + 4761355 * 2 ^ 59
def prefixEnd_4761355 : Nat := 4983230072969 + 3 ^ 40 * 4761355 * 2
def baseEnd_4761355 : Nat := 2444863681688323910365433

theorem tailTrace_4761355 : CollatzResearch.WordTrace tailWord_4761355 prefixEnd_4761355 2444863681688323910365433 := by
  unfold tailWord_4761355
  simp only [CollatzResearch.WordTrace]
  refine ⟨173660883665431484538965519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115773922443620989692643679 173660883665431484538965519)
  ·
    refine ⟨260491325498147226808448279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173660883665431484538965519 260491325498147226808448279)
    ·
      refine ⟨390736988247220840212672419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260491325498147226808448279 390736988247220840212672419)
      ·
        refine ⟨586105482370831260319008629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390736988247220840212672419 586105482370831260319008629)
        ·
          refine ⟨54947388972265430654907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 586105482370831260319008629 54947388972265430654907059)
          ·
            refine ⟨82421083458398145982360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54947388972265430654907059 82421083458398145982360589)
            ·
              refine ⟨30907906296899304743385221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82421083458398145982360589 30907906296899304743385221)
              ·
                refine ⟨5795232430668619639384729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30907906296899304743385221 5795232430668619639384729)
                ·
                  refine ⟨4346424323001464729538547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5795232430668619639384729 4346424323001464729538547)
                  ·
                    refine ⟨6519636484502197094307821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346424323001464729538547 6519636484502197094307821)
                    ·
                      refine ⟨2444863681688323910365433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519636484502197094307821 2444863681688323910365433)
                      ·
                        rfl

theorem cell23_4761355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 3].length) (baseStart_4761355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761355 prefixEnd_4761355 := by exact prefixLift 4761355
  have htrace : WordTrace (prefixWord ++ tailWord_4761355) baseStart_4761355 baseEnd_4761355 := by
    simpa [prefixWord, tailWord_4761355, baseEnd_4761355] using wordTrace_append hprefix tailTrace_4761355
  have hstable : (prefixWord ++ tailWord_4761355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761355).length < 2 ^ (prefixWord ++ tailWord_4761355).sum := by decide
  have hdescent : baseEnd_4761355 < baseStart_4761355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761365 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_4761365 : Nat := 118140960795 + 4761365 * 2 ^ 59
def prefixEnd_4761365 : Nat := 4983230072969 + 3 ^ 40 * 4761365 * 2
def baseEnd_4761365 : Nat := 2444868816494868871240387

theorem tailTrace_4761365 : CollatzResearch.WordTrace tailWord_4761365 prefixEnd_4761365 2444868816494868871240387 := by
  unfold tailWord_4761365
  simp only [CollatzResearch.WordTrace]
  refine ⟨173661248395395256246829549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115774165596930170831219699 173661248395395256246829549)
  ·
    refine ⟨65122968148273221092561081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173661248395395256246829549 65122968148273221092561081)
    ·
      refine ⟨48842226111204915819420811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65122968148273221092561081 48842226111204915819420811)
      ·
        refine ⟨73263339166807373729131217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48842226111204915819420811 73263339166807373729131217)
        ·
          refine ⟨54947504375105530296848413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73263339166807373729131217 54947504375105530296848413)
          ·
            refine ⟨20605314140664573861318155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54947504375105530296848413 20605314140664573861318155)
            ·
              refine ⟨30907971210996860791977233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20605314140664573861318155 30907971210996860791977233)
              ·
                refine ⟨23180978408247645593982925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30907971210996860791977233 23180978408247645593982925)
                ·
                  refine ⟨8692866903092867097743597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23180978408247645593982925 8692866903092867097743597)
                  ·
                    refine ⟨3259825088659825161653849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8692866903092867097743597 3259825088659825161653849)
                    ·
                      refine ⟨2444868816494868871240387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259825088659825161653849 2444868816494868871240387)
                      ·
                        rfl

theorem cell23_4761365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_4761365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761365 prefixEnd_4761365 := by exact prefixLift 4761365
  have htrace : WordTrace (prefixWord ++ tailWord_4761365) baseStart_4761365 baseEnd_4761365 := by
    simpa [prefixWord, tailWord_4761365, baseEnd_4761365] using wordTrace_append hprefix tailTrace_4761365
  have hstable : (prefixWord ++ tailWord_4761365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761365).length < 2 ^ (prefixWord ++ tailWord_4761365).sum := by decide
  have hdescent : baseEnd_4761365 < baseStart_4761365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761371 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 6]
def baseStart_4761371 : Nat := 118140960795 + 4761371 * 2 ^ 59
def prefixEnd_4761371 : Nat := 4983230072969 + 3 ^ 40 * 4761371 * 2
def baseEnd_4761371 : Nat := 814957299126265282588453

theorem tailTrace_4761371 : CollatzResearch.WordTrace tailWord_4761371 prefixEnd_4761371 814957299126265282588453 := by
  unfold tailWord_4761371
  simp only [CollatzResearch.WordTrace]
  refine ⟨173661467233373519271547967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115774311488915679514365311 173661467233373519271547967)
  ·
    refine ⟨260492200850060278907321951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173661467233373519271547967 260492200850060278907321951)
    ·
      refine ⟨390738301275090418360982927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260492200850060278907321951 390738301275090418360982927)
      ·
        refine ⟨586107451912635627541474391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390738301275090418360982927 586107451912635627541474391)
        ·
          refine ⟨879161177868953441312211587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586107451912635627541474391 879161177868953441312211587)
          ·
            refine ⟨1318741766803430161968317381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879161177868953441312211587 1318741766803430161968317381)
            ·
              refine ⟨247264081275643155369059509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1318741766803430161968317381 247264081275643155369059509)
              ·
                refine ⟨23181007619591545815849329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247264081275643155369059509 23181007619591545815849329)
                ·
                  refine ⟨17385755714693659361886997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23181007619591545815849329 17385755714693659361886997)
                  ·
                    refine ⟨814957299126265282588453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17385755714693659361886997 814957299126265282588453)
                    ·
                      rfl

theorem cell23_4761371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_4761371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761371 prefixEnd_4761371 := by exact prefixLift 4761371
  have htrace : WordTrace (prefixWord ++ tailWord_4761371) baseStart_4761371 baseEnd_4761371 := by
    simpa [prefixWord, tailWord_4761371, baseEnd_4761371] using wordTrace_append hprefix tailTrace_4761371
  have hstable : (prefixWord ++ tailWord_4761371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761371).length < 2 ^ (prefixWord ++ tailWord_4761371).sum := by decide
  have hdescent : baseEnd_4761371 < baseStart_4761371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
