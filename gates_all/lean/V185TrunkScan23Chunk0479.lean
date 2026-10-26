import V185TrunkScan23Chunk0478

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2832858 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2832858 : Nat := 118140960795 + 2832858 * 2 ^ 59
def prefixEnd_2832858 : Nat := 4983230072969 + 3 ^ 40 * 2832858 * 2
def baseEnd_2832858 : Nat := 1454617779934582663746929

theorem tailTrace_2832858 : CollatzResearch.WordTrace tailWord_2832858 prefixEnd_2832858 1454617779934582663746929 := by
  unfold tailWord_2832858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830704892761688618284807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68881879714031169648759485 25830704892761688618284807)
  ·
    refine ⟨38746057339142532927427211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25830704892761688618284807 38746057339142532927427211)
    ·
      refine ⟨58119086008713799391140817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38746057339142532927427211 58119086008713799391140817)
      ·
        refine ⟨43589314506535349543355613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58119086008713799391140817 43589314506535349543355613)
        ·
          refine ⟨16345992939950756078758355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43589314506535349543355613 16345992939950756078758355)
          ·
            refine ⟨24518989409926134118137533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345992939950756078758355 24518989409926134118137533)
            ·
              refine ⟨9194621028722300294301575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24518989409926134118137533 9194621028722300294301575)
              ·
                refine ⟨13791931543083450441452363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194621028722300294301575 13791931543083450441452363)
                ·
                  refine ⟨20687897314625175662178545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13791931543083450441452363 20687897314625175662178545)
                  ·
                    refine ⟨15515922985968881746633909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20687897314625175662178545 15515922985968881746633909)
                    ·
                      refine ⟨1454617779934582663746929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15515922985968881746633909 1454617779934582663746929)
                      ·
                        rfl

theorem cell23_2832858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2832858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832858 prefixEnd_2832858 := by exact prefixLift 2832858
  have htrace : WordTrace (prefixWord ++ tailWord_2832858) baseStart_2832858 baseEnd_2832858 := by
    simpa [prefixWord, tailWord_2832858, baseEnd_2832858] using wordTrace_append hprefix tailTrace_2832858
  have hstable : (prefixWord ++ tailWord_2832858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832858).length < 2 ^ (prefixWord ++ tailWord_2832858).sum := by decide
  have hdescent : baseEnd_2832858 < baseStart_2832858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832882 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_2832882 : Nat := 118140960795 + 2832882 * 2 ^ 59
def prefixEnd_2832882 : Nat := 4983230072969 + 3 ^ 40 * 2832882 * 2
def baseEnd_2832882 : Nat := 484876701156763523282273

theorem tailTrace_2832882 : CollatzResearch.WordTrace tailWord_2832882 prefixEnd_2832882 484876701156763523282273 := by
  unfold tailWord_2832882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830923730739951643003225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68882463281973204381341933 25830923730739951643003225)
  ·
    refine ⟨19373192798054963732252419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25830923730739951643003225 19373192798054963732252419)
    ·
      refine ⟨29059789197082445598378629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19373192798054963732252419 29059789197082445598378629)
      ·
        refine ⟨5448710474452958549695993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29059789197082445598378629 5448710474452958549695993)
        ·
          refine ⟨4086532855839718912271995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5448710474452958549695993 4086532855839718912271995)
          ·
            refine ⟨6129799283759578368407993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086532855839718912271995 6129799283759578368407993)
            ·
              refine ⟨4597349462819683776305995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6129799283759578368407993 4597349462819683776305995)
              ·
                refine ⟨6896024194229525664458993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597349462819683776305995 6896024194229525664458993)
                ·
                  refine ⟨5172018145672144248344245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6896024194229525664458993 5172018145672144248344245)
                  ·
                    refine ⟨484876701156763523282273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5172018145672144248344245 484876701156763523282273)
                    ·
                      rfl

theorem cell23_2832882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_2832882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832882 prefixEnd_2832882 := by exact prefixLift 2832882
  have htrace : WordTrace (prefixWord ++ tailWord_2832882) baseStart_2832882 baseEnd_2832882 := by
    simpa [prefixWord, tailWord_2832882, baseEnd_2832882] using wordTrace_append hprefix tailTrace_2832882
  have hstable : (prefixWord ++ tailWord_2832882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832882).length < 2 ^ (prefixWord ++ tailWord_2832882).sum := by decide
  have hdescent : baseEnd_2832882 < baseStart_2832882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832919 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2832919 : Nat := 118140960795 + 2832919 * 2 ^ 59
def prefixEnd_2832919 : Nat := 4983230072969 + 3 ^ 40 * 2832919 * 2
def baseEnd_2832919 : Nat := 1454649102254506925084149

theorem tailTrace_2832919 : CollatzResearch.WordTrace tailWord_2832919 prefixEnd_2832919 1454649102254506925084149 := by
  unfold tailWord_2832919
  simp only [CollatzResearch.WordTrace]
  refine ⟨103325044423825761891109811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68883362949217174594073207 103325044423825761891109811)
  ·
    refine ⟨154987566635738642836664717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103325044423825761891109811 154987566635738642836664717)
    ·
      refine ⟨58120337488401991063749269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154987566635738642836664717 58120337488401991063749269)
      ·
        refine ⟨2724390819768843331113247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58120337488401991063749269 2724390819768843331113247)
        ·
          refine ⟨4086586229653264996669871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724390819768843331113247 4086586229653264996669871)
          ·
            refine ⟨6129879344479897495004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086586229653264996669871 6129879344479897495004807)
            ·
              refine ⟨9194819016719846242507211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129879344479897495004807 9194819016719846242507211)
              ·
                refine ⟨13792228525079769363760817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194819016719846242507211 13792228525079769363760817)
                ·
                  refine ⟨10344171393809827022820613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13792228525079769363760817 10344171393809827022820613)
                  ·
                    refine ⟨1939532136339342566778865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10344171393809827022820613 1939532136339342566778865)
                    ·
                      refine ⟨1454649102254506925084149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939532136339342566778865 1454649102254506925084149)
                      ·
                        rfl

theorem cell23_2832919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2832919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832919 prefixEnd_2832919 := by exact prefixLift 2832919
  have htrace : WordTrace (prefixWord ++ tailWord_2832919) baseStart_2832919 baseEnd_2832919 := by
    simpa [prefixWord, tailWord_2832919, baseEnd_2832919] using wordTrace_append hprefix tailTrace_2832919
  have hstable : (prefixWord ++ tailWord_2832919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832919).length < 2 ^ (prefixWord ++ tailWord_2832919).sum := by decide
  have hdescent : baseEnd_2832919 < baseStart_2832919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832925 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 6]
def baseStart_2832925 : Nat := 118140960795 + 2832925 * 2 ^ 59
def prefixEnd_2832925 : Nat := 4983230072969 + 3 ^ 40 * 2832925 * 2
def baseEnd_2832925 : Nat := 161628020348714877956569

theorem tailTrace_2832925 : CollatzResearch.WordTrace tailWord_2832925 prefixEnd_2832925 161628020348714877956569 := by
  unfold tailWord_2832925
  simp only [CollatzResearch.WordTrace]
  refine ⟨103325263261804024915828229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68883508841202683277218819 103325263261804024915828229)
  ·
    refine ⟨19373486861588254671717793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103325263261804024915828229 19373486861588254671717793)
    ·
      refine ⟨14530115146191191003788345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19373486861588254671717793 14530115146191191003788345)
      ·
        refine ⟨10897586359643393252841259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14530115146191191003788345 10897586359643393252841259)
        ·
          refine ⟨16346379539465089879261889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897586359643393252841259 16346379539465089879261889)
          ·
            refine ⟨12259784654598817409446417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16346379539465089879261889 12259784654598817409446417)
            ·
              refine ⟨9194838490949113057084813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12259784654598817409446417 9194838490949113057084813)
              ·
                refine ⟨3448064434105917396406805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9194838490949113057084813 3448064434105917396406805)
                ·
                  refine ⟨161628020348714877956569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3448064434105917396406805 161628020348714877956569)
                  ·
                    rfl

theorem cell23_2832925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_2832925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832925 prefixEnd_2832925 := by exact prefixLift 2832925
  have htrace : WordTrace (prefixWord ++ tailWord_2832925) baseStart_2832925 baseEnd_2832925 := by
    simpa [prefixWord, tailWord_2832925, baseEnd_2832925] using wordTrace_append hprefix tailTrace_2832925
  have hstable : (prefixWord ++ tailWord_2832925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832925).length < 2 ^ (prefixWord ++ tailWord_2832925).sum := by decide
  have hdescent : baseEnd_2832925 < baseStart_2832925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832968 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2832968 : Nat := 118140960795 + 2832968 * 2 ^ 59
def prefixEnd_2832968 : Nat := 4983230072969 + 3 ^ 40 * 2832968 * 2
def baseEnd_2832968 : Nat := 484891420935525744457141

theorem tailTrace_2832968 : CollatzResearch.WordTrace tailWord_2832968 prefixEnd_2832968 484891420935525744457141 := by
  unfold tailWord_2832968
  simp only [CollatzResearch.WordTrace]
  refine ⟨51663415800324121629821779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68884554400432162173095705 51663415800324121629821779)
  ·
    refine ⟨77495123700486182444732669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51663415800324121629821779 77495123700486182444732669)
    ·
      refine ⟨29060671387682318416774751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77495123700486182444732669 29060671387682318416774751)
      ·
        refine ⟨43591007081523477625162127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29060671387682318416774751 43591007081523477625162127)
        ·
          refine ⟨65386510622285216437743191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43591007081523477625162127 65386510622285216437743191)
          ·
            refine ⟨98079765933427824656614787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65386510622285216437743191 98079765933427824656614787)
            ·
              refine ⟨147119648900141736984922181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98079765933427824656614787 147119648900141736984922181)
              ·
                refine ⟨27584934168776575684672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147119648900141736984922181 27584934168776575684672909)
                ·
                  refine ⟨10344350313291215881752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27584934168776575684672909 10344350313291215881752341)
                  ·
                    refine ⟨484891420935525744457141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10344350313291215881752341 484891420935525744457141)
                    ·
                      rfl

theorem cell23_2832968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2832968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832968 prefixEnd_2832968 := by exact prefixLift 2832968
  have htrace : WordTrace (prefixWord ++ tailWord_2832968) baseStart_2832968 baseEnd_2832968 := by
    simpa [prefixWord, tailWord_2832968, baseEnd_2832968] using wordTrace_append hprefix tailTrace_2832968
  have hstable : (prefixWord ++ tailWord_2832968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832968).length < 2 ^ (prefixWord ++ tailWord_2832968).sum := by decide
  have hdescent : baseEnd_2832968 < baseStart_2832968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833063 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2833063 : Nat := 118140960795 + 2833063 * 2 ^ 59
def prefixEnd_2833063 : Nat := 4983230072969 + 3 ^ 40 * 2833063 * 2
def baseEnd_2833063 : Nat := 1454723043468754361683487

theorem tailTrace_2833063 : CollatzResearch.WordTrace tailWord_2833063 prefixEnd_2833063 1454723043468754361683487 := by
  unfold tailWord_2833063
  simp only [CollatzResearch.WordTrace]
  refine ⟨103330296535304074484351843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68886864356869382989567895 103330296535304074484351843)
  ·
    refine ⟨154995444802956111726527765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103330296535304074484351843 154995444802956111726527765)
    ·
      refine ⟨7265411475138567737180989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154995444802956111726527765 7265411475138567737180989)
      ·
        refine ⟨2724529303176962901442871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7265411475138567737180989 2724529303176962901442871)
        ·
          refine ⟨4086793954765444352164307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724529303176962901442871 4086793954765444352164307)
          ·
            refine ⟨6130190932148166528246461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086793954765444352164307 6130190932148166528246461)
            ·
              refine ⟨2298821599555562448092423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6130190932148166528246461 2298821599555562448092423)
              ·
                refine ⟨3448232399333343672138635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298821599555562448092423 3448232399333343672138635)
                ·
                  refine ⟨5172348599000015508207953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448232399333343672138635 5172348599000015508207953)
                  ·
                    refine ⟨3879261449250011631155965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172348599000015508207953 3879261449250011631155965)
                    ·
                      refine ⟨1454723043468754361683487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3879261449250011631155965 1454723043468754361683487)
                      ·
                        rfl

theorem cell23_2833063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2833063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833063 prefixEnd_2833063 := by exact prefixLift 2833063
  have htrace : WordTrace (prefixWord ++ tailWord_2833063) baseStart_2833063 baseEnd_2833063 := by
    simpa [prefixWord, tailWord_2833063, baseEnd_2833063] using wordTrace_append hprefix tailTrace_2833063
  have hstable : (prefixWord ++ tailWord_2833063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833063).length < 2 ^ (prefixWord ++ tailWord_2833063).sum := by decide
  have hdescent : baseEnd_2833063 < baseStart_2833063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833082 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_2833082 : Nat := 118140960795 + 2833082 * 2 ^ 59
def prefixEnd_2833082 : Nat := 4983230072969 + 3 ^ 40 * 2833082 * 2
def baseEnd_2833082 : Nat := 1454732799601189787345899

theorem tailTrace_2833082 : CollatzResearch.WordTrace tailWord_2833082 prefixEnd_2833082 1454732799601189787345899 := by
  unfold tailWord_2833082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832747380558810182323375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68887326348156827152862333 25832747380558810182323375)
  ·
    refine ⟨38749121070838215273485063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25832747380558810182323375 38749121070838215273485063)
    ·
      refine ⟨58123681606257322910227595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38749121070838215273485063 58123681606257322910227595)
      ·
        refine ⟨87185522409385984365341393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58123681606257322910227595 87185522409385984365341393)
        ·
          refine ⟨65389141807039488274006045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87185522409385984365341393 65389141807039488274006045)
          ·
            refine ⟨24520928177639808102752267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65389141807039488274006045 24520928177639808102752267)
            ·
              refine ⟨36781392266459712154128401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24520928177639808102752267 36781392266459712154128401)
              ·
                refine ⟨27586044199844784115596301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36781392266459712154128401 27586044199844784115596301)
                ·
                  refine ⟨10344766574941794043348613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27586044199844784115596301 10344766574941794043348613)
                  ·
                    refine ⟨1939643732801586383127865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10344766574941794043348613 1939643732801586383127865)
                    ·
                      refine ⟨1454732799601189787345899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939643732801586383127865 1454732799601189787345899)
                      ·
                        rfl

theorem cell23_2833082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_2833082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833082 prefixEnd_2833082 := by exact prefixLift 2833082
  have htrace : WordTrace (prefixWord ++ tailWord_2833082) baseStart_2833082 baseEnd_2833082 := by
    simpa [prefixWord, tailWord_2833082, baseEnd_2833082] using wordTrace_append hprefix tailTrace_2833082
  have hstable : (prefixWord ++ tailWord_2833082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833082).length < 2 ^ (prefixWord ++ tailWord_2833082).sum := by decide
  have hdescent : baseEnd_2833082 < baseStart_2833082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833092 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2833092 : Nat := 118140960795 + 2833092 * 2 ^ 59
def prefixEnd_2833092 : Nat := 4983230072969 + 3 ^ 40 * 2833092 * 2
def baseEnd_2833092 : Nat := 484912644802578249406951

theorem tailTrace_2833092 : CollatzResearch.WordTrace tailWord_2833092 prefixEnd_2833092 484912644802578249406951 := by
  unfold tailWord_2833092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51665677126099506218578765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68887569501466008291438353 51665677126099506218578765)
  ·
    refine ⟨19374628922287314831967037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51665677126099506218578765 19374628922287314831967037)
    ·
      refine ⟨7265485845857743061987639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19374628922287314831967037 7265485845857743061987639)
      ·
        refine ⟨10898228768786614592981459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265485845857743061987639 10898228768786614592981459)
        ·
          refine ⟨16347343153179921889472189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10898228768786614592981459 16347343153179921889472189)
          ·
            refine ⟨6130253682442470708552071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16347343153179921889472189 6130253682442470708552071)
            ·
              refine ⟨9195380523663706062828107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130253682442470708552071 9195380523663706062828107)
              ·
                refine ⟨13793070785495559094242161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9195380523663706062828107 13793070785495559094242161)
                ·
                  refine ⟨10344803089121669320681621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13793070785495559094242161 10344803089121669320681621)
                  ·
                    refine ⟨484912644802578249406951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10344803089121669320681621 484912644802578249406951)
                    ·
                      rfl

theorem cell23_2833092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2833092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833092 prefixEnd_2833092 := by exact prefixLift 2833092
  have htrace : WordTrace (prefixWord ++ tailWord_2833092) baseStart_2833092 baseEnd_2833092 := by
    simpa [prefixWord, tailWord_2833092, baseEnd_2833092] using wordTrace_append hprefix tailTrace_2833092
  have hstable : (prefixWord ++ tailWord_2833092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833092).length < 2 ^ (prefixWord ++ tailWord_2833092).sum := by decide
  have hdescent : baseEnd_2833092 < baseStart_2833092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833105 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 7]
def baseStart_2833105 : Nat := 118140960795 + 2833105 * 2 ^ 59
def prefixEnd_2833105 : Nat := 4983230072969 + 3 ^ 40 * 2833105 * 2
def baseEnd_2833105 : Nat := 161638289961804799706477

theorem tailTrace_2833105 : CollatzResearch.WordTrace tailWord_2833105 prefixEnd_2833105 161638289961804799706477 := by
  unfold tailWord_2833105
  simp only [CollatzResearch.WordTrace]
  refine ⟨103331828401151915657380769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68887885600767943771587179 103331828401151915657380769)
  ·
    refine ⟨77498871300863936743035577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103331828401151915657380769 77498871300863936743035577)
    ·
      refine ⟨58124153475647952557276683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77498871300863936743035577 58124153475647952557276683)
      ·
        refine ⟨87186230213471928835915025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58124153475647952557276683 87186230213471928835915025)
        ·
          refine ⟨65389672660103946626936269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87186230213471928835915025 65389672660103946626936269)
          ·
            refine ⟨24521127247538979985101101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65389672660103946626936269 24521127247538979985101101)
            ·
              refine ⟨9195422717827117494412913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24521127247538979985101101 9195422717827117494412913)
              ·
                refine ⟨6896567038370338120809685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9195422717827117494412913 6896567038370338120809685)
                ·
                  refine ⟨161638289961804799706477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6896567038370338120809685 161638289961804799706477)
                  ·
                    rfl

theorem cell23_2833105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_2833105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833105 prefixEnd_2833105 := by exact prefixLift 2833105
  have htrace : WordTrace (prefixWord ++ tailWord_2833105) baseStart_2833105 baseEnd_2833105 := by
    simpa [prefixWord, tailWord_2833105, baseEnd_2833105] using wordTrace_append hprefix tailTrace_2833105
  have hstable : (prefixWord ++ tailWord_2833105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833105).length < 2 ^ (prefixWord ++ tailWord_2833105).sum := by decide
  have hdescent : baseEnd_2833105 < baseStart_2833105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833116 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2833116 : Nat := 118140960795 + 2833116 * 2 ^ 59
def prefixEnd_2833116 : Nat := 4983230072969 + 3 ^ 40 * 2833116 * 2
def baseEnd_2833116 : Nat := 1454750257943442654320743

theorem tailTrace_2833116 : CollatzResearch.WordTrace tailWord_2833116 prefixEnd_2833116 1454750257943442654320743 := by
  unfold tailWord_2833116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51666114802056032268015601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68888153069408043024020801 51666114802056032268015601)
  ·
    refine ⟨38749586101542024201011701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51666114802056032268015601 38749586101542024201011701)
    ·
      refine ⟨3632773697019564768844847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38749586101542024201011701 3632773697019564768844847)
      ·
        refine ⟨5449160545529347153267271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632773697019564768844847 5449160545529347153267271)
        ·
          refine ⟨8173740818294020729900907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449160545529347153267271 8173740818294020729900907)
          ·
            refine ⟨12260611227441031094851361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173740818294020729900907 12260611227441031094851361)
            ·
              refine ⟨9195458420580773321138521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12260611227441031094851361 9195458420580773321138521)
              ·
                refine ⟨6896593815435579990853891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9195458420580773321138521 6896593815435579990853891)
                ·
                  refine ⟨10344890723153369986280837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896593815435579990853891 10344890723153369986280837)
                  ·
                    refine ⟨1939667010591256872427657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10344890723153369986280837 1939667010591256872427657)
                    ·
                      refine ⟨1454750257943442654320743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939667010591256872427657 1454750257943442654320743)
                      ·
                        rfl

theorem cell23_2833116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2833116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833116 prefixEnd_2833116 := by exact prefixLift 2833116
  have htrace : WordTrace (prefixWord ++ tailWord_2833116) baseStart_2833116 baseEnd_2833116 := by
    simpa [prefixWord, tailWord_2833116, baseEnd_2833116] using wordTrace_append hprefix tailTrace_2833116
  have hstable : (prefixWord ++ tailWord_2833116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833116).length < 2 ^ (prefixWord ++ tailWord_2833116).sum := by decide
  have hdescent : baseEnd_2833116 < baseStart_2833116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833145 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2833145 : Nat := 118140960795 + 2833145 * 2 ^ 59
def prefixEnd_2833145 : Nat := 4983230072969 + 3 ^ 40 * 2833145 * 2
def baseEnd_2833145 : Nat := 1454765148882423040858109

theorem tailTrace_2833145 : CollatzResearch.WordTrace tailWord_2833145 prefixEnd_2833145 1454765148882423040858109 := by
  unfold tailWord_2833145
  simp only [CollatzResearch.WordTrace]
  refine ⟨103333287321007002488836889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68888858214004668325891259 103333287321007002488836889)
  ·
    refine ⟨77499965490755251866627667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103333287321007002488836889 77499965490755251866627667)
    ·
      refine ⟨116249948236132877799941501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77499965490755251866627667 116249948236132877799941501)
      ·
        refine ⟨43593730588549829174978063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116249948236132877799941501 43593730588549829174978063)
        ·
          refine ⟨65390595882824743762467095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43593730588549829174978063 65390595882824743762467095)
          ·
            refine ⟨98085893824237115643700643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65390595882824743762467095 98085893824237115643700643)
            ·
              refine ⟨147128840736355673465550965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98085893824237115643700643 147128840736355673465550965)
              ·
                refine ⟨13793328819033344387395403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147128840736355673465550965 13793328819033344387395403)
                ·
                  refine ⟨20689993228550016581093105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13793328819033344387395403 20689993228550016581093105)
                  ·
                    refine ⟨15517494921412512435819829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20689993228550016581093105 15517494921412512435819829)
                    ·
                      refine ⟨1454765148882423040858109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15517494921412512435819829 1454765148882423040858109)
                      ·
                        rfl

theorem cell23_2833145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2833145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833145 prefixEnd_2833145 := by exact prefixLift 2833145
  have htrace : WordTrace (prefixWord ++ tailWord_2833145) baseStart_2833145 baseEnd_2833145 := by
    simpa [prefixWord, tailWord_2833145, baseEnd_2833145] using wordTrace_append hprefix tailTrace_2833145
  have hstable : (prefixWord ++ tailWord_2833145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833145).length < 2 ^ (prefixWord ++ tailWord_2833145).sum := by decide
  have hdescent : baseEnd_2833145 < baseStart_2833145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833150 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2833150 : Nat := 118140960795 + 2833150 * 2 ^ 59
def prefixEnd_2833150 : Nat := 4983230072969 + 3 ^ 40 * 2833150 * 2
def baseEnd_2833150 : Nat := 1454767716285695521295587

theorem tailTrace_2833150 : CollatzResearch.WordTrace tailWord_2833150 prefixEnd_2833150 1454767716285695521295587 := by
  unfold tailWord_2833150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916683710748611042846113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68888979790659258895179269 12916683710748611042846113)
  ·
    refine ⟨9687512783061458282134585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12916683710748611042846113 9687512783061458282134585)
    ·
      refine ⟨7265634587296093711600939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9687512783061458282134585 7265634587296093711600939)
      ·
        refine ⟨10898451880944140567401409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265634587296093711600939 10898451880944140567401409)
        ·
          refine ⟨8173838910708105425551057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10898451880944140567401409 8173838910708105425551057)
          ·
            refine ⟨6130379183031079069163293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8173838910708105425551057 6130379183031079069163293)
            ·
              refine ⟨2298892193636654650936235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6130379183031079069163293 2298892193636654650936235)
              ·
                refine ⟨3448338290454981976404353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298892193636654650936235 3448338290454981976404353)
                ·
                  refine ⟨2586253717841236482303265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3448338290454981976404353 2586253717841236482303265)
                  ·
                    refine ⟨1939690288380927361727449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2586253717841236482303265 1939690288380927361727449)
                    ·
                      refine ⟨1454767716285695521295587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939690288380927361727449 1454767716285695521295587)
                      ·
                        rfl

theorem cell23_2833150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2833150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833150 prefixEnd_2833150 := by exact prefixLift 2833150
  have htrace : WordTrace (prefixWord ++ tailWord_2833150) baseStart_2833150 baseEnd_2833150 := by
    simpa [prefixWord, tailWord_2833150, baseEnd_2833150] using wordTrace_append hprefix tailTrace_2833150
  have hstable : (prefixWord ++ tailWord_2833150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833150).length < 2 ^ (prefixWord ++ tailWord_2833150).sum := by decide
  have hdescent : baseEnd_2833150 < baseStart_2833150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833235 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_2833235 : Nat := 118140960795 + 2833235 * 2 ^ 59
def prefixEnd_2833235 : Nat := 4983230072969 + 3 ^ 40 * 2833235 * 2
def baseEnd_2833235 : Nat := 1454811362141327688732695

theorem tailTrace_2833235 : CollatzResearch.WordTrace tailWord_2833235 prefixEnd_2833235 1454811362141327688732695 := by
  unfold tailWord_2833235
  simp only [CollatzResearch.WordTrace]
  refine ⟨103336569890680947859613159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68891046593787298573075439 103336569890680947859613159)
  ·
    refine ⟨155004854836021421789419739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103336569890680947859613159 155004854836021421789419739)
    ·
      refine ⟨232507282254032132684129609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155004854836021421789419739 232507282254032132684129609)
      ·
        refine ⟨174380461690524099513097207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232507282254032132684129609 174380461690524099513097207)
        ·
          refine ⟨261570692535786149269645811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174380461690524099513097207 261570692535786149269645811)
          ·
            refine ⟨392356038803679223904468717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261570692535786149269645811 392356038803679223904468717)
            ·
              refine ⟨147133514551379708964175769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392356038803679223904468717 147133514551379708964175769)
              ·
                refine ⟨110350135913534781723131827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147133514551379708964175769 110350135913534781723131827)
                ·
                  refine ⟨165525203870302172584697741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110350135913534781723131827 165525203870302172584697741)
                  ·
                    refine ⟨62071951451363314719261653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165525203870302172584697741 62071951451363314719261653)
                    ·
                      refine ⟨1454811362141327688732695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62071951451363314719261653 1454811362141327688732695)
                      ·
                        rfl

theorem cell23_2833235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_2833235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833235 prefixEnd_2833235 := by exact prefixLift 2833235
  have htrace : WordTrace (prefixWord ++ tailWord_2833235) baseStart_2833235 baseEnd_2833235 := by
    simpa [prefixWord, tailWord_2833235, baseEnd_2833235] using wordTrace_append hprefix tailTrace_2833235
  have hstable : (prefixWord ++ tailWord_2833235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833235).length < 2 ^ (prefixWord ++ tailWord_2833235).sum := by decide
  have hdescent : baseEnd_2833235 < baseStart_2833235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833249 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_2833249 : Nat := 118140960795 + 2833249 * 2 ^ 59
def prefixEnd_2833249 : Nat := 4983230072969 + 3 ^ 40 * 2833249 * 2
def baseEnd_2833249 : Nat := 1454818550870490633957631

theorem tailTrace_2833249 : CollatzResearch.WordTrace tailWord_2833249 prefixEnd_2833249 1454818550870490633957631 := by
  unfold tailWord_2833249
  simp only [CollatzResearch.WordTrace]
  refine ⟨103337080512630228250622801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68891387008420152167081867 103337080512630228250622801)
  ·
    refine ⟨77502810384472671187967101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103337080512630228250622801 77502810384472671187967101)
    ·
      refine ⟨29063553894177251695487663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77502810384472671187967101 29063553894177251695487663)
      ·
        refine ⟨43595330841265877543231495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29063553894177251695487663 43595330841265877543231495)
        ·
          refine ⟨65392996261898816314847243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43595330841265877543231495 65392996261898816314847243)
          ·
            refine ⟨98089494392848224472270865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65392996261898816314847243 98089494392848224472270865)
            ·
              refine ⟨73567120794636168354203149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98089494392848224472270865 73567120794636168354203149)
              ·
                refine ⟨27587670297988563132826181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73567120794636168354203149 27587670297988563132826181)
                ·
                  refine ⟨5172688180872855587404909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27587670297988563132826181 5172688180872855587404909)
                  ·
                    refine ⟨1939758067827320845276841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5172688180872855587404909 1939758067827320845276841)
                    ·
                      refine ⟨1454818550870490633957631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939758067827320845276841 1454818550870490633957631)
                      ·
                        rfl

theorem cell23_2833249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_2833249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833249 prefixEnd_2833249 := by exact prefixLift 2833249
  have htrace : WordTrace (prefixWord ++ tailWord_2833249) baseStart_2833249 baseEnd_2833249 := by
    simpa [prefixWord, tailWord_2833249, baseEnd_2833249] using wordTrace_append hprefix tailTrace_2833249
  have hstable : (prefixWord ++ tailWord_2833249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833249).length < 2 ^ (prefixWord ++ tailWord_2833249).sum := by decide
  have hdescent : baseEnd_2833249 < baseStart_2833249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833290 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2833290 : Nat := 118140960795 + 2833290 * 2 ^ 59
def prefixEnd_2833290 : Nat := 4983230072969 + 3 ^ 40 * 2833290 * 2
def baseEnd_2833290 : Nat := 1454839603577324973544943

theorem tailTrace_2833290 : CollatzResearch.WordTrace tailWord_2833290 prefixEnd_2833290 1454839603577324973544943 := by
  unfold tailWord_2833290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25834643976370423063216331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68892383936987794835243549 25834643976370423063216331)
  ·
    refine ⟨38751965964555634594824497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25834643976370423063216331 38751965964555634594824497)
    ·
      refine ⟨29063974473416725946118373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38751965964555634594824497 29063974473416725946118373)
      ·
        refine ⟨5449495213765636114897195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29063974473416725946118373 5449495213765636114897195)
        ·
          refine ⟨8174242820648454172345793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449495213765636114897195 8174242820648454172345793)
          ·
            refine ⟨6130682115486340629259345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8174242820648454172345793 6130682115486340629259345)
            ·
              refine ⟨4598011586614755471944509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6130682115486340629259345 4598011586614755471944509)
              ·
                refine ⟨1724254344980533301979191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4598011586614755471944509 1724254344980533301979191)
                ·
                  refine ⟨2586381517470799952968787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724254344980533301979191 2586381517470799952968787)
                  ·
                    refine ⟨3879572276206199929453181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586381517470799952968787 3879572276206199929453181)
                    ·
                      refine ⟨1454839603577324973544943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3879572276206199929453181 1454839603577324973544943)
                      ·
                        rfl

theorem cell23_2833290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2833290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833290 prefixEnd_2833290 := by exact prefixLift 2833290
  have htrace : WordTrace (prefixWord ++ tailWord_2833290) baseStart_2833290 baseEnd_2833290 := by
    simpa [prefixWord, tailWord_2833290, baseEnd_2833290] using wordTrace_append hprefix tailTrace_2833290
  have hstable : (prefixWord ++ tailWord_2833290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833290).length < 2 ^ (prefixWord ++ tailWord_2833290).sum := by decide
  have hdescent : baseEnd_2833290 < baseStart_2833290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833306 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_2833306 : Nat := 118140960795 + 2833306 * 2 ^ 59
def prefixEnd_2833306 : Nat := 4983230072969 + 3 ^ 40 * 2833306 * 2
def baseEnd_2833306 : Nat := 484949273089265636981623

theorem tailTrace_2833306 : CollatzResearch.WordTrace tailWord_2833306 prefixEnd_2833306 484949273089265636981623 := by
  unfold tailWord_2833306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25834789868355931746361943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68892772982282484656965181 25834789868355931746361943)
  ·
    refine ⟨38752184802533897619542915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25834789868355931746361943 38752184802533897619542915)
    ·
      refine ⟨58128277203800846429314373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38752184802533897619542915 58128277203800846429314373)
      ·
        refine ⟨10899051975712658705496445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58128277203800846429314373 10899051975712658705496445)
        ·
          refine ⟨4087144490892247014561167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10899051975712658705496445 4087144490892247014561167)
          ·
            refine ⟨6130716736338370521841751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4087144490892247014561167 6130716736338370521841751)
            ·
              refine ⟨9196075104507555782762627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130716736338370521841751 9196075104507555782762627)
              ·
                refine ⟨13794112656761333674143941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9196075104507555782762627 13794112656761333674143941)
                ·
                  refine ⟨2586396123142750063901989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13794112656761333674143941 2586396123142750063901989)
                  ·
                    refine ⟨484949273089265636981623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586396123142750063901989 484949273089265636981623)
                    ·
                      rfl

theorem cell23_2833306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_2833306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833306 prefixEnd_2833306 := by exact prefixLift 2833306
  have htrace : WordTrace (prefixWord ++ tailWord_2833306) baseStart_2833306 baseEnd_2833306 := by
    simpa [prefixWord, tailWord_2833306, baseEnd_2833306] using wordTrace_append hprefix tailTrace_2833306
  have hstable : (prefixWord ++ tailWord_2833306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833306).length < 2 ^ (prefixWord ++ tailWord_2833306).sum := by decide
  have hdescent : baseEnd_2833306 < baseStart_2833306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833313 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2833313 : Nat := 118140960795 + 2833313 * 2 ^ 59
def prefixEnd_2833313 : Nat := 4983230072969 + 3 ^ 40 * 2833313 * 2
def baseEnd_2833313 : Nat := 1454851413632378383557337

theorem tailTrace_2833313 : CollatzResearch.WordTrace tailWord_2833313 prefixEnd_2833313 1454851413632378383557337 := by
  unfold tailWord_2833313
  simp only [CollatzResearch.WordTrace]
  refine ⟨103339414784398367180952593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68892943189598911453968395 103339414784398367180952593)
  ·
    refine ⟨77504561088298775385714445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103339414784398367180952593 77504561088298775385714445)
    ·
      refine ⟨29064210408112040769642917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77504561088298775385714445 29064210408112040769642917)
      ·
        refine ⟨5449539451521007644308047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29064210408112040769642917 5449539451521007644308047)
        ·
          refine ⟨8174309177281511466462071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449539451521007644308047 8174309177281511466462071)
          ·
            refine ⟨12261463765922267199693107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174309177281511466462071 12261463765922267199693107)
            ·
              refine ⟨18392195648883400799539661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261463765922267199693107 18392195648883400799539661)
              ·
                refine ⟨6897073368331275299827373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18392195648883400799539661 6897073368331275299827373)
                ·
                  refine ⟨2586402513124228237435265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6897073368331275299827373 2586402513124228237435265)
                  ·
                    refine ⟨1939801884843171178076449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2586402513124228237435265 1939801884843171178076449)
                    ·
                      refine ⟨1454851413632378383557337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939801884843171178076449 1454851413632378383557337)
                      ·
                        rfl

theorem cell23_2833313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2833313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833313 prefixEnd_2833313 := by exact prefixLift 2833313
  have htrace : WordTrace (prefixWord ++ tailWord_2833313) baseStart_2833313 baseEnd_2833313 := by
    simpa [prefixWord, tailWord_2833313, baseEnd_2833313] using wordTrace_append hprefix tailTrace_2833313
  have hstable : (prefixWord ++ tailWord_2833313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833313).length < 2 ^ (prefixWord ++ tailWord_2833313).sum := by decide
  have hdescent : baseEnd_2833313 < baseStart_2833313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833392 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 9]
def baseStart_2833392 : Nat := 118140960795 + 2833392 * 2 ^ 59
def prefixEnd_2833392 : Nat := 4983230072969 + 3 ^ 40 * 2833392 * 2
def baseEnd_2833392 : Nat := 161654664289342619385497

theorem tailTrace_2833392 : CollatzResearch.WordTrace tailWord_2833392 prefixEnd_2833392 161654664289342619385497 := by
  unfold tailWord_2833392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51671148075556081836539215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68894864100741442448718953 51671148075556081836539215)
  ·
    refine ⟨77506722113334122754808823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51671148075556081836539215 77506722113334122754808823)
    ·
      refine ⟨116260083170001184132213235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77506722113334122754808823 116260083170001184132213235)
      ·
        refine ⟨174390124755001776198319853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116260083170001184132213235 174390124755001776198319853)
        ·
          refine ⟨65396296783125666074369945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174390124755001776198319853 65396296783125666074369945)
          ·
            refine ⟨49047222587344249555777459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65396296783125666074369945 49047222587344249555777459)
            ·
              refine ⟨73570833881016374333666189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49047222587344249555777459 73570833881016374333666189)
              ·
                refine ⟨27589062705381140375124821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73570833881016374333666189 27589062705381140375124821)
                ·
                  refine ⟨161654664289342619385497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27589062705381140375124821 161654664289342619385497)
                  ·
                    rfl

theorem cell23_2833392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_2833392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833392 prefixEnd_2833392 := by exact prefixLift 2833392
  have htrace : WordTrace (prefixWord ++ tailWord_2833392) baseStart_2833392 baseEnd_2833392 := by
    simpa [prefixWord, tailWord_2833392, baseEnd_2833392] using wordTrace_append hprefix tailTrace_2833392
  have hstable : (prefixWord ++ tailWord_2833392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833392).length < 2 ^ (prefixWord ++ tailWord_2833392).sum := by decide
  have hdescent : baseEnd_2833392 < baseStart_2833392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833420 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_2833420 : Nat := 118140960795 + 2833420 * 2 ^ 59
def prefixEnd_2833420 : Nat := 4983230072969 + 3 ^ 40 * 2833420 * 2
def baseEnd_2833420 : Nat := 1454906356062409464919345

theorem tailTrace_2833420 : CollatzResearch.WordTrace tailWord_2833420 prefixEnd_2833420 1454906356062409464919345 := by
  unfold tailWord_2833420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51671658697505362227548857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68895544930007149636731809 51671658697505362227548857)
  ·
    refine ⟨38753744023129021670661643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51671658697505362227548857 38753744023129021670661643)
    ·
      refine ⟨58130616034693532505992465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38753744023129021670661643 58130616034693532505992465)
      ·
        refine ⟨43597962026020149379494349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58130616034693532505992465 43597962026020149379494349)
        ·
          refine ⟨16349235759757556017310381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43597962026020149379494349 16349235759757556017310381)
          ·
            refine ⟨6130963409909083506491393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16349235759757556017310381 6130963409909083506491393)
            ·
              refine ⟨4598222557431812629868545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6130963409909083506491393 4598222557431812629868545)
              ·
                refine ⟨3448666918073859472401409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4598222557431812629868545 3448666918073859472401409)
                ·
                  refine ⟨2586500188555394604301057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3448666918073859472401409 2586500188555394604301057)
                  ·
                    refine ⟨1939875141416545953225793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2586500188555394604301057 1939875141416545953225793)
                    ·
                      refine ⟨1454906356062409464919345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939875141416545953225793 1454906356062409464919345)
                      ·
                        rfl

theorem cell23_2833420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_2833420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833420 prefixEnd_2833420 := by exact prefixLift 2833420
  have htrace : WordTrace (prefixWord ++ tailWord_2833420) baseStart_2833420 baseEnd_2833420 := by
    simpa [prefixWord, tailWord_2833420, baseEnd_2833420] using wordTrace_append hprefix tailTrace_2833420
  have hstable : (prefixWord ++ tailWord_2833420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833420).length < 2 ^ (prefixWord ++ tailWord_2833420).sum := by decide
  have hdescent : baseEnd_2833420 < baseStart_2833420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833460 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2833460 : Nat := 118140960795 + 2833460 * 2 ^ 59
def prefixEnd_2833460 : Nat := 4983230072969 + 3 ^ 40 * 2833460 * 2
def baseEnd_2833460 : Nat := 161658543920954367602129

theorem tailTrace_2833460 : CollatzResearch.WordTrace tailWord_2833460 prefixEnd_2833460 161658543920954367602129 := by
  unfold tailWord_2833460
  simp only [CollatzResearch.WordTrace]
  refine ⟨51672388157432905643276917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68896517543243874191035889 51672388157432905643276917)
  ·
    refine ⟨4844286389759334904057211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51672388157432905643276917 4844286389759334904057211)
    ·
      refine ⟨7266429584639002356085817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4844286389759334904057211 7266429584639002356085817)
      ·
        refine ⟨5449822188479251767064363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7266429584639002356085817 5449822188479251767064363)
        ·
          refine ⟨8174733282718877650596545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449822188479251767064363 8174733282718877650596545)
          ·
            refine ⟨6131049962039158237947409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8174733282718877650596545 6131049962039158237947409)
            ·
              refine ⟨4598287471529368678460557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6131049962039158237947409 4598287471529368678460557)
              ·
                refine ⟨1724357801823513254422709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4598287471529368678460557 1724357801823513254422709)
                ·
                  refine ⟨161658543920954367602129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724357801823513254422709 161658543920954367602129)
                  ·
                    rfl

theorem cell23_2833460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2833460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833460 prefixEnd_2833460 := by exact prefixLift 2833460
  have htrace : WordTrace (prefixWord ++ tailWord_2833460) baseStart_2833460 baseEnd_2833460 := by
    simpa [prefixWord, tailWord_2833460, baseEnd_2833460] using wordTrace_append hprefix tailTrace_2833460
  have hstable : (prefixWord ++ tailWord_2833460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833460).length < 2 ^ (prefixWord ++ tailWord_2833460).sum := by decide
  have hdescent : baseEnd_2833460 < baseStart_2833460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833537 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2833537 : Nat := 118140960795 + 2833537 * 2 ^ 59
def prefixEnd_2833537 : Nat := 4983230072969 + 3 ^ 40 * 2833537 * 2
def baseEnd_2833537 : Nat := 484988811099661835718769

theorem tailTrace_2833537 : CollatzResearch.WordTrace tailWord_2833537 prefixEnd_2833537 484988811099661835718769 := by
  unfold tailWord_2833537
  simp only [CollatzResearch.WordTrace]
  refine ⟨103347584735586853437106865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68898389823724568958071243 103347584735586853437106865)
  ·
    refine ⟨77510688551690140077830149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103347584735586853437106865 77510688551690140077830149)
    ·
      refine ⟨14533254103441901264593153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77510688551690140077830149 14533254103441901264593153)
      ·
        refine ⟨10899940577581425948444865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14533254103441901264593153 10899940577581425948444865)
        ·
          refine ⟨8174955433186069461333649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10899940577581425948444865 8174955433186069461333649)
          ·
            refine ⟨6131216574889552096000237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8174955433186069461333649 6131216574889552096000237)
            ·
              refine ⟨2299206215583582036000089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6131216574889552096000237 2299206215583582036000089)
              ·
                refine ⟨1724404661687686527000067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299206215583582036000089 1724404661687686527000067)
                ·
                  refine ⟨2586606992531529790500101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724404661687686527000067 2586606992531529790500101)
                  ·
                    refine ⟨484988811099661835718769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586606992531529790500101 484988811099661835718769)
                    ·
                      rfl

theorem cell23_2833537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2833537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833537 prefixEnd_2833537 := by exact prefixLift 2833537
  have htrace : WordTrace (prefixWord ++ tailWord_2833537) baseStart_2833537 baseEnd_2833537 := by
    simpa [prefixWord, tailWord_2833537, baseEnd_2833537] using wordTrace_append hprefix tailTrace_2833537
  have hstable : (prefixWord ++ tailWord_2833537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833537).length < 2 ^ (prefixWord ++ tailWord_2833537).sum := by decide
  have hdescent : baseEnd_2833537 < baseStart_2833537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833546 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_2833546 : Nat := 118140960795 + 2833546 * 2 ^ 59
def prefixEnd_2833546 : Nat := 4983230072969 + 3 ^ 40 * 2833546 * 2
def baseEnd_2833546 : Nat := 484990351541625323981255

theorem tailTrace_2833546 : CollatzResearch.WordTrace tailWord_2833546 prefixEnd_2833546 484990351541625323981255 := by
  unfold tailWord_2833546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25836978248138561993546123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68898608661702831982789661 25836978248138561993546123)
  ·
    refine ⟨38755467372207842990319185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25836978248138561993546123 38755467372207842990319185)
    ·
      refine ⟨29066600529155882242739389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38755467372207842990319185 29066600529155882242739389)
      ·
        refine ⟨10899975198433455841027271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29066600529155882242739389 10899975198433455841027271)
        ·
          refine ⟨16349962797650183761540907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899975198433455841027271 16349962797650183761540907)
          ·
            refine ⟨24524944196475275642311361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16349962797650183761540907 24524944196475275642311361)
            ·
              refine ⟨18393708147356456731733521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24524944196475275642311361 18393708147356456731733521)
              ·
                refine ⟨13795281110517342548800141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18393708147356456731733521 13795281110517342548800141)
                ·
                  refine ⟨5173230416444003455800053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13795281110517342548800141 5173230416444003455800053)
                  ·
                    refine ⟨484990351541625323981255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173230416444003455800053 484990351541625323981255)
                    ·
                      rfl

theorem cell23_2833546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_2833546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833546 prefixEnd_2833546 := by exact prefixLift 2833546
  have htrace : WordTrace (prefixWord ++ tailWord_2833546) baseStart_2833546 baseEnd_2833546 := by
    simpa [prefixWord, tailWord_2833546, baseEnd_2833546] using wordTrace_append hprefix tailTrace_2833546
  have hstable : (prefixWord ++ tailWord_2833546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833546).length < 2 ^ (prefixWord ++ tailWord_2833546).sum := by decide
  have hdescent : baseEnd_2833546 < baseStart_2833546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833550 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_2833550 : Nat := 118140960795 + 2833550 * 2 ^ 59
def prefixEnd_2833550 : Nat := 4983230072969 + 3 ^ 40 * 2833550 * 2
def baseEnd_2833550 : Nat := 161663678727499328477083

theorem tailTrace_2833550 : CollatzResearch.WordTrace tailWord_2833550 prefixEnd_2833550 161663678727499328477083 := by
  unfold tailWord_2833550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918507360567469582166263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68898705923026504438220069 12918507360567469582166263)
  ·
    refine ⟨19377761040851204373249395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12918507360567469582166263 19377761040851204373249395)
    ·
      refine ⟨29066641561276806559874093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19377761040851204373249395 29066641561276806559874093)
      ·
        refine ⟨10899990585478802459952785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29066641561276806559874093 10899990585478802459952785)
        ·
          refine ⟨8174992939109101844964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10899990585478802459952785 8174992939109101844964589)
          ·
            refine ⟨3065622352165913191861721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8174992939109101844964589 3065622352165913191861721)
            ·
              refine ⟨2299216764124434893896291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065622352165913191861721 2299216764124434893896291)
              ·
                refine ⟨3448825146186652340844437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299216764124434893896291 3448825146186652340844437)
                ·
                  refine ⟨161663678727499328477083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3448825146186652340844437 161663678727499328477083)
                  ·
                    rfl

theorem cell23_2833550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_2833550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833550 prefixEnd_2833550 := by exact prefixLift 2833550
  have htrace : WordTrace (prefixWord ++ tailWord_2833550) baseStart_2833550 baseEnd_2833550 := by
    simpa [prefixWord, tailWord_2833550, baseEnd_2833550] using wordTrace_append hprefix tailTrace_2833550
  have hstable : (prefixWord ++ tailWord_2833550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833550).length < 2 ^ (prefixWord ++ tailWord_2833550).sum := by decide
  have hdescent : baseEnd_2833550 < baseStart_2833550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833589 : List Nat := [1, 3, 3, 16]
def baseStart_2833589 : Nat := 118140960795 + 2833589 * 2 ^ 59
def prefixEnd_2833589 : Nat := 4983230072969 + 3 ^ 40 * 2833589 * 2
def baseEnd_2833589 : Nat := 665291785227718017241

theorem tailTrace_2833589 : CollatzResearch.WordTrace tailWord_2833589 prefixEnd_2833589 665291785227718017241 := by
  unfold tailWord_2833589
  simp only [CollatzResearch.WordTrace]
  refine ⟨103349481331398466317999821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68899654220932310878666547 103349481331398466317999821)
  ·
    refine ⟨38756055499274424869249933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103349481331398466317999821 38756055499274424869249933)
    ·
      refine ⟨14533520812227909325968725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38756055499274424869249933 14533520812227909325968725)
      ·
        refine ⟨665291785227718017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 14533520812227909325968725 665291785227718017241)
        ·
          rfl

theorem cell23_2833589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 16].length) (baseStart_2833589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833589 prefixEnd_2833589 := by exact prefixLift 2833589
  have htrace : WordTrace (prefixWord ++ tailWord_2833589) baseStart_2833589 baseEnd_2833589 := by
    simpa [prefixWord, tailWord_2833589, baseEnd_2833589] using wordTrace_append hprefix tailTrace_2833589
  have hstable : (prefixWord ++ tailWord_2833589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833589).length < 2 ^ (prefixWord ++ tailWord_2833589).sum := by decide
  have hdescent : baseEnd_2833589 < baseStart_2833589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833593 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_2833593 : Nat := 118140960795 + 2833593 * 2 ^ 59
def prefixEnd_2833593 : Nat := 4983230072969 + 3 ^ 40 * 2833593 * 2
def baseEnd_2833593 : Nat := 484998396071879096018683

theorem tailTrace_2833593 : CollatzResearch.WordTrace tailWord_2833593 prefixEnd_2833593 484998396071879096018683 := by
  unfold tailWord_2833593
  simp only [CollatzResearch.WordTrace]
  refine ⟨103349627223383975001145433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68899751482255983334096955 103349627223383975001145433)
  ·
    refine ⟨77512220417537981250859075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103349627223383975001145433 77512220417537981250859075)
    ·
      refine ⟨116268330626306971876288613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77512220417537981250859075 116268330626306971876288613)
      ·
        refine ⟨21800311992432557226804115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116268330626306971876288613 21800311992432557226804115)
        ·
          refine ⟨32700467988648835840206173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21800311992432557226804115 32700467988648835840206173)
          ·
            refine ⟨12262675495743313440077315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32700467988648835840206173 12262675495743313440077315)
            ·
              refine ⟨18394013243614970160115973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12262675495743313440077315 18394013243614970160115973)
              ·
                refine ⟨3448877483177806905021745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18394013243614970160115973 3448877483177806905021745)
                ·
                  refine ⟨2586658112383355178766309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3448877483177806905021745 2586658112383355178766309)
                  ·
                    refine ⟨484998396071879096018683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586658112383355178766309 484998396071879096018683)
                    ·
                      rfl

theorem cell23_2833593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_2833593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833593 prefixEnd_2833593 := by exact prefixLift 2833593
  have htrace : WordTrace (prefixWord ++ tailWord_2833593) baseStart_2833593 baseEnd_2833593 := by
    simpa [prefixWord, tailWord_2833593, baseEnd_2833593] using wordTrace_append hprefix tailTrace_2833593
  have hstable : (prefixWord ++ tailWord_2833593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833593).length < 2 ^ (prefixWord ++ tailWord_2833593).sum := by decide
  have hdescent : baseEnd_2833593 < baseStart_2833593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833633 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2833633 : Nat := 118140960795 + 2833633 * 2 ^ 59
def prefixEnd_2833633 : Nat := 4983230072969 + 3 ^ 40 * 2833633 * 2
def baseEnd_2833633 : Nat := 1455015727441817131555865

theorem tailTrace_2833633 : CollatzResearch.WordTrace tailWord_2833633 prefixEnd_2833633 1455015727441817131555865 := by
  unfold tailWord_2833633
  simp only [CollatzResearch.WordTrace]
  refine ⟨103351086143239061832601553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68900724095492707888401035 103351086143239061832601553)
  ·
    refine ⟨77513314607429296374451165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103351086143239061832601553 77513314607429296374451165)
    ·
      refine ⟨29067492977785986140419187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77513314607429296374451165 29067492977785986140419187)
      ·
        refine ⟨43601239466678979210628781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29067492977785986140419187 43601239466678979210628781)
        ·
          refine ⟨16350464800004617203985793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43601239466678979210628781 16350464800004617203985793)
          ·
            refine ⟨12262848600003462902989345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16350464800004617203985793 12262848600003462902989345)
            ·
              refine ⟨9197136450002597177242009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12262848600003462902989345 9197136450002597177242009)
              ·
                refine ⟨6897852337501947882931507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9197136450002597177242009 6897852337501947882931507)
                ·
                  refine ⟨10346778506252921824397261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6897852337501947882931507 10346778506252921824397261)
                  ·
                    refine ⟨3880041939844845684148973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10346778506252921824397261 3880041939844845684148973)
                    ·
                      refine ⟨1455015727441817131555865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880041939844845684148973 1455015727441817131555865)
                      ·
                        rfl

theorem cell23_2833633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2833633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833633 prefixEnd_2833633 := by exact prefixLift 2833633
  have htrace : WordTrace (prefixWord ++ tailWord_2833633) baseStart_2833633 baseEnd_2833633 := by
    simpa [prefixWord, tailWord_2833633, baseEnd_2833633] using wordTrace_append hprefix tailTrace_2833633
  have hstable : (prefixWord ++ tailWord_2833633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833633).length < 2 ^ (prefixWord ++ tailWord_2833633).sum := by decide
  have hdescent : baseEnd_2833633 < baseStart_2833633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833667 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 2, 1, 3]
def baseStart_2833667 : Nat := 118140960795 + 2833667 * 2 ^ 59
def prefixEnd_2833667 : Nat := 4983230072969 + 3 ^ 40 * 2833667 * 2
def baseEnd_2833667 : Nat := 1455033185784069998530709

theorem tailTrace_2833667 : CollatzResearch.WordTrace tailWord_2833667 prefixEnd_2833667 1455033185784069998530709 := by
  unfold tailWord_2833667
  simp only [CollatzResearch.WordTrace]
  refine ⟨103352326225115885639339255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68901550816743923759559503 103352326225115885639339255)
  ·
    refine ⟨155028489337673828459008883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103352326225115885639339255 155028489337673828459008883)
    ·
      refine ⟨232542734006510742688513325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155028489337673828459008883 232542734006510742688513325)
      ·
        refine ⟨87203525252441528508192497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232542734006510742688513325 87203525252441528508192497)
        ·
          refine ⟨65402643939331146381144373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87203525252441528508192497 65402643939331146381144373)
          ·
            refine ⟨6131497869312294973232285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65402643939331146381144373 6131497869312294973232285)
            ·
              refine ⟨2299311700992110614962107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6131497869312294973232285 2299311700992110614962107)
              ·
                refine ⟨3448967551488165922443161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299311700992110614962107 3448967551488165922443161)
                ·
                  refine ⟨2586725663616124441832371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3448967551488165922443161 2586725663616124441832371)
                  ·
                    refine ⟨3880088495424186662748557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586725663616124441832371 3880088495424186662748557)
                    ·
                      refine ⟨1455033185784069998530709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880088495424186662748557 1455033185784069998530709)
                      ·
                        rfl

theorem cell23_2833667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_2833667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833667 prefixEnd_2833667 := by exact prefixLift 2833667
  have htrace : WordTrace (prefixWord ++ tailWord_2833667) baseStart_2833667 baseEnd_2833667 := by
    simpa [prefixWord, tailWord_2833667, baseEnd_2833667] using wordTrace_append hprefix tailTrace_2833667
  have hstable : (prefixWord ++ tailWord_2833667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833667).length < 2 ^ (prefixWord ++ tailWord_2833667).sum := by decide
  have hdescent : baseEnd_2833667 < baseStart_2833667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833693 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2833693 : Nat := 118140960795 + 2833693 * 2 ^ 59
def prefixEnd_2833693 : Nat := 4983230072969 + 3 ^ 40 * 2833693 * 2
def baseEnd_2833693 : Nat := 1455046536281086896805589

theorem tailTrace_2833693 : CollatzResearch.WordTrace tailWord_2833693 prefixEnd_2833693 1455046536281086896805589 := by
  unfold tailWord_2833693
  simp only [CollatzResearch.WordTrace]
  refine ⟨103353274523021692079785733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68902183015347794719857155 103353274523021692079785733)
  ·
    refine ⟨19378738973066567264959825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103353274523021692079785733 19378738973066567264959825)
    ·
      refine ⟨14534054229799925448719869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19378738973066567264959825 14534054229799925448719869)
      ·
        refine ⟨5450270336174972043269951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14534054229799925448719869 5450270336174972043269951)
        ·
          refine ⟨8175405504262458064904927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450270336174972043269951 8175405504262458064904927)
          ·
            refine ⟨12263108256393687097357391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8175405504262458064904927 12263108256393687097357391)
            ·
              refine ⟨18394662384590530646036087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12263108256393687097357391 18394662384590530646036087)
              ·
                refine ⟨27591993576885795969054131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18394662384590530646036087 27591993576885795969054131)
                ·
                  refine ⟨41387990365328693953581197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27591993576885795969054131 41387990365328693953581197)
                  ·
                    refine ⟨15520496386998260232592949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41387990365328693953581197 15520496386998260232592949)
                    ·
                      refine ⟨1455046536281086896805589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15520496386998260232592949 1455046536281086896805589)
                      ·
                        rfl

theorem cell23_2833693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2833693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833693 prefixEnd_2833693 := by exact prefixLift 2833693
  have htrace : WordTrace (prefixWord ++ tailWord_2833693) baseStart_2833693 baseEnd_2833693 := by
    simpa [prefixWord, tailWord_2833693, baseEnd_2833693] using wordTrace_append hprefix tailTrace_2833693
  have hstable : (prefixWord ++ tailWord_2833693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833693).length < 2 ^ (prefixWord ++ tailWord_2833693).sum := by decide
  have hdescent : baseEnd_2833693 < baseStart_2833693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833713 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 7]
def baseStart_2833713 : Nat := 118140960795 + 2833713 * 2 ^ 59
def prefixEnd_2833713 : Nat := 4983230072969 + 3 ^ 40 * 2833713 * 2
def baseEnd_2833713 : Nat := 161672978432686313172833

theorem tailTrace_2833713 : CollatzResearch.WordTrace tailWord_2833713 prefixEnd_2833713 161672978432686313172833 := by
  unfold tailWord_2833713
  simp only [CollatzResearch.WordTrace]
  refine ⟨103354003982949235495513793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68902669321966156997009195 103354003982949235495513793)
  ·
    refine ⟨77515502987211926621635345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103354003982949235495513793 77515502987211926621635345)
    ·
      refine ⟨58136627240408944966226509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77515502987211926621635345 58136627240408944966226509)
      ·
        refine ⟨21801235215153354362334941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58136627240408944966226509 21801235215153354362334941)
        ·
          refine ⟨8175463205682507885875603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21801235215153354362334941 8175463205682507885875603)
          ·
            refine ⟨12263194808523761828813405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8175463205682507885875603 12263194808523761828813405)
            ·
              refine ⟨4598698053196410685805027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12263194808523761828813405 4598698053196410685805027)
              ·
                refine ⟨6898047079794616028707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598698053196410685805027 6898047079794616028707541)
                ·
                  refine ⟨161672978432686313172833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6898047079794616028707541 161672978432686313172833)
                  ·
                    rfl

theorem cell23_2833713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_2833713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833713 prefixEnd_2833713 := by exact prefixLift 2833713
  have htrace : WordTrace (prefixWord ++ tailWord_2833713) baseStart_2833713 baseEnd_2833713 := by
    simpa [prefixWord, tailWord_2833713, baseEnd_2833713] using wordTrace_append hprefix tailTrace_2833713
  have hstable : (prefixWord ++ tailWord_2833713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833713).length < 2 ^ (prefixWord ++ tailWord_2833713).sum := by decide
  have hdescent : baseEnd_2833713 < baseStart_2833713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833718 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2833718 : Nat := 118140960795 + 2833718 * 2 ^ 59
def prefixEnd_2833718 : Nat := 4983230072969 + 3 ^ 40 * 2833718 * 2
def baseEnd_2833718 : Nat := 1455059373297449298992975

theorem tailTrace_2833718 : CollatzResearch.WordTrace tailWord_2833718 prefixEnd_2833718 1455059373297449298992975 := by
  unfold tailWord_2833718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459636646745695084340363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68902790898620747566297205 6459636646745695084340363)
  ·
    refine ⟨9689454970118542626510545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459636646745695084340363 9689454970118542626510545)
    ·
      refine ⟨7267091227588906969882909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9689454970118542626510545 7267091227588906969882909)
      ·
        refine ⟨2725159210345840113706091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7267091227588906969882909 2725159210345840113706091)
        ·
          refine ⟨4087738815518760170559137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725159210345840113706091 4087738815518760170559137)
          ·
            refine ⟨3065804111639070127919353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4087738815518760170559137 3065804111639070127919353)
            ·
              refine ⟨2299353083729302595939515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065804111639070127919353 2299353083729302595939515)
              ·
                refine ⟨3449029625593953893909273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299353083729302595939515 3449029625593953893909273)
                ·
                  refine ⟨2586772219195465420431955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449029625593953893909273 2586772219195465420431955)
                  ·
                    refine ⟨3880158328793198130647933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586772219195465420431955 3880158328793198130647933)
                    ·
                      refine ⟨1455059373297449298992975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880158328793198130647933 1455059373297449298992975)
                      ·
                        rfl

theorem cell23_2833718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2833718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833718 prefixEnd_2833718 := by exact prefixLift 2833718
  have htrace : WordTrace (prefixWord ++ tailWord_2833718) baseStart_2833718 baseEnd_2833718 := by
    simpa [prefixWord, tailWord_2833718, baseEnd_2833718] using wordTrace_append hprefix tailTrace_2833718
  have hstable : (prefixWord ++ tailWord_2833718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833718).length < 2 ^ (prefixWord ++ tailWord_2833718).sum := by decide
  have hdescent : baseEnd_2833718 < baseStart_2833718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833724 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_2833724 : Nat := 118140960795 + 2833724 * 2 ^ 59
def prefixEnd_2833724 : Nat := 4983230072969 + 3 ^ 40 * 2833724 * 2
def baseEnd_2833724 : Nat := 1455062454181376275517947

theorem tailTrace_2833724 : CollatzResearch.WordTrace tailWord_2833724 prefixEnd_2833724 1455062454181376275517947 := by
  unfold tailWord_2833724
  simp only [CollatzResearch.WordTrace]
  refine ⟨51677202592954692187082113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68902936790606256249442817 51677202592954692187082113)
  ·
    refine ⟨38757901944716019140311585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51677202592954692187082113 38757901944716019140311585)
    ·
      refine ⟨29068426458537014355233689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38757901944716019140311585 29068426458537014355233689)
      ·
        refine ⟨21801319843902760766425267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29068426458537014355233689 21801319843902760766425267)
        ·
          refine ⟨32701979765854141149637901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21801319843902760766425267 32701979765854141149637901)
          ·
            refine ⟨12263242412195302931114213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32701979765854141149637901 12263242412195302931114213)
            ·
              refine ⟨2299357952286619299583915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12263242412195302931114213 2299357952286619299583915)
              ·
                refine ⟨3449036928429928949375873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299357952286619299583915 3449036928429928949375873)
                ·
                  refine ⟨2586777696322446712031905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449036928429928949375873 2586777696322446712031905)
                  ·
                    refine ⟨1940083272241835034023929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2586777696322446712031905 1940083272241835034023929)
                    ·
                      refine ⟨1455062454181376275517947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940083272241835034023929 1455062454181376275517947)
                      ·
                        rfl

theorem cell23_2833724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_2833724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833724 prefixEnd_2833724 := by exact prefixLift 2833724
  have htrace : WordTrace (prefixWord ++ tailWord_2833724) baseStart_2833724 baseEnd_2833724 := by
    simpa [prefixWord, tailWord_2833724, baseEnd_2833724] using wordTrace_append hprefix tailTrace_2833724
  have hstable : (prefixWord ++ tailWord_2833724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833724).length < 2 ^ (prefixWord ++ tailWord_2833724).sum := by decide
  have hdescent : baseEnd_2833724 < baseStart_2833724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833736 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2833736 : Nat := 118140960795 + 2833736 * 2 ^ 59
def prefixEnd_2833736 : Nat := 4983230072969 + 3 ^ 40 * 2833736 * 2
def baseEnd_2833736 : Nat := 1455068615949230228567891

theorem tailTrace_2833736 : CollatzResearch.WordTrace tailWord_2833736 prefixEnd_2833736 1455068615949230228567891 := by
  unfold tailWord_2833736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51677421430932955211800531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68903228574577273615734041 51677421430932955211800531)
  ·
    refine ⟨77516132146399432817700797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51677421430932955211800531 77516132146399432817700797)
    ·
      refine ⟨29068549554899787306637799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77516132146399432817700797 29068549554899787306637799)
      ·
        refine ⟨43602824332349680959956699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29068549554899787306637799 43602824332349680959956699)
        ·
          refine ⟨65404236498524521439935049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43602824332349680959956699 65404236498524521439935049)
          ·
            refine ⟨49053177373893391079951287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65404236498524521439935049 49053177373893391079951287)
            ·
              refine ⟨73579766060840086619926931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49053177373893391079951287 73579766060840086619926931)
              ·
                refine ⟨110369649091260129929890397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73579766060840086619926931 110369649091260129929890397)
                ·
                  refine ⟨41388618409222548723708899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110369649091260129929890397 41388618409222548723708899)
                  ·
                    refine ⟨62082927613833823085563349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41388618409222548723708899 62082927613833823085563349)
                    ·
                      refine ⟨1455068615949230228567891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62082927613833823085563349 1455068615949230228567891)
                      ·
                        rfl

theorem cell23_2833736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2833736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833736 prefixEnd_2833736 := by exact prefixLift 2833736
  have htrace : WordTrace (prefixWord ++ tailWord_2833736) baseStart_2833736 baseEnd_2833736 := by
    simpa [prefixWord, tailWord_2833736, baseEnd_2833736] using wordTrace_append hprefix tailTrace_2833736
  have hstable : (prefixWord ++ tailWord_2833736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833736).length < 2 ^ (prefixWord ++ tailWord_2833736).sum := by decide
  have hdescent : baseEnd_2833736 < baseStart_2833736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833783 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_2833783 : Nat := 118140960795 + 2833783 * 2 ^ 59
def prefixEnd_2833783 : Nat := 4983230072969 + 3 ^ 40 * 2833783 * 2
def baseEnd_2833783 : Nat := 1455092749539991544680175

theorem tailTrace_2833783 : CollatzResearch.WordTrace tailWord_2833783 prefixEnd_2833783 1455092749539991544680175 := by
  unfold tailWord_2833783
  simp only [CollatzResearch.WordTrace]
  refine ⟨103356557092695637450562003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68904371395130424967041335 103356557092695637450562003)
  ·
    refine ⟨155034835639043456175843005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103356557092695637450562003 155034835639043456175843005)
    ·
      refine ⟨58138063364641296065941127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155034835639043456175843005 58138063364641296065941127)
      ·
        refine ⟨87207095046961944098911691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58138063364641296065941127 87207095046961944098911691)
        ·
          refine ⟨130810642570442916148367537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87207095046961944098911691 130810642570442916148367537)
          ·
            refine ⟨98107981927832187111275653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130810642570442916148367537 98107981927832187111275653)
            ·
              refine ⟨18395246611468535083364185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98107981927832187111275653 18395246611468535083364185)
              ·
                refine ⟨13796434958601401312523139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18395246611468535083364185 13796434958601401312523139)
                ·
                  refine ⟨20694652437902101968784709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796434958601401312523139 20694652437902101968784709)
                  ·
                    refine ⟨3880247332106644119147133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20694652437902101968784709 3880247332106644119147133)
                    ·
                      refine ⟨1455092749539991544680175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880247332106644119147133 1455092749539991544680175)
                      ·
                        rfl

theorem cell23_2833783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_2833783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833783 prefixEnd_2833783 := by exact prefixLift 2833783
  have htrace : WordTrace (prefixWord ++ tailWord_2833783) baseStart_2833783 baseEnd_2833783 := by
    simpa [prefixWord, tailWord_2833783, baseEnd_2833783] using wordTrace_append hprefix tailTrace_2833783
  have hstable : (prefixWord ++ tailWord_2833783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833783).length < 2 ^ (prefixWord ++ tailWord_2833783).sum := by decide
  have hdescent : baseEnd_2833783 < baseStart_2833783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833794 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2833794 : Nat := 118140960795 + 2833794 * 2 ^ 59
def prefixEnd_2833794 : Nat := 4983230072969 + 3 ^ 40 * 2833794 * 2
def baseEnd_2833794 : Nat := 485032799275730333880875

theorem tailTrace_2833794 : CollatzResearch.WordTrace tailWord_2833794 prefixEnd_2833794 485032799275730333880875 := by
  unfold tailWord_2833794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25839239573913946582303109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68904638863770524219474957 25839239573913946582303109)
  ·
    refine ⟨4844857420108864984181833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25839239573913946582303109 4844857420108864984181833)
    ·
      refine ⟨3633643065081648738136375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4844857420108864984181833 3633643065081648738136375)
      ·
        refine ⟨5450464597622473107204563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3633643065081648738136375 5450464597622473107204563)
        ·
          refine ⟨8175696896433709660806845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450464597622473107204563 8175696896433709660806845)
          ·
            refine ⟨3065886336162641122802567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8175696896433709660806845 3065886336162641122802567)
            ·
              refine ⟨4598829504243961684203851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065886336162641122802567 4598829504243961684203851)
              ·
                refine ⟨6898244256365942526305777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598829504243961684203851 6898244256365942526305777)
                ·
                  refine ⟨5173683192274456894729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898244256365942526305777 5173683192274456894729333)
                  ·
                    refine ⟨485032799275730333880875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173683192274456894729333 485032799275730333880875)
                    ·
                      rfl

theorem cell23_2833794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2833794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833794 prefixEnd_2833794 := by exact prefixLift 2833794
  have htrace : WordTrace (prefixWord ++ tailWord_2833794) baseStart_2833794 baseEnd_2833794 := by
    simpa [prefixWord, tailWord_2833794, baseEnd_2833794] using wordTrace_append hprefix tailTrace_2833794
  have hstable : (prefixWord ++ tailWord_2833794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833794).length < 2 ^ (prefixWord ++ tailWord_2833794).sum := by decide
  have hdescent : baseEnd_2833794 < baseStart_2833794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833800 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2833800 : Nat := 118140960795 + 2833800 * 2 ^ 59
def prefixEnd_2833800 : Nat := 4983230072969 + 3 ^ 40 * 2833800 * 2
def baseEnd_2833800 : Nat := 1455101478711117978167597

theorem tailTrace_2833800 : CollatzResearch.WordTrace tailWord_2833800 prefixEnd_2833800 1455101478711117978167597 := by
  unfold tailWord_2833800
  simp only [CollatzResearch.WordTrace]
  refine ⟨51678588566817024676965427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68904784755756032902620569 51678588566817024676965427)
  ·
    refine ⟨77517882850225537015448141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51678588566817024676965427 77517882850225537015448141)
    ·
      refine ⟨29069206068834576380793053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77517882850225537015448141 29069206068834576380793053)
      ·
        refine ⟨10900952275812966142797395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29069206068834576380793053 10900952275812966142797395)
        ·
          refine ⟨16351428413719449214196093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900952275812966142797395 16351428413719449214196093)
          ·
            refine ⟨6131785655144793455323535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351428413719449214196093 6131785655144793455323535)
            ·
              refine ⟨9197678482717190182985303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131785655144793455323535 9197678482717190182985303)
              ·
                refine ⟨13796517724075785274477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197678482717190182985303 13796517724075785274477955)
                ·
                  refine ⟨20694776586113677911716933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796517724075785274477955 20694776586113677911716933)
                  ·
                    refine ⟨3880270609896314608446925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20694776586113677911716933 3880270609896314608446925)
                    ·
                      refine ⟨1455101478711117978167597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880270609896314608446925 1455101478711117978167597)
                      ·
                        rfl

theorem cell23_2833800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2833800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833800 prefixEnd_2833800 := by exact prefixLift 2833800
  have htrace : WordTrace (prefixWord ++ tailWord_2833800) baseStart_2833800 baseEnd_2833800 := by
    simpa [prefixWord, tailWord_2833800, baseEnd_2833800] using wordTrace_append hprefix tailTrace_2833800
  have hstable : (prefixWord ++ tailWord_2833800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833800).length < 2 ^ (prefixWord ++ tailWord_2833800).sum := by decide
  have hdescent : baseEnd_2833800 < baseStart_2833800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833823 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2833823 : Nat := 118140960795 + 2833823 * 2 ^ 59
def prefixEnd_2833823 : Nat := 4983230072969 + 3 ^ 40 * 2833823 * 2
def baseEnd_2833823 : Nat := 1455113288766171388179991

theorem tailTrace_2833823 : CollatzResearch.WordTrace tailWord_2833823 prefixEnd_2833823 1455113288766171388179991 := by
  unfold tailWord_2833823
  simp only [CollatzResearch.WordTrace]
  refine ⟨103358016012550724282018123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68905344008367149521345415 103358016012550724282018123)
  ·
    refine ⟨155037024018826086423027185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103358016012550724282018123 155037024018826086423027185)
    ·
      refine ⟨116277768014119564817270389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155037024018826086423027185 116277768014119564817270389)
      ·
        refine ⟨10901040751323709201619099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116277768014119564817270389 10901040751323709201619099)
        ·
          refine ⟨16351561126985563802428649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901040751323709201619099 16351561126985563802428649)
          ·
            refine ⟨12263670845239172851821487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16351561126985563802428649 12263670845239172851821487)
            ·
              refine ⟨18395506267858759277732231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12263670845239172851821487 18395506267858759277732231)
              ·
                refine ⟨27593259401788138916598347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18395506267858759277732231 27593259401788138916598347)
                ·
                  refine ⟨41389889102682208374897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27593259401788138916598347 41389889102682208374897521)
                  ·
                    refine ⟨31042416827011656281173141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41389889102682208374897521 31042416827011656281173141)
                    ·
                      refine ⟨1455113288766171388179991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31042416827011656281173141 1455113288766171388179991)
                      ·
                        rfl

theorem cell23_2833823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2833823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833823 prefixEnd_2833823 := by exact prefixLift 2833823
  have htrace : WordTrace (prefixWord ++ tailWord_2833823) baseStart_2833823 baseEnd_2833823 := by
    simpa [prefixWord, tailWord_2833823, baseEnd_2833823] using wordTrace_append hprefix tailTrace_2833823
  have hstable : (prefixWord ++ tailWord_2833823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833823).length < 2 ^ (prefixWord ++ tailWord_2833823).sum := by decide
  have hdescent : baseEnd_2833823 < baseStart_2833823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833840 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2]
def baseStart_2833840 : Nat := 118140960795 + 2833840 * 2 ^ 59
def prefixEnd_2833840 : Nat := 4983230072969 + 3 ^ 40 * 2833840 * 2
def baseEnd_2833840 : Nat := 1455122017937297821667413

theorem tailTrace_2833840 : CollatzResearch.WordTrace tailWord_2833840 prefixEnd_2833840 1455122017937297821667413 := by
  unfold tailWord_2833840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679318026744568092693487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68905757368992757456924649 51679318026744568092693487)
  ·
    refine ⟨77518977040116852139040231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51679318026744568092693487 77518977040116852139040231)
    ·
      refine ⟨116278465560175278208560347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77518977040116852139040231 116278465560175278208560347)
      ·
        refine ⟨174417698340262917312840521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116278465560175278208560347 174417698340262917312840521)
        ·
          refine ⟨130813273755197187984630391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174417698340262917312840521 130813273755197187984630391)
          ·
            refine ⟨196219910632795781976945587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130813273755197187984630391 196219910632795781976945587)
            ·
              refine ⟨294329865949193672965418381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196219910632795781976945587 294329865949193672965418381)
              ·
                refine ⟨110373699730947627362031893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294329865949193672965418381 110373699730947627362031893)
                ·
                  refine ⟨5173767174888170032595245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110373699730947627362031893 5173767174888170032595245)
                  ·
                    refine ⟨1940162690583063762223217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5173767174888170032595245 1940162690583063762223217)
                    ·
                      refine ⟨1455122017937297821667413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940162690583063762223217 1455122017937297821667413)
                      ·
                        rfl

theorem cell23_2833840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2].length) (baseStart_2833840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833840 prefixEnd_2833840 := by exact prefixLift 2833840
  have htrace : WordTrace (prefixWord ++ tailWord_2833840) baseStart_2833840 baseEnd_2833840 := by
    simpa [prefixWord, tailWord_2833840, baseEnd_2833840] using wordTrace_append hprefix tailTrace_2833840
  have hstable : (prefixWord ++ tailWord_2833840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833840).length < 2 ^ (prefixWord ++ tailWord_2833840).sum := by decide
  have hdescent : baseEnd_2833840 < baseStart_2833840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833863 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 6]
def baseStart_2833863 : Nat := 118140960795 + 2833863 * 2 ^ 59
def prefixEnd_2833863 : Nat := 4983230072969 + 3 ^ 40 * 2833863 * 2
def baseEnd_2833863 : Nat := 485044609330783743893269

theorem tailTrace_2833863 : CollatzResearch.WordTrace tailWord_2833863 prefixEnd_2833863 485044609330783743893269 := by
  unfold tailWord_2833863
  simp only [CollatzResearch.WordTrace]
  refine ⟨103359474932405811113474243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68906316621603874075649495 103359474932405811113474243)
  ·
    refine ⟨155039212398608716670211365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103359474932405811113474243 155039212398608716670211365)
    ·
      refine ⟨29069852324739134375664631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155039212398608716670211365 29069852324739134375664631)
      ·
        refine ⟨43604778487108701563496947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29069852324739134375664631 43604778487108701563496947)
        ·
          refine ⟨65407167730663052345245421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43604778487108701563496947 65407167730663052345245421)
          ·
            refine ⟨24527687898998644629467033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65407167730663052345245421 24527687898998644629467033)
            ·
              refine ⟨18395765924248983472100275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24527687898998644629467033 18395765924248983472100275)
              ·
                refine ⟨27593648886373475208150413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18395765924248983472100275 27593648886373475208150413)
                ·
                  refine ⟨10347618332390053203056405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27593648886373475208150413 10347618332390053203056405)
                  ·
                    refine ⟨485044609330783743893269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10347618332390053203056405 485044609330783743893269)
                    ·
                      rfl

theorem cell23_2833863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_2833863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833863 prefixEnd_2833863 := by exact prefixLift 2833863
  have htrace : WordTrace (prefixWord ++ tailWord_2833863) baseStart_2833863 baseEnd_2833863 := by
    simpa [prefixWord, tailWord_2833863, baseEnd_2833863] using wordTrace_append hprefix tailTrace_2833863
  have hstable : (prefixWord ++ tailWord_2833863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833863).length < 2 ^ (prefixWord ++ tailWord_2833863).sum := by decide
  have hdescent : baseEnd_2833863 < baseStart_2833863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833880 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_2833880 : Nat := 118140960795 + 2833880 * 2 ^ 59
def prefixEnd_2833880 : Nat := 4983230072969 + 3 ^ 40 * 2833880 * 2
def baseEnd_2833880 : Nat := 485047519054492555055743

theorem tailTrace_2833880 : CollatzResearch.WordTrace tailWord_2833880 prefixEnd_2833880 485047519054492555055743 := by
  unfold tailWord_2833880
  simp only [CollatzResearch.WordTrace]
  refine ⟨51680047486672111508421547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68906729982229482011228729 51680047486672111508421547)
  ·
    refine ⟨77520071230008167262632321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51680047486672111508421547 77520071230008167262632321)
    ·
      refine ⟨58140053422506125446974241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77520071230008167262632321 58140053422506125446974241)
      ·
        refine ⟨43605040066879594085230681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58140053422506125446974241 43605040066879594085230681)
        ·
          refine ⟨32703780050159695563923011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43605040066879594085230681 32703780050159695563923011)
          ·
            refine ⟨49055670075239543345884517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32703780050159695563923011 49055670075239543345884517)
            ·
              refine ⟨9197938139107414377353347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49055670075239543345884517 9197938139107414377353347)
              ·
                refine ⟨13796907208661121566030021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197938139107414377353347 13796907208661121566030021)
                ·
                  refine ⟨2586920101623960293630629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13796907208661121566030021 2586920101623960293630629)
                  ·
                    refine ⟨485047519054492555055743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586920101623960293630629 485047519054492555055743)
                    ·
                      rfl

theorem cell23_2833880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_2833880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833880 prefixEnd_2833880 := by exact prefixLift 2833880
  have htrace : WordTrace (prefixWord ++ tailWord_2833880) baseStart_2833880 baseEnd_2833880 := by
    simpa [prefixWord, tailWord_2833880, baseEnd_2833880] using wordTrace_append hprefix tailTrace_2833880
  have hstable : (prefixWord ++ tailWord_2833880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833880).length < 2 ^ (prefixWord ++ tailWord_2833880).sum := by decide
  have hdescent : baseEnd_2833880 < baseStart_2833880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833881 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 1, 1, 3]
def baseStart_2833881 : Nat := 118140960795 + 2833881 * 2 ^ 59
def prefixEnd_2833881 : Nat := 4983230072969 + 3 ^ 40 * 2833881 * 2
def baseEnd_2833881 : Nat := 1455143070644132161254725

theorem tailTrace_2833881 : CollatzResearch.WordTrace tailWord_2833881 prefixEnd_2833881 1455143070644132161254725 := by
  unfold tailWord_2833881
  simp only [CollatzResearch.WordTrace]
  refine ⟨103360131446340600187629497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68906754297560400125086331 103360131446340600187629497)
  ·
    refine ⟨77520098584755450140722123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103360131446340600187629497 77520098584755450140722123)
    ·
      refine ⟨116280147877133175211083185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77520098584755450140722123 116280147877133175211083185)
      ·
        refine ⟨87210110907849881408312389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116280147877133175211083185 87210110907849881408312389)
        ·
          refine ⟨16351895795221852764058573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87210110907849881408312389 16351895795221852764058573)
          ·
            refine ⟨6131960923208194786521965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351895795221852764058573 6131960923208194786521965)
            ·
              refine ⟨2299485346203073044945737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6131960923208194786521965 2299485346203073044945737)
              ·
                refine ⟨1724614009652304783709303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299485346203073044945737 1724614009652304783709303)
                ·
                  refine ⟨2586921014478457175563955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724614009652304783709303 2586921014478457175563955)
                  ·
                    refine ⟨3880381521717685763345933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586921014478457175563955 3880381521717685763345933)
                    ·
                      refine ⟨1455143070644132161254725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880381521717685763345933 1455143070644132161254725)
                      ·
                        rfl

theorem cell23_2833881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_2833881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833881 prefixEnd_2833881 := by exact prefixLift 2833881
  have htrace : WordTrace (prefixWord ++ tailWord_2833881) baseStart_2833881 baseEnd_2833881 := by
    simpa [prefixWord, tailWord_2833881, baseEnd_2833881] using wordTrace_append hprefix tailTrace_2833881
  have hstable : (prefixWord ++ tailWord_2833881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833881).length < 2 ^ (prefixWord ++ tailWord_2833881).sum := by decide
  have hdescent : baseEnd_2833881 < baseStart_2833881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833901 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2833901 : Nat := 118140960795 + 2833901 * 2 ^ 59
def prefixEnd_2833901 : Nat := 4983230072969 + 3 ^ 40 * 2833901 * 2
def baseEnd_2833901 : Nat := 485051113419074027668211

theorem tailTrace_2833901 : CollatzResearch.WordTrace tailWord_2833901 prefixEnd_2833901 485051113419074027668211 := by
  unfold tailWord_2833901
  simp only [CollatzResearch.WordTrace]
  refine ⟨103360860906268143603357557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68907240604178762402238371 103360860906268143603357557)
  ·
    refine ⟨9690080709962638462814771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103360860906268143603357557 9690080709962638462814771)
    ·
      refine ⟨14535121064943957694222157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690080709962638462814771 14535121064943957694222157)
      ·
        refine ⟨5450670399353984135333309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14535121064943957694222157 5450670399353984135333309)
        ·
          refine ⟨2044001399757744050749991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5450670399353984135333309 2044001399757744050749991)
          ·
            refine ⟨3066002099636616076124987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044001399757744050749991 3066002099636616076124987)
            ·
              refine ⟨4599003149454924114187481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066002099636616076124987 4599003149454924114187481)
              ·
                refine ⟨3449252362091193085640611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599003149454924114187481 3449252362091193085640611)
                ·
                  refine ⟨5173878543136789628460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449252362091193085640611 5173878543136789628460917)
                  ·
                    refine ⟨485051113419074027668211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173878543136789628460917 485051113419074027668211)
                    ·
                      rfl

theorem cell23_2833901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2833901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833901 prefixEnd_2833901 := by exact prefixLift 2833901
  have htrace : WordTrace (prefixWord ++ tailWord_2833901) baseStart_2833901 baseEnd_2833901 := by
    simpa [prefixWord, tailWord_2833901, baseEnd_2833901] using wordTrace_append hprefix tailTrace_2833901
  have hstable : (prefixWord ++ tailWord_2833901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833901).length < 2 ^ (prefixWord ++ tailWord_2833901).sum := by decide
  have hdescent : baseEnd_2833901 < baseStart_2833901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833910 : List Nat := [5, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2833910 : Nat := 118140960795 + 2833910 * 2 ^ 59
def prefixEnd_2833910 : Nat := 4983230072969 + 3 ^ 40 * 2833910 * 2
def baseEnd_2833910 : Nat := 53894739317893057325633

theorem tailTrace_2833910 : CollatzResearch.WordTrace tailWord_2833910 prefixEnd_2833910 53894739317893057325633 := by
  unfold tailWord_2833910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460074322702221133777199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68907459442157025426956789 6460074322702221133777199)
  ·
    refine ⟨9690111484053331700665799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6460074322702221133777199 9690111484053331700665799)
    ·
      refine ⟨14535167226079997550998699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690111484053331700665799 14535167226079997550998699)
      ·
        refine ⟨21802750839119996326498049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14535167226079997550998699 21802750839119996326498049)
        ·
          refine ⟨16352063129339997244873537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21802750839119996326498049 16352063129339997244873537)
          ·
            refine ⟨12264047347004997933655153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16352063129339997244873537 12264047347004997933655153)
            ·
              refine ⟨9198035510253748450241365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12264047347004997933655153 9198035510253748450241365)
              ·
                refine ⟨53894739317893057325633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9198035510253748450241365 53894739317893057325633)
                ·
                  rfl

theorem cell23_2833910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2833910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833910 prefixEnd_2833910 := by exact prefixLift 2833910
  have htrace : WordTrace (prefixWord ++ tailWord_2833910) baseStart_2833910 baseEnd_2833910 := by
    simpa [prefixWord, tailWord_2833910, baseEnd_2833910] using wordTrace_append hprefix tailTrace_2833910
  have hstable : (prefixWord ++ tailWord_2833910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833910).length < 2 ^ (prefixWord ++ tailWord_2833910).sum := by decide
  have hdescent : baseEnd_2833910 < baseStart_2833910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833924 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2833924 : Nat := 118140960795 + 2833924 * 2 ^ 59
def prefixEnd_2833924 : Nat := 4983230072969 + 3 ^ 40 * 2833924 * 2
def baseEnd_2833924 : Nat := 1455165150312275493017027

theorem tailTrace_2833924 : CollatzResearch.WordTrace tailWord_2833924 prefixEnd_2833924 1455165150312275493017027 := by
  unfold tailWord_2833924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51680849892592409265722413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68907799856789879020963217 51680849892592409265722413)
  ·
    refine ⟨19380318709722153474645905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51680849892592409265722413 19380318709722153474645905)
    ·
      refine ⟨14535239032291615105984429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19380318709722153474645905 14535239032291615105984429)
      ·
        refine ⟨5450714637109355664744161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14535239032291615105984429 5450714637109355664744161)
        ·
          refine ⟨4088035977832016748558121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5450714637109355664744161 4088035977832016748558121)
          ·
            refine ⟨3066026983374012561418591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088035977832016748558121 3066026983374012561418591)
            ·
              refine ⟨4599040475061018842127887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066026983374012561418591 4599040475061018842127887)
              ·
                refine ⟨6898560712591528263191831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599040475061018842127887 6898560712591528263191831)
                ·
                  refine ⟨10347841068887292394787747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6898560712591528263191831 10347841068887292394787747)
                  ·
                    refine ⟨15521761603330938592181621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10347841068887292394787747 15521761603330938592181621)
                    ·
                      refine ⟨1455165150312275493017027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15521761603330938592181621 1455165150312275493017027)
                      ·
                        rfl

theorem cell23_2833924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2833924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833924 prefixEnd_2833924 := by exact prefixLift 2833924
  have htrace : WordTrace (prefixWord ++ tailWord_2833924) baseStart_2833924 baseEnd_2833924 := by
    simpa [prefixWord, tailWord_2833924, baseEnd_2833924] using wordTrace_append hprefix tailTrace_2833924
  have hstable : (prefixWord ++ tailWord_2833924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833924).length < 2 ^ (prefixWord ++ tailWord_2833924).sum := by decide
  have hdescent : baseEnd_2833924 < baseStart_2833924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833954 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2833954 : Nat := 118140960795 + 2833954 * 2 ^ 59
def prefixEnd_2833954 : Nat := 4983230072969 + 3 ^ 40 * 2833954 * 2
def baseEnd_2833954 : Nat := 1455180554731910375641889

theorem tailTrace_2833954 : CollatzResearch.WordTrace tailWord_2833954 prefixEnd_2833954 1455180554731910375641889 := by
  unfold tailWord_2833954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25840698493769033413759229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68908529316717422436691277 25840698493769033413759229)
  ·
    refine ⟨9690261935163387530159711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25840698493769033413759229 9690261935163387530159711)
    ·
      refine ⟨14535392902745081295239567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690261935163387530159711 14535392902745081295239567)
      ·
        refine ⟨21803089354117621942859351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14535392902745081295239567 21803089354117621942859351)
        ·
          refine ⟨32704634031176432914289027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21803089354117621942859351 32704634031176432914289027)
          ·
            refine ⟨49056951046764649371433541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32704634031176432914289027 49056951046764649371433541)
            ·
              refine ⟨9198178321268371757143789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49056951046764649371433541 9198178321268371757143789)
              ·
                refine ⟨3449316870475639408928921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198178321268371757143789 3449316870475639408928921)
                ·
                  refine ⟨2586987652856729556696691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449316870475639408928921 2586987652856729556696691)
                  ·
                    refine ⟨3880481479285094335045037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586987652856729556696691 3880481479285094335045037)
                    ·
                      refine ⟨1455180554731910375641889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880481479285094335045037 1455180554731910375641889)
                      ·
                        rfl

theorem cell23_2833954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2833954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833954 prefixEnd_2833954 := by exact prefixLift 2833954
  have htrace : WordTrace (prefixWord ++ tailWord_2833954) baseStart_2833954 baseEnd_2833954 := by
    simpa [prefixWord, tailWord_2833954, baseEnd_2833954] using wordTrace_append hprefix tailTrace_2833954
  have hstable : (prefixWord ++ tailWord_2833954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833954).length < 2 ^ (prefixWord ++ tailWord_2833954).sum := by decide
  have hdescent : baseEnd_2833954 < baseStart_2833954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833981 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2833981 : Nat := 118140960795 + 2833981 * 2 ^ 59
def prefixEnd_2833981 : Nat := 4983230072969 + 3 ^ 40 * 2833981 * 2
def baseEnd_2833981 : Nat := 1455194418709581770004265

theorem tailTrace_2833981 : CollatzResearch.WordTrace tailWord_2833981 prefixEnd_2833981 1455194418709581770004265 := by
  unfold tailWord_2833981
  simp only [CollatzResearch.WordTrace]
  refine ⟨103363778745978317266269797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68909185830652211510846531 103363778745978317266269797)
  ·
    refine ⟨19380708514870934487425587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103363778745978317266269797 19380708514870934487425587)
    ·
      refine ⟨29071062772306401731138381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19380708514870934487425587 29071062772306401731138381)
      ·
        refine ⟨10901648539614900649176893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29071062772306401731138381 10901648539614900649176893)
        ·
          refine ⟨4088118202355587743441335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10901648539614900649176893 4088118202355587743441335)
          ·
            refine ⟨6132177303533381615162003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088118202355587743441335 6132177303533381615162003)
            ·
              refine ⟨9198265955300072422743005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132177303533381615162003 9198265955300072422743005)
              ·
                refine ⟨3449349733237527158528627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198265955300072422743005 3449349733237527158528627)
                ·
                  refine ⟨5174024599856290737792941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449349733237527158528627 5174024599856290737792941)
                  ·
                    refine ⟨1940259224946109026672353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5174024599856290737792941 1940259224946109026672353)
                    ·
                      refine ⟨1455194418709581770004265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940259224946109026672353 1455194418709581770004265)
                      ·
                        rfl

theorem cell23_2833981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2833981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833981 prefixEnd_2833981 := by exact prefixLift 2833981
  have htrace : WordTrace (prefixWord ++ tailWord_2833981) baseStart_2833981 baseEnd_2833981 := by
    simpa [prefixWord, tailWord_2833981, baseEnd_2833981] using wordTrace_append hprefix tailTrace_2833981
  have hstable : (prefixWord ++ tailWord_2833981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833981).length < 2 ^ (prefixWord ++ tailWord_2833981).sum := by decide
  have hdescent : baseEnd_2833981 < baseStart_2833981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833994 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_2833994 : Nat := 118140960795 + 2833994 * 2 ^ 59
def prefixEnd_2833994 : Nat := 4983230072969 + 3 ^ 40 * 2833994 * 2
def baseEnd_2833994 : Nat := 1455201093958090219141705

theorem tailTrace_2833994 : CollatzResearch.WordTrace tailWord_2833994 prefixEnd_2833994 1455201093958090219141705 := by
  unfold tailWord_2833994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841063223732805121623259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68909501929954146990995357 25841063223732805121623259)
  ·
    refine ⟨38761594835599207682434889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25841063223732805121623259 38761594835599207682434889)
    ·
      refine ⟨29071196126699405761826167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38761594835599207682434889 29071196126699405761826167)
      ·
        refine ⟨43606794190049108642739251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29071196126699405761826167 43606794190049108642739251)
        ·
          refine ⟨65410191285073662964108877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43606794190049108642739251 65410191285073662964108877)
          ·
            refine ⟨24528821731902623611540829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65410191285073662964108877 24528821731902623611540829)
            ·
              refine ⟨9198308149463483854327811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24528821731902623611540829 9198308149463483854327811)
              ·
                refine ⟨13797462224195225781491717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198308149463483854327811 13797462224195225781491717)
                ·
                  refine ⟨2587024167036604834029697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13797462224195225781491717 2587024167036604834029697)
                  ·
                    refine ⟨1940268125277453625522273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2587024167036604834029697 1940268125277453625522273)
                    ·
                      refine ⟨1455201093958090219141705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940268125277453625522273 1455201093958090219141705)
                      ·
                        rfl

theorem cell23_2833994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_2833994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833994 prefixEnd_2833994 := by exact prefixLift 2833994
  have htrace : WordTrace (prefixWord ++ tailWord_2833994) baseStart_2833994 baseEnd_2833994 := by
    simpa [prefixWord, tailWord_2833994, baseEnd_2833994] using wordTrace_append hprefix tailTrace_2833994
  have hstable : (prefixWord ++ tailWord_2833994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833994).length < 2 ^ (prefixWord ++ tailWord_2833994).sum := by decide
  have hdescent : baseEnd_2833994 < baseStart_2833994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834000 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 7]
def baseStart_2834000 : Nat := 118140960795 + 2834000 * 2 ^ 59
def prefixEnd_2834000 : Nat := 4983230072969 + 3 ^ 40 * 2834000 * 2
def baseEnd_2834000 : Nat := 161689352760224132851853

theorem tailTrace_2834000 : CollatzResearch.WordTrace tailWord_2834000 prefixEnd_2834000 161689352760224132851853 := by
  unfold tailWord_2834000
  simp only [CollatzResearch.WordTrace]
  refine ⟨51682235866454741755605727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68909647821939655674140969 51682235866454741755605727)
  ·
    refine ⟨77523353799682112633408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51682235866454741755605727 77523353799682112633408591)
    ·
      refine ⟨116285030699523168950112887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77523353799682112633408591 116285030699523168950112887)
      ·
        refine ⟨174427546049284753425169331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116285030699523168950112887 174427546049284753425169331)
        ·
          refine ⟨261641319073927130137753997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174427546049284753425169331 261641319073927130137753997)
          ·
            refine ⟨98115494652722673801657749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261641319073927130137753997 98115494652722673801657749)
            ·
              refine ⟨4599163811846375334452707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98115494652722673801657749 4599163811846375334452707)
              ·
                refine ⟨6898745717769563001679061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599163811846375334452707 6898745717769563001679061)
                ·
                  refine ⟨161689352760224132851853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6898745717769563001679061 161689352760224132851853)
                  ·
                    rfl

theorem cell23_2834000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_2834000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834000 prefixEnd_2834000 := by exact prefixLift 2834000
  have htrace : WordTrace (prefixWord ++ tailWord_2834000) baseStart_2834000 baseEnd_2834000 := by
    simpa [prefixWord, tailWord_2834000, baseEnd_2834000] using wordTrace_append hprefix tailTrace_2834000
  have hstable : (prefixWord ++ tailWord_2834000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834000).length < 2 ^ (prefixWord ++ tailWord_2834000).sum := by decide
  have hdescent : baseEnd_2834000 < baseStart_2834000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834034 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_2834034 : Nat := 118140960795 + 2834034 * 2 ^ 59
def prefixEnd_2834034 : Nat := 4983230072969 + 3 ^ 40 * 2834034 * 2
def baseEnd_2834034 : Nat := 161691292576030006960169

theorem tailTrace_2834034 : CollatzResearch.WordTrace tailWord_2834034 prefixEnd_2834034 161691292576030006960169 := by
  unfold tailWord_2834034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841427953696576829487289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68910474543190871545299437 25841427953696576829487289)
  ·
    refine ⟨19381070965272432622115467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25841427953696576829487289 19381070965272432622115467)
    ·
      refine ⟨29071606447908648933173201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19381070965272432622115467 29071606447908648933173201)
      ·
        refine ⟨21803704835931486699879901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29071606447908648933173201 21803704835931486699879901)
        ·
          refine ⟨8176389313474307512454963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21803704835931486699879901 8176389313474307512454963)
          ·
            refine ⟨12264583970211461268682445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176389313474307512454963 12264583970211461268682445)
            ·
              refine ⟨4599218988829297975755917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12264583970211461268682445 4599218988829297975755917)
              ·
                refine ⟨1724707120810986740908469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4599218988829297975755917 1724707120810986740908469)
                ·
                  refine ⟨161691292576030006960169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724707120810986740908469 161691292576030006960169)
                  ·
                    rfl

theorem cell23_2834034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_2834034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834034 prefixEnd_2834034 := by exact prefixLift 2834034
  have htrace : WordTrace (prefixWord ++ tailWord_2834034) baseStart_2834034 baseEnd_2834034 := by
    simpa [prefixWord, tailWord_2834034, baseEnd_2834034] using wordTrace_append hprefix tailTrace_2834034
  have hstable : (prefixWord ++ tailWord_2834034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834034).length < 2 ^ (prefixWord ++ tailWord_2834034).sum := by decide
  have hdescent : baseEnd_2834034 < baseStart_2834034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834077 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2834077 : Nat := 118140960795 + 2834077 * 2 ^ 59
def prefixEnd_2834077 : Nat := 4983230072969 + 3 ^ 40 * 2834077 * 2
def baseEnd_2834077 : Nat := 485081237617471131467941

theorem tailTrace_2834077 : CollatzResearch.WordTrace tailWord_2834077 prefixEnd_2834077 485081237617471131467941 := by
  unfold tailWord_2834077
  simp only [CollatzResearch.WordTrace]
  refine ⟨103367280153630525661764485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68911520102420350441176323 103367280153630525661764485)
  ·
    refine ⟨19381365028805723561580841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103367280153630525661764485 19381365028805723561580841)
    ·
      refine ⟨14536023771604292671185631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19381365028805723561580841 14536023771604292671185631)
      ·
        refine ⟨21804035657406439006778447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536023771604292671185631 21804035657406439006778447)
        ·
          refine ⟨32706053486109658510167671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21804035657406439006778447 32706053486109658510167671)
          ·
            refine ⟨49059080229164487765251507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32706053486109658510167671 49059080229164487765251507)
            ·
              refine ⟨73588620343746731647877261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49059080229164487765251507 73588620343746731647877261)
              ·
                refine ⟨27595732628905024367953973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73588620343746731647877261 27595732628905024367953973)
                ·
                  refine ⟨2587099933959846034495685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27595732628905024367953973 2587099933959846034495685)
                  ·
                    refine ⟨485081237617471131467941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587099933959846034495685 485081237617471131467941)
                    ·
                      rfl

theorem cell23_2834077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2834077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834077 prefixEnd_2834077 := by exact prefixLift 2834077
  have htrace : WordTrace (prefixWord ++ tailWord_2834077) baseStart_2834077 baseEnd_2834077 := by
    simpa [prefixWord, tailWord_2834077, baseEnd_2834077] using wordTrace_append hprefix tailTrace_2834077
  have hstable : (prefixWord ++ tailWord_2834077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834077).length < 2 ^ (prefixWord ++ tailWord_2834077).sum := by decide
  have hdescent : baseEnd_2834077 < baseStart_2834077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834084 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_2834084 : Nat := 118140960795 + 2834084 * 2 ^ 59
def prefixEnd_2834084 : Nat := 4983230072969 + 3 ^ 40 * 2834084 * 2
def baseEnd_2834084 : Nat := 1455247307216994867016291

theorem tailTrace_2834084 : CollatzResearch.WordTrace tailWord_2834084 prefixEnd_2834084 1455247307216994867016291 := by
  unfold tailWord_2834084
  simp only [CollatzResearch.WordTrace]
  refine ⟨51683767732302582928634653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68911690309736777238179537 51683767732302582928634653)
  ·
    refine ⟨19381412899613468598237995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51683767732302582928634653 19381412899613468598237995)
    ·
      refine ⟨29072119349420202897356993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19381412899613468598237995 29072119349420202897356993)
      ·
        refine ⟨21804089512065152173017745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29072119349420202897356993 21804089512065152173017745)
        ·
          refine ⟨16353067134048864129763309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21804089512065152173017745 16353067134048864129763309)
          ·
            refine ⟨6132400175268324048661241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16353067134048864129763309 6132400175268324048661241)
            ·
              refine ⟨4599300131451243036495931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132400175268324048661241 4599300131451243036495931)
              ·
                refine ⟨6898950197176864554743897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599300131451243036495931 6898950197176864554743897)
                ·
                  refine ⟨5174212647882648416057923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898950197176864554743897 5174212647882648416057923)
                  ·
                    refine ⟨7761318971823972624086885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174212647882648416057923 7761318971823972624086885)
                    ·
                      refine ⟨1455247307216994867016291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7761318971823972624086885 1455247307216994867016291)
                      ·
                        rfl

theorem cell23_2834084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_2834084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834084 prefixEnd_2834084 := by exact prefixLift 2834084
  have htrace : WordTrace (prefixWord ++ tailWord_2834084) baseStart_2834084 baseEnd_2834084 := by
    simpa [prefixWord, tailWord_2834084, baseEnd_2834084] using wordTrace_append hprefix tailTrace_2834084
  have hstable : (prefixWord ++ tailWord_2834084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834084).length < 2 ^ (prefixWord ++ tailWord_2834084).sum := by decide
  have hdescent : baseEnd_2834084 < baseStart_2834084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834118 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2834118 : Nat := 118140960795 + 2834118 * 2 ^ 59
def prefixEnd_2834118 : Nat := 4983230072969 + 3 ^ 40 * 2834118 * 2
def baseEnd_2834118 : Nat := 1455264765559247733991135

theorem tailTrace_2834118 : CollatzResearch.WordTrace tailWord_2834118 prefixEnd_2834118 1455264765559247733991135 := by
  unfold tailWord_2834118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230274235827562177000219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68912517030987993109338005 3230274235827562177000219)
  ·
    refine ⟨4845411353741343265500329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3230274235827562177000219 4845411353741343265500329)
    ·
      refine ⟨3634058515306007449125247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845411353741343265500329 3634058515306007449125247)
      ·
        refine ⟨5451087772959011173687871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634058515306007449125247 5451087772959011173687871)
        ·
          refine ⟨8176631659438516760531807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451087772959011173687871 8176631659438516760531807)
          ·
            refine ⟨12264947489157775140797711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176631659438516760531807 12264947489157775140797711)
            ·
              refine ⟨18397421233736662711196567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12264947489157775140797711 18397421233736662711196567)
              ·
                refine ⟨27596131850604994066794851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18397421233736662711196567 27596131850604994066794851)
                ·
                  refine ⟨41394197775907491100192277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27596131850604994066794851 41394197775907491100192277)
                  ·
                    refine ⟨1940353020745663645321513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41394197775907491100192277 1940353020745663645321513)
                    ·
                      refine ⟨1455264765559247733991135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940353020745663645321513 1455264765559247733991135)
                      ·
                        rfl

theorem cell23_2834118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2834118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834118 prefixEnd_2834118 := by exact prefixLift 2834118
  have htrace : WordTrace (prefixWord ++ tailWord_2834118) baseStart_2834118 baseEnd_2834118 := by
    simpa [prefixWord, tailWord_2834118, baseEnd_2834118] using wordTrace_append hprefix tailTrace_2834118
  have hstable : (prefixWord ++ tailWord_2834118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834118).length < 2 ^ (prefixWord ++ tailWord_2834118).sum := by decide
  have hdescent : baseEnd_2834118 < baseStart_2834118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834137 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_2834137 : Nat := 118140960795 + 2834137 * 2 ^ 59
def prefixEnd_2834137 : Nat := 4983230072969 + 3 ^ 40 * 2834137 * 2
def baseEnd_2834137 : Nat := 485091507230561053217849

theorem tailTrace_2834137 : CollatzResearch.WordTrace tailWord_2834137 prefixEnd_2834137 485091507230561053217849 := by
  unfold tailWord_2834137
  simp only [CollatzResearch.WordTrace]
  refine ⟨103369468533413155908948665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68912979022275437272632443 103369468533413155908948665)
  ·
    refine ⟨77527101400059866931711499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103369468533413155908948665 77527101400059866931711499)
    ·
      refine ⟨116290652100089800397567249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77527101400059866931711499 116290652100089800397567249)
      ·
        refine ⟨87217989075067350298175437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116290652100089800397567249 87217989075067350298175437)
        ·
          refine ⟨32706745903150256361815789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87217989075067350298175437 32706745903150256361815789)
          ·
            refine ⟨12265029713681346135680921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32706745903150256361815789 12265029713681346135680921)
            ·
              refine ⟨9198772285261009601760691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12265029713681346135680921 9198772285261009601760691)
              ·
                refine ⟨13798158427891514402641037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198772285261009601760691 13798158427891514402641037)
                ·
                  refine ⟨5174309410459317900990389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13798158427891514402641037 5174309410459317900990389)
                  ·
                    refine ⟨485091507230561053217849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5174309410459317900990389 485091507230561053217849)
                    ·
                      rfl

theorem cell23_2834137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_2834137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834137 prefixEnd_2834137 := by exact prefixLift 2834137
  have htrace : WordTrace (prefixWord ++ tailWord_2834137) baseStart_2834137 baseEnd_2834137 := by
    simpa [prefixWord, tailWord_2834137, baseEnd_2834137] using wordTrace_append hprefix tailTrace_2834137
  have hstable : (prefixWord ++ tailWord_2834137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834137).length < 2 ^ (prefixWord ++ tailWord_2834137).sum := by decide
  have hdescent : baseEnd_2834137 < baseStart_2834137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834177 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2834177 : Nat := 118140960795 + 2834177 * 2 ^ 59
def prefixEnd_2834177 : Nat := 4983230072969 + 3 ^ 40 * 2834177 * 2
def baseEnd_2834177 : Nat := 1455295060917863003153363

theorem tailTrace_2834177 : CollatzResearch.WordTrace tailWord_2834177 prefixEnd_2834177 1455295060917863003153363 := by
  unfold tailWord_2834177
  simp only [CollatzResearch.WordTrace]
  refine ⟨103370927453268242740404785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68913951635512161826936523 103370927453268242740404785)
  ·
    refine ⟨77528195589951182055303589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103370927453268242740404785 77528195589951182055303589)
    ·
      refine ⟨14536536673115846635369423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77528195589951182055303589 14536536673115846635369423)
      ·
        refine ⟨21804805009673769953054135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536536673115846635369423 21804805009673769953054135)
        ·
          refine ⟨32707207514510654929581203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21804805009673769953054135 32707207514510654929581203)
          ·
            refine ⟨49060811271765982394371805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32707207514510654929581203 49060811271765982394371805)
            ·
              refine ⟨18397804226912243397889427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49060811271765982394371805 18397804226912243397889427)
              ·
                refine ⟨27596706340368365096834141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18397804226912243397889427 27596706340368365096834141)
                ·
                  refine ⟨10348764877638136911312803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27596706340368365096834141 10348764877638136911312803)
                  ·
                    refine ⟨15523147316457205366969205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10348764877638136911312803 15523147316457205366969205)
                    ·
                      refine ⟨1455295060917863003153363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15523147316457205366969205 1455295060917863003153363)
                      ·
                        rfl

theorem cell23_2834177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2834177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834177 prefixEnd_2834177 := by exact prefixLift 2834177
  have htrace : WordTrace (prefixWord ++ tailWord_2834177) baseStart_2834177 baseEnd_2834177 := by
    simpa [prefixWord, tailWord_2834177, baseEnd_2834177] using wordTrace_append hprefix tailTrace_2834177
  have hstable : (prefixWord ++ tailWord_2834177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834177).length < 2 ^ (prefixWord ++ tailWord_2834177).sum := by decide
  have hdescent : baseEnd_2834177 < baseStart_2834177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834197 : List Nat := [1, 3, 2, 1, 2, 4, 1, 9]
def baseStart_2834197 : Nat := 118140960795 + 2834197 * 2 ^ 59
def prefixEnd_2834197 : Nat := 4983230072969 + 3 ^ 40 * 2834197 * 2
def baseEnd_2834197 : Nat := 53900197427072330551973

theorem tailTrace_2834197 : CollatzResearch.WordTrace tailWord_2834197 prefixEnd_2834197 53900197427072330551973 := by
  unfold tailWord_2834197
  simp only [CollatzResearch.WordTrace]
  refine ⟨103371656913195786156132845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68914437942130524104088563 103371656913195786156132845)
  ·
    refine ⟨38764371342448419808549817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103371656913195786156132845 38764371342448419808549817)
    ·
      refine ⟨29073278506836314856412363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38764371342448419808549817 29073278506836314856412363)
      ·
        refine ⟨43609917760254472284618545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29073278506836314856412363 43609917760254472284618545)
        ·
          refine ⟨32707438320190854213463909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43609917760254472284618545 32707438320190854213463909)
          ·
            refine ⟨6132644685035785165024483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32707438320190854213463909 6132644685035785165024483)
            ·
              refine ⟨9198967027553677747536725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132644685035785165024483 9198967027553677747536725)
              ·
                refine ⟨53900197427072330551973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9198967027553677747536725 53900197427072330551973)
                ·
                  rfl

theorem cell23_2834197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 9].length) (baseStart_2834197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834197 prefixEnd_2834197 := by exact prefixLift 2834197
  have htrace : WordTrace (prefixWord ++ tailWord_2834197) baseStart_2834197 baseEnd_2834197 := by
    simpa [prefixWord, tailWord_2834197, baseEnd_2834197] using wordTrace_append hprefix tailTrace_2834197
  have hstable : (prefixWord ++ tailWord_2834197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834197).length < 2 ^ (prefixWord ++ tailWord_2834197).sum := by decide
  have hdescent : baseEnd_2834197 < baseStart_2834197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834277 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2834277 : Nat := 118140960795 + 2834277 * 2 ^ 59
def prefixEnd_2834277 : Nat := 4983230072969 + 3 ^ 40 * 2834277 * 2
def baseEnd_2834277 : Nat := 1455346408983312611902903

theorem tailTrace_2834277 : CollatzResearch.WordTrace tailWord_2834277 prefixEnd_2834277 1455346408983312611902903 := by
  unfold tailWord_2834277
  simp only [CollatzResearch.WordTrace]
  refine ⟨103374574752905959819045085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68916383168603973212696723 103374574752905959819045085)
  ·
    refine ⟨38765465532339734932141907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103374574752905959819045085 38765465532339734932141907)
    ·
      refine ⟨58148198298509602398212861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38765465532339734932141907 58148198298509602398212861)
      ·
        refine ⟨21805574361941100899329823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58148198298509602398212861 21805574361941100899329823)
        ·
          refine ⟨32708361542911651348994735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21805574361941100899329823 32708361542911651348994735)
          ·
            refine ⟨49062542314367477023492103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32708361542911651348994735 49062542314367477023492103)
            ·
              refine ⟨73593813471551215535238155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49062542314367477023492103 73593813471551215535238155)
              ·
                refine ⟨110390720207326823302857233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73593813471551215535238155 110390720207326823302857233)
                ·
                  refine ⟨82793040155495117477142925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110390720207326823302857233 82793040155495117477142925)
                  ·
                    refine ⟨31047390058310669053928597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82793040155495117477142925 31047390058310669053928597)
                    ·
                      refine ⟨1455346408983312611902903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31047390058310669053928597 1455346408983312611902903)
                      ·
                        rfl

theorem cell23_2834277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2834277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834277 prefixEnd_2834277 := by exact prefixLift 2834277
  have htrace : WordTrace (prefixWord ++ tailWord_2834277) baseStart_2834277 baseEnd_2834277 := by
    simpa [prefixWord, tailWord_2834277, baseEnd_2834277] using wordTrace_append hprefix tailTrace_2834277
  have hstable : (prefixWord ++ tailWord_2834277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834277).length < 2 ^ (prefixWord ++ tailWord_2834277).sum := by decide
  have hdescent : baseEnd_2834277 < baseStart_2834277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 4, 2, 2]
def baseStart_2834281 : Nat := 118140960795 + 2834281 * 2 ^ 59
def prefixEnd_2834281 : Nat := 4983230072969 + 3 ^ 40 * 2834281 * 2
def baseEnd_2834281 : Nat := 1455348462905930596252885

theorem tailTrace_2834281 : CollatzResearch.WordTrace tailWord_2834281 prefixEnd_2834281 1455348462905930596252885 := by
  unfold tailWord_2834281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103374720644891468502190697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68916480429927645668127131 103374720644891468502190697)
  ·
    refine ⟨77531040483668601376643023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103374720644891468502190697 77531040483668601376643023)
    ·
      refine ⟨116296560725502902064964535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77531040483668601376643023 116296560725502902064964535)
      ·
        refine ⟨174444841088254353097446803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116296560725502902064964535 174444841088254353097446803)
        ·
          refine ⟨261667261632381529646170205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174444841088254353097446803 261667261632381529646170205)
          ·
            refine ⟨98125223112143073617313827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261667261632381529646170205 98125223112143073617313827)
            ·
              refine ⟨147187834668214610425970741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98125223112143073617313827 147187834668214610425970741)
              ·
                refine ⟨13798859500145119727434757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147187834668214610425970741 13798859500145119727434757)
                ·
                  refine ⟨2587286156277209948894017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13798859500145119727434757 2587286156277209948894017)
                  ·
                    refine ⟨1940464617207907461670513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2587286156277209948894017 1940464617207907461670513)
                    ·
                      refine ⟨1455348462905930596252885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940464617207907461670513 1455348462905930596252885)
                      ·
                        rfl

theorem cell23_2834281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2, 2].length) (baseStart_2834281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834281 prefixEnd_2834281 := by exact prefixLift 2834281
  have htrace : WordTrace (prefixWord ++ tailWord_2834281) baseStart_2834281 baseEnd_2834281 := by
    simpa [prefixWord, tailWord_2834281, baseEnd_2834281] using wordTrace_append hprefix tailTrace_2834281
  have hstable : (prefixWord ++ tailWord_2834281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834281).length < 2 ^ (prefixWord ++ tailWord_2834281).sum := by decide
  have hdescent : baseEnd_2834281 < baseStart_2834281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834284 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_2834284 : Nat := 118140960795 + 2834284 * 2 ^ 59
def prefixEnd_2834284 : Nat := 4983230072969 + 3 ^ 40 * 2834284 * 2
def baseEnd_2834284 : Nat := 1455350003347894084515371

theorem tailTrace_2834284 : CollatzResearch.WordTrace tailWord_2834284 prefixEnd_2834284 1455350003347894084515371 := by
  unfold tailWord_2834284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51687415031940300007274953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68916553375920400009699937 51687415031940300007274953)
  ·
    refine ⟨38765561273955225005456215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51687415031940300007274953 38765561273955225005456215)
    ·
      refine ⟨58148341910932837508184323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38765561273955225005456215 58148341910932837508184323)
      ·
        refine ⟨87222512866399256262276485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58148341910932837508184323 87222512866399256262276485)
        ·
          refine ⟨16354221162449860549176841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87222512866399256262276485 16354221162449860549176841)
          ·
            refine ⟨12265665871837395411882631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16354221162449860549176841 12265665871837395411882631)
            ·
              refine ⟨18398498807756093117823947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12265665871837395411882631 18398498807756093117823947)
              ·
                refine ⟨27597748211634139676735921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18398498807756093117823947 27597748211634139676735921)
                ·
                  refine ⟨20698311158725604757551941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27597748211634139676735921 20698311158725604757551941)
                  ·
                    refine ⟨3880933342261050892040989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20698311158725604757551941 3880933342261050892040989)
                    ·
                      refine ⟨1455350003347894084515371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880933342261050892040989 1455350003347894084515371)
                      ·
                        rfl

theorem cell23_2834284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_2834284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834284 prefixEnd_2834284 := by exact prefixLift 2834284
  have htrace : WordTrace (prefixWord ++ tailWord_2834284) baseStart_2834284 baseEnd_2834284 := by
    simpa [prefixWord, tailWord_2834284, baseEnd_2834284] using wordTrace_append hprefix tailTrace_2834284
  have hstable : (prefixWord ++ tailWord_2834284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834284).length < 2 ^ (prefixWord ++ tailWord_2834284).sum := by decide
  have hdescent : baseEnd_2834284 < baseStart_2834284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834298 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_2834298 : Nat := 118140960795 + 2834298 * 2 ^ 59
def prefixEnd_2834298 : Nat := 4983230072969 + 3 ^ 40 * 2834298 * 2
def baseEnd_2834298 : Nat := 1455357192077057029740307

theorem tailTrace_2834298 : CollatzResearch.WordTrace tailWord_2834298 prefixEnd_2834298 1455357192077057029740307 := by
  unfold tailWord_2834298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25843835171457470101389887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68916893790553253603706365 25843835171457470101389887)
  ·
    refine ⟨38765752757186205152084831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25843835171457470101389887 38765752757186205152084831)
    ·
      refine ⟨58148629135779307728127247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38765752757186205152084831 58148629135779307728127247)
      ·
        refine ⟨87222943703668961592190871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58148629135779307728127247 87222943703668961592190871)
        ·
          refine ⟨130834415555503442388286307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87222943703668961592190871 130834415555503442388286307)
          ·
            refine ⟨196251623333255163582429461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130834415555503442388286307 196251623333255163582429461)
            ·
              refine ⟨9199294843746335792926381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196251623333255163582429461 9199294843746335792926381)
              ·
                refine ⟨3449735566404875922347393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9199294843746335792926381 3449735566404875922347393)
                ·
                  refine ⟨2587301674803656941760545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449735566404875922347393 2587301674803656941760545)
                  ·
                    refine ⟨1940476256102742706320409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2587301674803656941760545 1940476256102742706320409)
                    ·
                      refine ⟨1455357192077057029740307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940476256102742706320409 1455357192077057029740307)
                      ·
                        rfl

theorem cell23_2834298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_2834298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834298 prefixEnd_2834298 := by exact prefixLift 2834298
  have htrace : WordTrace (prefixWord ++ tailWord_2834298) baseStart_2834298 baseEnd_2834298 := by
    simpa [prefixWord, tailWord_2834298, baseEnd_2834298] using wordTrace_append hprefix tailTrace_2834298
  have hstable : (prefixWord ++ tailWord_2834298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834298).length < 2 ^ (prefixWord ++ tailWord_2834298).sum := by decide
  have hdescent : baseEnd_2834298 < baseStart_2834298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834326 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2834326 : Nat := 118140960795 + 2834326 * 2 ^ 59
def prefixEnd_2834326 : Nat := 4983230072969 + 3 ^ 40 * 2834326 * 2
def baseEnd_2834326 : Nat := 1455371569535382920190179

theorem tailTrace_2834326 : CollatzResearch.WordTrace tailWord_2834326 prefixEnd_2834326 1455371569535382920190179 := by
  unfold tailWord_2834326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461022620608027574223677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68917574619818960791719221 6461022620608027574223677)
  ·
    refine ⟨2422883482728010340333879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6461022620608027574223677 2422883482728010340333879)
    ·
      refine ⟨3634325224092015510500819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422883482728010340333879 3634325224092015510500819)
      ·
        refine ⟨5451487836138023265751229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634325224092015510500819 5451487836138023265751229)
        ·
          refine ⟨2044307938551758724656711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5451487836138023265751229 2044307938551758724656711)
          ·
            refine ⟨3066461907827638086985067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044307938551758724656711 3066461907827638086985067)
            ·
              refine ⟨4599692861741457130477601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066461907827638086985067 4599692861741457130477601)
              ·
                refine ⟨3449769646306092847858201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599692861741457130477601 3449769646306092847858201)
                ·
                  refine ⟨2587327234729569635893651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449769646306092847858201 2587327234729569635893651)
                  ·
                    refine ⟨3880990852094354453840477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2587327234729569635893651 3880990852094354453840477)
                    ·
                      refine ⟨1455371569535382920190179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3880990852094354453840477 1455371569535382920190179)
                      ·
                        rfl

theorem cell23_2834326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2834326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834326 prefixEnd_2834326 := by exact prefixLift 2834326
  have htrace : WordTrace (prefixWord ++ tailWord_2834326) baseStart_2834326 baseEnd_2834326 := by
    simpa [prefixWord, tailWord_2834326, baseEnd_2834326] using wordTrace_append hprefix tailTrace_2834326
  have hstable : (prefixWord ++ tailWord_2834326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834326).length < 2 ^ (prefixWord ++ tailWord_2834326).sum := by decide
  have hdescent : baseEnd_2834326 < baseStart_2834326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834332 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2834332 : Nat := 118140960795 + 2834332 * 2 ^ 59
def prefixEnd_2834332 : Nat := 4983230072969 + 3 ^ 40 * 2834332 * 2
def baseEnd_2834332 : Nat := 1455374650419309896715151

theorem tailTrace_2834332 : CollatzResearch.WordTrace tailWord_2834332 prefixEnd_2834332 1455374650419309896715151 := by
  unfold tailWord_2834332
  simp only [CollatzResearch.WordTrace]
  refine ⟨51688290383853352106148625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68917720511804469474864833 51688290383853352106148625)
  ·
    refine ⟨38766217787890014079611469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51688290383853352106148625 38766217787890014079611469)
    ·
      refine ⟨14537331670458755279854301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38766217787890014079611469 14537331670458755279854301)
      ·
        refine ⟨5451499376422033229945363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14537331670458755279854301 5451499376422033229945363)
        ·
          refine ⟨8177249064633049844918045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451499376422033229945363 8177249064633049844918045)
          ·
            refine ⟨3066468399237393691844267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8177249064633049844918045 3066468399237393691844267)
            ·
              refine ⟨4599702598856090537766401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066468399237393691844267 4599702598856090537766401)
              ·
                refine ⟨3449776949142067903324801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599702598856090537766401 3449776949142067903324801)
                ·
                  refine ⟨2587332711856550927493601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449776949142067903324801 2587332711856550927493601)
                  ·
                    refine ⟨1940499533892413195620201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2587332711856550927493601 1940499533892413195620201)
                    ·
                      refine ⟨1455374650419309896715151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940499533892413195620201 1455374650419309896715151)
                      ·
                        rfl

theorem cell23_2834332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2834332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834332 prefixEnd_2834332 := by exact prefixLift 2834332
  have htrace : WordTrace (prefixWord ++ tailWord_2834332) baseStart_2834332 baseEnd_2834332 := by
    simpa [prefixWord, tailWord_2834332, baseEnd_2834332] using wordTrace_append hprefix tailTrace_2834332
  have hstable : (prefixWord ++ tailWord_2834332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834332).length < 2 ^ (prefixWord ++ tailWord_2834332).sum := by decide
  have hdescent : baseEnd_2834332 < baseStart_2834332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834347 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 8]
def baseStart_2834347 : Nat := 118140960795 + 2834347 * 2 ^ 59
def prefixEnd_2834347 : Nat := 4983230072969 + 3 ^ 40 * 2834347 * 2
def baseEnd_2834347 : Nat := 485127450876375779342527

theorem tailTrace_2834347 : CollatzResearch.WordTrace tailWord_2834347 prefixEnd_2834347 485127450876375779342527 := by
  unfold tailWord_2834347
  simp only [CollatzResearch.WordTrace]
  refine ⟨103377127862652361774093295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68918085241768241182728863 103377127862652361774093295)
  ·
    refine ⟨155065691793978542661139943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103377127862652361774093295 155065691793978542661139943)
    ·
      refine ⟨232598537690967813991709915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155065691793978542661139943 232598537690967813991709915)
      ·
        refine ⟨348897806536451720987564873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232598537690967813991709915 348897806536451720987564873)
        ·
          refine ⟨261673354902338790740673655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348897806536451720987564873 261673354902338790740673655)
          ·
            refine ⟨392510032353508186111010483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261673354902338790740673655 392510032353508186111010483)
            ·
              refine ⟨588765048530262279166515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392510032353508186111010483 588765048530262279166515725)
              ·
                refine ⟨220786893198848354687443397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588765048530262279166515725 220786893198848354687443397)
                ·
                  refine ⟨41397542474784066503895637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220786893198848354687443397 41397542474784066503895637)
                  ·
                    refine ⟨485127450876375779342527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41397542474784066503895637 485127450876375779342527)
                    ·
                      rfl

theorem cell23_2834347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_2834347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834347 prefixEnd_2834347 := by exact prefixLift 2834347
  have htrace : WordTrace (prefixWord ++ tailWord_2834347) baseStart_2834347 baseEnd_2834347 := by
    simpa [prefixWord, tailWord_2834347, baseEnd_2834347] using wordTrace_append hprefix tailTrace_2834347
  have hstable : (prefixWord ++ tailWord_2834347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834347).length < 2 ^ (prefixWord ++ tailWord_2834347).sum := by decide
  have hdescent : baseEnd_2834347 < baseStart_2834347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834391 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2834391 : Nat := 118140960795 + 2834391 * 2 ^ 59
def prefixEnd_2834391 : Nat := 4983230072969 + 3 ^ 40 * 2834391 * 2
def baseEnd_2834391 : Nat := 1455404945777925165877379

theorem tailTrace_2834391 : CollatzResearch.WordTrace tailWord_2834391 prefixEnd_2834391 1455404945777925165877379 := by
  unfold tailWord_2834391
  simp only [CollatzResearch.WordTrace]
  refine ⟨103378732674492957288695027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68919155116328638192463351 103378732674492957288695027)
  ·
    refine ⟨155068099011739435933042541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103378732674492957288695027 155068099011739435933042541)
    ·
      refine ⟨58150537129402288474890953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155068099011739435933042541 58150537129402288474890953)
      ·
        refine ⟨43612902847051716356168215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58150537129402288474890953 43612902847051716356168215)
        ·
          refine ⟨65419354270577574534252323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43612902847051716356168215 65419354270577574534252323)
          ·
            refine ⟨98129031405866361801378485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65419354270577574534252323 98129031405866361801378485)
            ·
              refine ⟨9199596694299971418879233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98129031405866361801378485 9199596694299971418879233)
              ·
                refine ⟨6899697520724978564159425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9199596694299971418879233 6899697520724978564159425)
                ·
                  refine ⟨5174773140543733923119569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6899697520724978564159425 5174773140543733923119569)
                  ·
                    refine ⟨3881079855407800442339677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5174773140543733923119569 3881079855407800442339677)
                    ·
                      refine ⟨1455404945777925165877379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3881079855407800442339677 1455404945777925165877379)
                      ·
                        rfl

theorem cell23_2834391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2834391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834391 prefixEnd_2834391 := by exact prefixLift 2834391
  have htrace : WordTrace (prefixWord ++ tailWord_2834391) baseStart_2834391 baseEnd_2834391 := by
    simpa [prefixWord, tailWord_2834391, baseEnd_2834391] using wordTrace_append hprefix tailTrace_2834391
  have hstable : (prefixWord ++ tailWord_2834391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834391).length < 2 ^ (prefixWord ++ tailWord_2834391).sum := by decide
  have hdescent : baseEnd_2834391 < baseStart_2834391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834431 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 5, 2]
def baseStart_2834431 : Nat := 118140960795 + 2834431 * 2 ^ 59
def prefixEnd_2834431 : Nat := 4983230072969 + 3 ^ 40 * 2834431 * 2
def baseEnd_2834431 : Nat := 1455425485004105009377195

theorem tailTrace_2834431 : CollatzResearch.WordTrace tailWord_2834431 prefixEnd_2834431 1455425485004105009377195 := by
  unfold tailWord_2834431
  simp only [CollatzResearch.WordTrace]
  refine ⟨103380191594348044120151147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68920127729565362746767431 103380191594348044120151147)
  ·
    refine ⟨155070287391522066180226721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103380191594348044120151147 155070287391522066180226721)
    ·
      refine ⟨116302715543641549635170041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155070287391522066180226721 116302715543641549635170041)
      ·
        refine ⟨87227036657731162226377531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116302715543641549635170041 87227036657731162226377531)
        ·
          refine ⟨130840554986596743339566297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87227036657731162226377531 130840554986596743339566297)
          ·
            refine ⟨98130416239947557504674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130840554986596743339566297 98130416239947557504674723)
            ·
              refine ⟨147195624359921336257012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98130416239947557504674723 147195624359921336257012085)
              ·
                refine ⟨13799589783742625274094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147195624359921336257012085 13799589783742625274094883)
                ·
                  refine ⟨20699384675613937911142325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13799589783742625274094883 20699384675613937911142325)
                  ·
                    refine ⟨1940567313338806679169593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20699384675613937911142325 1940567313338806679169593)
                    ·
                      refine ⟨1455425485004105009377195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940567313338806679169593 1455425485004105009377195)
                      ·
                        rfl

theorem cell23_2834431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_2834431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834431 prefixEnd_2834431 := by exact prefixLift 2834431
  have htrace : WordTrace (prefixWord ++ tailWord_2834431) baseStart_2834431 baseEnd_2834431 := by
    simpa [prefixWord, tailWord_2834431, baseEnd_2834431] using wordTrace_append hprefix tailTrace_2834431
  have hstable : (prefixWord ++ tailWord_2834431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834431).length < 2 ^ (prefixWord ++ tailWord_2834431).sum := by decide
  have hdescent : baseEnd_2834431 < baseStart_2834431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834472 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2834472 : Nat := 118140960795 + 2834472 * 2 ^ 59
def prefixEnd_2834472 : Nat := 4983230072969 + 3 ^ 40 * 2834472 * 2
def baseEnd_2834472 : Nat := 1455446537710939348964507

theorem tailTrace_2834472 : CollatzResearch.WordTrace tailWord_2834472 prefixEnd_2834472 1455446537710939348964507 := by
  unfold tailWord_2834472
  simp only [CollatzResearch.WordTrace]
  refine ⟨51690843493599754061196835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68921124658133005414929113 51690843493599754061196835)
  ·
    refine ⟨77536265240399631091795253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51690843493599754061196835 77536265240399631091795253)
    ·
      refine ⟨7269024866287465414855805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77536265240399631091795253 7269024866287465414855805)
      ·
        refine ⟨2725884324857799530570927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7269024866287465414855805 2725884324857799530570927)
        ·
          refine ⟨4088826487286699295856391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725884324857799530570927 4088826487286699295856391)
          ·
            refine ⟨6133239730930048943784587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088826487286699295856391 6133239730930048943784587)
            ·
              refine ⟨9199859596395073415676881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133239730930048943784587 9199859596395073415676881)
              ·
                refine ⟨6899894697296305061757661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9199859596395073415676881 6899894697296305061757661)
                ·
                  refine ⟨2587460511486114398159123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6899894697296305061757661 2587460511486114398159123)
                  ·
                    refine ⟨3881190767229171597238685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2587460511486114398159123 3881190767229171597238685)
                    ·
                      refine ⟨1455446537710939348964507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3881190767229171597238685 1455446537710939348964507)
                      ·
                        rfl

theorem cell23_2834472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2834472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834472 prefixEnd_2834472 := by exact prefixLift 2834472
  have htrace : WordTrace (prefixWord ++ tailWord_2834472) baseStart_2834472 baseEnd_2834472 := by
    simpa [prefixWord, tailWord_2834472, baseEnd_2834472] using wordTrace_append hprefix tailTrace_2834472
  have hstable : (prefixWord ++ tailWord_2834472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834472).length < 2 ^ (prefixWord ++ tailWord_2834472).sum := by decide
  have hdescent : baseEnd_2834472 < baseStart_2834472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834478 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2834478 : Nat := 118140960795 + 2834478 * 2 ^ 59
def prefixEnd_2834478 : Nat := 4983230072969 + 3 ^ 40 * 2834478 * 2
def baseEnd_2834478 : Nat := 1455449618594866325489479

theorem tailTrace_2834478 : CollatzResearch.WordTrace tailWord_2834478 prefixEnd_2834478 1455449618594866325489479 := by
  unfold tailWord_2834478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922738228147221393389011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68921270550118514098074725 12922738228147221393389011)
  ·
    refine ⟨19384107342220832090083517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12922738228147221393389011 19384107342220832090083517)
    ·
      refine ⟨7269040253332812033781319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19384107342220832090083517 7269040253332812033781319)
      ·
        refine ⟨10903560379999218050671979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269040253332812033781319 10903560379999218050671979)
        ·
          refine ⟨16355340569998827076007969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10903560379999218050671979 16355340569998827076007969)
          ·
            refine ⟨12266505427499120307005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16355340569998827076007969 12266505427499120307005977)
            ·
              refine ⟨9199879070624340230254483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12266505427499120307005977 9199879070624340230254483)
              ·
                refine ⟨13799818605936510345381725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199879070624340230254483 13799818605936510345381725)
                ·
                  refine ⟨5174931977226191379518147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13799818605936510345381725 5174931977226191379518147)
                  ·
                    refine ⟨7762397965839287069277221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174931977226191379518147 7762397965839287069277221)
                    ·
                      refine ⟨1455449618594866325489479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7762397965839287069277221 1455449618594866325489479)
                      ·
                        rfl

theorem cell23_2834478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2834478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834478 prefixEnd_2834478 := by exact prefixLift 2834478
  have htrace : WordTrace (prefixWord ++ tailWord_2834478) baseStart_2834478 baseEnd_2834478 := by
    simpa [prefixWord, tailWord_2834478, baseEnd_2834478] using wordTrace_append hprefix tailTrace_2834478
  have hstable : (prefixWord ++ tailWord_2834478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834478).length < 2 ^ (prefixWord ++ tailWord_2834478).sum := by decide
  have hdescent : baseEnd_2834478 < baseStart_2834478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834525 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2834525 : Nat := 118140960795 + 2834525 * 2 ^ 59
def prefixEnd_2834525 : Nat := 4983230072969 + 3 ^ 40 * 2834525 * 2
def baseEnd_2834525 : Nat := 1455473752185627641601763

theorem tailTrace_2834525 : CollatzResearch.WordTrace tailWord_2834525 prefixEnd_2834525 1455473752185627641601763 := by
  unfold tailWord_2834525
  simp only [CollatzResearch.WordTrace]
  refine ⟨103383620056007498174073029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68922413370671665449382019 103383620056007498174073029)
  ·
    refine ⟨19384428760501405907638693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103383620056007498174073029 19384428760501405907638693)
    ·
      refine ⟨3634580392594013607682255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19384428760501405907638693 3634580392594013607682255)
      ·
        refine ⟨5451870588891020411523383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634580392594013607682255 5451870588891020411523383)
        ·
          refine ⟨8177805883336530617285075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451870588891020411523383 8177805883336530617285075)
          ·
            refine ⟨12266708825004795925927613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8177805883336530617285075 12266708825004795925927613)
            ·
              refine ⟨4600015809376798472222855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12266708825004795925927613 4600015809376798472222855)
              ·
                refine ⟨6900023714065197708334283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600015809376798472222855 6900023714065197708334283)
                ·
                  refine ⟨10350035571097796562501425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6900023714065197708334283 10350035571097796562501425)
                  ·
                    refine ⟨7762526678323347421876069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10350035571097796562501425 7762526678323347421876069)
                    ·
                      refine ⟨1455473752185627641601763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7762526678323347421876069 1455473752185627641601763)
                      ·
                        rfl

theorem cell23_2834525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2834525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834525 prefixEnd_2834525 := by exact prefixLift 2834525
  have htrace : WordTrace (prefixWord ++ tailWord_2834525) baseStart_2834525 baseEnd_2834525 := by
    simpa [prefixWord, tailWord_2834525, baseEnd_2834525] using wordTrace_append hprefix tailTrace_2834525
  have hstable : (prefixWord ++ tailWord_2834525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834525).length < 2 ^ (prefixWord ++ tailWord_2834525).sum := by decide
  have hdescent : baseEnd_2834525 < baseStart_2834525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834528 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_2834528 : Nat := 118140960795 + 2834528 * 2 ^ 59
def prefixEnd_2834528 : Nat := 4983230072969 + 3 ^ 40 * 2834528 * 2
def baseEnd_2834528 : Nat := 1455475292627591129864249

theorem tailTrace_2834528 : CollatzResearch.WordTrace tailWord_2834528 prefixEnd_2834528 1455475292627591129864249 := by
  unfold tailWord_2834528
  simp only [CollatzResearch.WordTrace]
  refine ⟨51691864737498314843216119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68922486316664419790954825 51691864737498314843216119)
  ·
    refine ⟨77537797106247472264824179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51691864737498314843216119 77537797106247472264824179)
    ·
      refine ⟨116306695659371208397236269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77537797106247472264824179 116306695659371208397236269)
      ·
        refine ⟨43615010872264203148963601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116306695659371208397236269 43615010872264203148963601)
        ·
          refine ⟨32711258154198152361722701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43615010872264203148963601 32711258154198152361722701)
          ·
            refine ⟨12266721807824307135646013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32711258154198152361722701 12266721807824307135646013)
            ·
              refine ⟨4600020677934115175867255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12266721807824307135646013 4600020677934115175867255)
              ·
                refine ⟨6900031016901172763800883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600020677934115175867255 6900031016901172763800883)
                ·
                  refine ⟨10350046525351759145701325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6900031016901172763800883 10350046525351759145701325)
                  ·
                    refine ⟨3881267447006909679637997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10350046525351759145701325 3881267447006909679637997)
                    ·
                      refine ⟨1455475292627591129864249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3881267447006909679637997 1455475292627591129864249)
                      ·
                        rfl

theorem cell23_2834528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_2834528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834528 prefixEnd_2834528 := by exact prefixLift 2834528
  have htrace : WordTrace (prefixWord ++ tailWord_2834528) baseStart_2834528 baseEnd_2834528 := by
    simpa [prefixWord, tailWord_2834528, baseEnd_2834528] using wordTrace_append hprefix tailTrace_2834528
  have hstable : (prefixWord ++ tailWord_2834528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834528).length < 2 ^ (prefixWord ++ tailWord_2834528).sum := by decide
  have hdescent : baseEnd_2834528 < baseStart_2834528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834541 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2834541 : Nat := 118140960795 + 2834541 * 2 ^ 59
def prefixEnd_2834541 : Nat := 4983230072969 + 3 ^ 40 * 2834541 * 2
def baseEnd_2834541 : Nat := 1455481967876099579001689

theorem tailTrace_2834541 : CollatzResearch.WordTrace tailWord_2834541 prefixEnd_2834541 1455481967876099579001689 := by
  unfold tailWord_2834541
  simp only [CollatzResearch.WordTrace]
  refine ⟨103384203623949532906655477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68922802415966355271103651 103384203623949532906655477)
  ·
    refine ⟨9692269089745268709998951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103384203623949532906655477 9692269089745268709998951)
    ·
      refine ⟨14538403634617903064998427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9692269089745268709998951 14538403634617903064998427)
      ·
        refine ⟨21807605451926854597497641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14538403634617903064998427 21807605451926854597497641)
        ·
          refine ⟨16355704088945140948123231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21807605451926854597497641 16355704088945140948123231)
          ·
            refine ⟨24533556133417711422184847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16355704088945140948123231 24533556133417711422184847)
            ·
              refine ⟨36800334200126567133277271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24533556133417711422184847 36800334200126567133277271)
              ·
                refine ⟨55200501300189850699915907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36800334200126567133277271 55200501300189850699915907)
                ·
                  refine ⟨82800751950284776049873861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55200501300189850699915907 82800751950284776049873861)
                  ·
                    refine ⟨15525140990678395509351349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82800751950284776049873861 15525140990678395509351349)
                    ·
                      refine ⟨1455481967876099579001689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15525140990678395509351349 1455481967876099579001689)
                      ·
                        rfl

theorem cell23_2834541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2834541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834541 prefixEnd_2834541 := by exact prefixLift 2834541
  have htrace : WordTrace (prefixWord ++ tailWord_2834541) baseStart_2834541 baseEnd_2834541 := by
    simpa [prefixWord, tailWord_2834541, baseEnd_2834541] using wordTrace_append hprefix tailTrace_2834541
  have hstable : (prefixWord ++ tailWord_2834541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834541).length < 2 ^ (prefixWord ++ tailWord_2834541).sum := by decide
  have hdescent : baseEnd_2834541 < baseStart_2834541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834581 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2834581 : Nat := 118140960795 + 2834581 * 2 ^ 59
def prefixEnd_2834581 : Nat := 4983230072969 + 3 ^ 40 * 2834581 * 2
def baseEnd_2834581 : Nat := 1455502507102279422501505

theorem tailTrace_2834581 : CollatzResearch.WordTrace tailWord_2834581 prefixEnd_2834581 1455502507102279422501505 := by
  unfold tailWord_2834581
  simp only [CollatzResearch.WordTrace]
  refine ⟨103385662543804619738111597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68923775029203079825407731 103385662543804619738111597)
  ·
    refine ⟨38769623453926732401791849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103385662543804619738111597 38769623453926732401791849)
    ·
      refine ⟨29077217590445049301343887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38769623453926732401791849 29077217590445049301343887)
      ·
        refine ⟨43615826385667573952015831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29077217590445049301343887 43615826385667573952015831)
        ·
          refine ⟨65423739578501360928023747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43615826385667573952015831 65423739578501360928023747)
          ·
            refine ⟨98135609367752041392035621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65423739578501360928023747 98135609367752041392035621)
            ·
              refine ⟨18400426756453507761006679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98135609367752041392035621 18400426756453507761006679)
              ·
                refine ⟨27600640134680261641510019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18400426756453507761006679 27600640134680261641510019)
                ·
                  refine ⟨41400960202020392462265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27600640134680261641510019 41400960202020392462265029)
                  ·
                    refine ⟨7762680037878823586674693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41400960202020392462265029 7762680037878823586674693)
                    ·
                      refine ⟨1455502507102279422501505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7762680037878823586674693 1455502507102279422501505)
                      ·
                        rfl

theorem cell23_2834581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2834581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834581 prefixEnd_2834581 := by exact prefixLift 2834581
  have htrace : WordTrace (prefixWord ++ tailWord_2834581) baseStart_2834581 baseEnd_2834581 := by
    simpa [prefixWord, tailWord_2834581, baseEnd_2834581] using wordTrace_append hprefix tailTrace_2834581
  have hstable : (prefixWord ++ tailWord_2834581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834581).length < 2 ^ (prefixWord ++ tailWord_2834581).sum := by decide
  have hdescent : baseEnd_2834581 < baseStart_2834581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834621 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2834621 : Nat := 118140960795 + 2834621 * 2 ^ 59
def prefixEnd_2834621 : Nat := 4983230072969 + 3 ^ 40 * 2834621 * 2
def baseEnd_2834621 : Nat := 485174348776153088667107

theorem tailTrace_2834621 : CollatzResearch.WordTrace tailWord_2834621 prefixEnd_2834621 485174348776153088667107 := by
  unfold tailWord_2834621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103387121463659706569567717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68924747642439804379711811 103387121463659706569567717)
  ·
    refine ⟨19385085274436194981793947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103387121463659706569567717 19385085274436194981793947)
    ·
      refine ⟨29077627911654292472690921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19385085274436194981793947 29077627911654292472690921)
      ·
        refine ⟨21808220933740719354518191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29077627911654292472690921 21808220933740719354518191)
        ·
          refine ⟨32712331400611079031777287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21808220933740719354518191 32712331400611079031777287)
          ·
            refine ⟨49068497100916618547665931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32712331400611079031777287 49068497100916618547665931)
            ·
              refine ⟨73602745651374927821498897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49068497100916618547665931 73602745651374927821498897)
              ·
                refine ⟨55202059238531195866124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73602745651374927821498897 55202059238531195866124173)
                ·
                  refine ⟨20700772214449198449796565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55202059238531195866124173 20700772214449198449796565)
                  ·
                    refine ⟨485174348776153088667107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20700772214449198449796565 485174348776153088667107)
                    ·
                      rfl

theorem cell23_2834621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2834621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834621 prefixEnd_2834621 := by exact prefixLift 2834621
  have htrace : WordTrace (prefixWord ++ tailWord_2834621) baseStart_2834621 baseEnd_2834621 := by
    simpa [prefixWord, tailWord_2834621, baseEnd_2834621] using wordTrace_append hprefix tailTrace_2834621
  have hstable : (prefixWord ++ tailWord_2834621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834621).length < 2 ^ (prefixWord ++ tailWord_2834621).sum := by decide
  have hdescent : baseEnd_2834621 < baseStart_2834621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834668 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_2834668 : Nat := 118140960795 + 2834668 * 2 ^ 59
def prefixEnd_2834668 : Nat := 4983230072969 + 3 ^ 40 * 2834668 * 2
def baseEnd_2834668 : Nat := 485182393306406860704535

theorem tailTrace_2834668 : CollatzResearch.WordTrace tailWord_2834668 prefixEnd_2834668 485182393306406860704535 := by
  unfold tailWord_2834668
  simp only [CollatzResearch.WordTrace]
  refine ⟨51694417847244716798264329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68925890462992955731019105 51694417847244716798264329)
  ·
    refine ⟨38770813385433537598698247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51694417847244716798264329 38770813385433537598698247)
    ·
      refine ⟨58156220078150306398047371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38770813385433537598698247 58156220078150306398047371)
      ·
        refine ⟨87234330117225459597071057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58156220078150306398047371 87234330117225459597071057)
        ·
          refine ⟨65425747587919094697803293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87234330117225459597071057 65425747587919094697803293)
          ·
            refine ⟨24534655345469660511676235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65425747587919094697803293 24534655345469660511676235)
            ·
              refine ⟨36801983018204490767514353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24534655345469660511676235 36801983018204490767514353)
              ·
                refine ⟨27601487263653368075635765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36801983018204490767514353 27601487263653368075635765)
                ·
                  refine ⟨2587639430967503257090853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27601487263653368075635765 2587639430967503257090853)
                  ·
                    refine ⟨485182393306406860704535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587639430967503257090853 485182393306406860704535)
                    ·
                      rfl

theorem cell23_2834668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_2834668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834668 prefixEnd_2834668 := by exact prefixLift 2834668
  have htrace : WordTrace (prefixWord ++ tailWord_2834668) baseStart_2834668 baseEnd_2834668 := by
    simpa [prefixWord, tailWord_2834668, baseEnd_2834668] using wordTrace_append hprefix tailTrace_2834668
  have hstable : (prefixWord ++ tailWord_2834668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834668).length < 2 ^ (prefixWord ++ tailWord_2834668).sum := by decide
  have hdescent : baseEnd_2834668 < baseStart_2834668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834678 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2834678 : Nat := 118140960795 + 2834678 * 2 ^ 59
def prefixEnd_2834678 : Nat := 4983230072969 + 3 ^ 40 * 2834678 * 2
def baseEnd_2834678 : Nat := 1455552314725765542988559

theorem tailTrace_2834678 : CollatzResearch.WordTrace tailWord_2834678 prefixEnd_2834678 1455552314725765542988559 := by
  unfold tailWord_2834678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461825026528325331524543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68926133616302136869595125 6461825026528325331524543)
  ·
    refine ⟨9692737539792487997286815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6461825026528325331524543 9692737539792487997286815)
    ·
      refine ⟨14539106309688731995930223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9692737539792487997286815 14539106309688731995930223)
      ·
        refine ⟨21808659464533097993895335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14539106309688731995930223 21808659464533097993895335)
        ·
          refine ⟨32712989196799646990843003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21808659464533097993895335 32712989196799646990843003)
          ·
            refine ⟨49069483795199470486264505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32712989196799646990843003 49069483795199470486264505)
            ·
              refine ⟨36802112846399602864698379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49069483795199470486264505 36802112846399602864698379)
              ·
                refine ⟨55203169269599404297047569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36802112846399602864698379 55203169269599404297047569)
                ·
                  refine ⟨41402376952199553222785677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55203169269599404297047569 41402376952199553222785677)
                  ·
                    refine ⟨15525891357074832458544629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41402376952199553222785677 15525891357074832458544629)
                    ·
                      refine ⟨1455552314725765542988559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15525891357074832458544629 1455552314725765542988559)
                      ·
                        rfl

theorem cell23_2834678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2834678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834678 prefixEnd_2834678 := by exact prefixLift 2834678
  have htrace : WordTrace (prefixWord ++ tailWord_2834678) baseStart_2834678 baseEnd_2834678 := by
    simpa [prefixWord, tailWord_2834678, baseEnd_2834678] using wordTrace_append hprefix tailTrace_2834678
  have hstable : (prefixWord ++ tailWord_2834678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834678).length < 2 ^ (prefixWord ++ tailWord_2834678).sum := by decide
  have hdescent : baseEnd_2834678 < baseStart_2834678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834698 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_2834698 : Nat := 118140960795 + 2834698 * 2 ^ 59
def prefixEnd_2834698 : Nat := 4983230072969 + 3 ^ 40 * 2834698 * 2
def baseEnd_2834698 : Nat := 161729176037650607193163

theorem tailTrace_2834698 : CollatzResearch.WordTrace tailWord_2834698 prefixEnd_2834698 161729176037650607193163 := by
  unfold tailWord_2834698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25847482471095187180030187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68926619922920499146747165 25847482471095187180030187)
  ·
    refine ⟨38771223706642780770045281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25847482471095187180030187 38771223706642780770045281)
    ·
      refine ⟨29078417779982085577533961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38771223706642780770045281 29078417779982085577533961)
      ·
        refine ⟨21808813334986564183150471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29078417779982085577533961 21808813334986564183150471)
        ·
          refine ⟨32713220002479846274725707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21808813334986564183150471 32713220002479846274725707)
          ·
            refine ⟨49069830003719769412088561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32713220002479846274725707 49069830003719769412088561)
            ·
              refine ⟨36802372502789827059066421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49069830003719769412088561 36802372502789827059066421)
              ·
                refine ⟨3450222422136546286787477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36802372502789827059066421 3450222422136546286787477)
                ·
                  refine ⟨161729176037650607193163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3450222422136546286787477 161729176037650607193163)
                  ·
                    rfl

theorem cell23_2834698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_2834698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834698 prefixEnd_2834698 := by exact prefixLift 2834698
  have htrace : WordTrace (prefixWord ++ tailWord_2834698) baseStart_2834698 baseEnd_2834698 := by
    simpa [prefixWord, tailWord_2834698, baseEnd_2834698] using wordTrace_append hprefix tailTrace_2834698
  have hstable : (prefixWord ++ tailWord_2834698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834698).length < 2 ^ (prefixWord ++ tailWord_2834698).sum := by decide
  have hdescent : baseEnd_2834698 < baseStart_2834698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834719 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 1, 4]
def baseStart_2834719 : Nat := 118140960795 + 2834719 * 2 ^ 59
def prefixEnd_2834719 : Nat := 4983230072969 + 3 ^ 40 * 2834719 * 2
def baseEnd_2834719 : Nat := 485191122477533294191957

theorem tailTrace_2834719 : CollatzResearch.WordTrace tailWord_2834719 prefixEnd_2834719 485191122477533294191957 := by
  unfold tailWord_2834719
  simp only [CollatzResearch.WordTrace]
  refine ⟨103390695817304669306635211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68927130544869779537756807 103390695817304669306635211)
  ·
    refine ⟨155086043725957003959952817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103390695817304669306635211 155086043725957003959952817)
    ·
      refine ⟨116314532794467752969964613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155086043725957003959952817 116314532794467752969964613)
      ·
        refine ⟨21808974898962703681868365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116314532794467752969964613 21808974898962703681868365)
        ·
          refine ⟨8178365587111013880700637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21808974898962703681868365 8178365587111013880700637)
          ·
            refine ⟨3066887095166630205262739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8178365587111013880700637 3066887095166630205262739)
            ·
              refine ⟨4600330642749945307894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066887095166630205262739 4600330642749945307894109)
              ·
                refine ⟨1725123991031229490460291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4600330642749945307894109 1725123991031229490460291)
                ·
                  refine ⟨2587685986546844235690437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725123991031229490460291 2587685986546844235690437)
                  ·
                    refine ⟨485191122477533294191957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587685986546844235690437 485191122477533294191957)
                    ·
                      rfl

theorem cell23_2834719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_2834719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834719 prefixEnd_2834719 := by exact prefixLift 2834719
  have htrace : WordTrace (prefixWord ++ tailWord_2834719) baseStart_2834719 baseEnd_2834719 := by
    simpa [prefixWord, tailWord_2834719, baseEnd_2834719] using wordTrace_append hprefix tailTrace_2834719
  have hstable : (prefixWord ++ tailWord_2834719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834719).length < 2 ^ (prefixWord ++ tailWord_2834719).sum := by decide
  have hdescent : baseEnd_2834719 < baseStart_2834719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834735 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 4, 3, 2]
def baseStart_2834735 : Nat := 118140960795 + 2834735 * 2 ^ 59
def prefixEnd_2834735 : Nat := 4983230072969 + 3 ^ 40 * 2834735 * 2
def baseEnd_2834735 : Nat := 1455581583123071819975797

theorem tailTrace_2834735 : CollatzResearch.WordTrace tailWord_2834735 prefixEnd_2834735 1455581583123071819975797 := by
  unfold tailWord_2834735
  simp only [CollatzResearch.WordTrace]
  refine ⟨103391279385246704039217659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68927519590164469359478439 103391279385246704039217659)
  ·
    refine ⟨155086919077870056058826489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103391279385246704039217659 155086919077870056058826489)
    ·
      refine ⟨116315189308402542044119867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155086919077870056058826489 116315189308402542044119867)
      ·
        refine ⟨174472783962603813066179801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116315189308402542044119867 174472783962603813066179801)
        ·
          refine ⟨130854587971952859799634851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174472783962603813066179801 130854587971952859799634851)
          ·
            refine ⟨196281881957929289699452277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130854587971952859799634851 196281881957929289699452277)
            ·
              refine ⟨18401426433555870909323651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196281881957929289699452277 18401426433555870909323651)
              ·
                refine ⟨27602139650333806363985477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18401426433555870909323651 27602139650333806363985477)
                ·
                  refine ⟨5175401184437588693247277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27602139650333806363985477 5175401184437588693247277)
                  ·
                    refine ⟨1940775444164095759967729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5175401184437588693247277 1940775444164095759967729)
                    ·
                      refine ⟨1455581583123071819975797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940775444164095759967729 1455581583123071819975797)
                      ·
                        rfl

theorem cell23_2834735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3, 2].length) (baseStart_2834735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834735 prefixEnd_2834735 := by exact prefixLift 2834735
  have htrace : WordTrace (prefixWord ++ tailWord_2834735) baseStart_2834735 baseEnd_2834735 := by
    simpa [prefixWord, tailWord_2834735, baseEnd_2834735] using wordTrace_append hprefix tailTrace_2834735
  have hstable : (prefixWord ++ tailWord_2834735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834735).length < 2 ^ (prefixWord ++ tailWord_2834735).sum := by decide
  have hdescent : baseEnd_2834735 < baseStart_2834735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834792 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2834792 : Nat := 118140960795 + 2834792 * 2 ^ 59
def prefixEnd_2834792 : Nat := 4983230072969 + 3 ^ 40 * 2834792 * 2
def baseEnd_2834792 : Nat := 485203617173459365654345

theorem tailTrace_2834792 : CollatzResearch.WordTrace tailWord_2834792 prefixEnd_2834792 485203617173459365654345 := by
  unfold tailWord_2834792
  simp only [CollatzResearch.WordTrace]
  refine ⟨51696679173020101387021315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68928905564026801849361753 51696679173020101387021315)
  ·
    refine ⟨77545018759530152080531973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51696679173020101387021315 77545018759530152080531973)
    ·
      refine ⟨14539691017411903515099745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77545018759530152080531973 14539691017411903515099745)
      ·
        refine ⟨10904768263058927636324809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14539691017411903515099745 10904768263058927636324809)
        ·
          refine ⟨8178576197294195727243607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10904768263058927636324809 8178576197294195727243607)
          ·
            refine ⟨12267864295941293590865411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178576197294195727243607 12267864295941293590865411)
            ·
              refine ⟨18401796443911940386298117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12267864295941293590865411 18401796443911940386298117)
              ·
                refine ⟨3450336833233488822430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18401796443911940386298117 3450336833233488822430897)
                ·
                  refine ⟨2587752624925116616823173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450336833233488822430897 2587752624925116616823173)
                  ·
                    refine ⟨485203617173459365654345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587752624925116616823173 485203617173459365654345)
                    ·
                      rfl

theorem cell23_2834792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2834792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834792 prefixEnd_2834792 := by exact prefixLift 2834792
  have htrace : WordTrace (prefixWord ++ tailWord_2834792) baseStart_2834792 baseEnd_2834792 := by
    simpa [prefixWord, tailWord_2834792, baseEnd_2834792] using wordTrace_append hprefix tailTrace_2834792
  have hstable : (prefixWord ++ tailWord_2834792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834792).length < 2 ^ (prefixWord ++ tailWord_2834792).sum := by decide
  have hdescent : baseEnd_2834792 < baseStart_2834792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834805 : List Nat := [1, 3, 4, 1, 2, 1, 3, 8]
def baseStart_2834805 : Nat := 118140960795 + 2834805 * 2 ^ 59
def prefixEnd_2834805 : Nat := 4983230072969 + 3 ^ 40 * 2834805 * 2
def baseEnd_2834805 : Nat := 53911760250699501707425

theorem tailTrace_2834805 : CollatzResearch.WordTrace tailWord_2834805 prefixEnd_2834805 53911760250699501707425 := by
  unfold tailWord_2834805
  simp only [CollatzResearch.WordTrace]
  refine ⟨103393832494993105994265869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68929221663328737329510579 103393832494993105994265869)
  ·
    refine ⟨38772687185622414747849701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103393832494993105994265869 38772687185622414747849701)
    ·
      refine ⟨7269878847304202765221819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38772687185622414747849701 7269878847304202765221819)
      ·
        refine ⟨10904818270956304147832729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269878847304202765221819 10904818270956304147832729)
        ·
          refine ⟨8178613703217228110874547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10904818270956304147832729 8178613703217228110874547)
          ·
            refine ⟨12267920554825842166311821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178613703217228110874547 12267920554825842166311821)
            ·
              refine ⟨4600470208059690812366933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12267920554825842166311821 4600470208059690812366933)
              ·
                refine ⟨53911760250699501707425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4600470208059690812366933 53911760250699501707425)
                ·
                  rfl

theorem cell23_2834805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 8].length) (baseStart_2834805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834805 prefixEnd_2834805 := by exact prefixLift 2834805
  have htrace : WordTrace (prefixWord ++ tailWord_2834805) baseStart_2834805 baseEnd_2834805 := by
    simpa [prefixWord, tailWord_2834805, baseEnd_2834805] using wordTrace_append hprefix tailTrace_2834805
  have hstable : (prefixWord ++ tailWord_2834805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834805).length < 2 ^ (prefixWord ++ tailWord_2834805).sum := by decide
  have hdescent : baseEnd_2834805 < baseStart_2834805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834865 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_2834865 : Nat := 118140960795 + 2834865 * 2 ^ 59
def prefixEnd_2834865 : Nat := 4983230072969 + 3 ^ 40 * 2834865 * 2
def baseEnd_2834865 : Nat := 485216111869385437116733

theorem tailTrace_2834865 : CollatzResearch.WordTrace tailWord_2834865 prefixEnd_2834865 485216111869385437116733 := by
  unfold tailWord_2834865
  simp only [CollatzResearch.WordTrace]
  refine ⟨103396020874775736241450049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68930680583183824160966699 103396020874775736241450049)
  ·
    refine ⟨77547015656081802181087537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103396020874775736241450049 77547015656081802181087537)
    ·
      refine ⟨58160261742061351635815653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77547015656081802181087537 58160261742061351635815653)
      ·
        refine ⟨10905049076636503431715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58160261742061351635815653 10905049076636503431715435)
        ·
          refine ⟨16357573614954755147573153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10905049076636503431715435 16357573614954755147573153)
          ·
            refine ⟨12268180211216066360679865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16357573614954755147573153 12268180211216066360679865)
            ·
              refine ⟨9201135158412049770509899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12268180211216066360679865 9201135158412049770509899)
              ·
                refine ⟨13801702737618074655764849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201135158412049770509899 13801702737618074655764849)
                ·
                  refine ⟨10351277053213555991823637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13801702737618074655764849 10351277053213555991823637)
                  ·
                    refine ⟨485216111869385437116733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10351277053213555991823637 485216111869385437116733)
                    ·
                      rfl

theorem cell23_2834865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_2834865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834865 prefixEnd_2834865 := by exact prefixLift 2834865
  have htrace : WordTrace (prefixWord ++ tailWord_2834865) baseStart_2834865 baseEnd_2834865 := by
    simpa [prefixWord, tailWord_2834865, baseEnd_2834865] using wordTrace_append hprefix tailTrace_2834865
  have hstable : (prefixWord ++ tailWord_2834865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834865).length < 2 ^ (prefixWord ++ tailWord_2834865).sum := by decide
  have hdescent : baseEnd_2834865 < baseStart_2834865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834876 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2834876 : Nat := 118140960795 + 2834876 * 2 ^ 59
def prefixEnd_2834876 : Nat := 4983230072969 + 3 ^ 40 * 2834876 * 2
def baseEnd_2834876 : Nat := 1455653983895355768312649

theorem tailTrace_2834876 : CollatzResearch.WordTrace tailWord_2834876 prefixEnd_2834876 1455653983895355768312649 := by
  unfold tailWord_2834876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51698211038867942560050241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68930948051823923413400321 51698211038867942560050241)
  ·
    refine ⟨38773658279150956920037681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51698211038867942560050241 38773658279150956920037681)
    ·
      refine ⟨29080243709363217690028261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38773658279150956920037681 29080243709363217690028261)
      ·
        refine ⟨5452545695505603316880299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29080243709363217690028261 5452545695505603316880299)
        ·
          refine ⟨8178818543258404975320449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452545695505603316880299 8178818543258404975320449)
          ·
            refine ⟨6134113907443803731490337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8178818543258404975320449 6134113907443803731490337)
            ·
              refine ⟨4600585430582852798617753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6134113907443803731490337 4600585430582852798617753)
              ·
                refine ⟨3450439072937139598963315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600585430582852798617753 3450439072937139598963315)
                ·
                  refine ⟨5175658609405709398444973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450439072937139598963315 5175658609405709398444973)
                  ·
                    refine ⟨1940871978527141024416865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5175658609405709398444973 1940871978527141024416865)
                    ·
                      refine ⟨1455653983895355768312649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940871978527141024416865 1455653983895355768312649)
                      ·
                        rfl

theorem cell23_2834876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2834876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834876 prefixEnd_2834876 := by exact prefixLift 2834876
  have htrace : WordTrace (prefixWord ++ tailWord_2834876) baseStart_2834876 baseEnd_2834876 := by
    simpa [prefixWord, tailWord_2834876, baseEnd_2834876] using wordTrace_append hprefix tailTrace_2834876
  have hstable : (prefixWord ++ tailWord_2834876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834876).length < 2 ^ (prefixWord ++ tailWord_2834876).sum := by decide
  have hdescent : baseEnd_2834876 < baseStart_2834876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834892 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2834892 : Nat := 118140960795 + 2834892 * 2 ^ 59
def prefixEnd_2834892 : Nat := 4983230072969 + 3 ^ 40 * 2834892 * 2
def baseEnd_2834892 : Nat := 1455662199585827705712575

theorem tailTrace_2834892 : CollatzResearch.WordTrace tailWord_2834892 prefixEnd_2834892 1455662199585827705712575 := by
  unfold tailWord_2834892
  simp only [CollatzResearch.WordTrace]
  refine ⟨51698502822838959926341465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68931337097118613235121953 51698502822838959926341465)
  ·
    refine ⟨38773877117129219944756099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51698502822838959926341465 38773877117129219944756099)
    ·
      refine ⟨58160815675693829917134149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38773877117129219944756099 58160815675693829917134149)
      ·
        refine ⟨10905152939192593109462653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58160815675693829917134149 10905152939192593109462653)
        ·
          refine ⟨4089432352197222416048495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10905152939192593109462653 4089432352197222416048495)
          ·
            refine ⟨6134148528295833624072743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089432352197222416048495 6134148528295833624072743)
            ·
              refine ⟨9201222792443750436109115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134148528295833624072743 9201222792443750436109115)
              ·
                refine ⟨13801834188665625654163673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201222792443750436109115 13801834188665625654163673)
                ·
                  refine ⟨10351375641499219240622755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13801834188665625654163673 10351375641499219240622755)
                  ·
                    refine ⟨15527063462248828860934133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10351375641499219240622755 15527063462248828860934133)
                    ·
                      refine ⟨1455662199585827705712575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15527063462248828860934133 1455662199585827705712575)
                      ·
                        rfl

theorem cell23_2834892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2834892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834892 prefixEnd_2834892 := by exact prefixLift 2834892
  have htrace : WordTrace (prefixWord ++ tailWord_2834892) baseStart_2834892 baseEnd_2834892 := by
    simpa [prefixWord, tailWord_2834892, baseEnd_2834892] using wordTrace_append hprefix tailTrace_2834892
  have hstable : (prefixWord ++ tailWord_2834892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834892).length < 2 ^ (prefixWord ++ tailWord_2834892).sum := by decide
  have hdescent : baseEnd_2834892 < baseStart_2834892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834965 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2834965 : Nat := 118140960795 + 2834965 * 2 ^ 59
def prefixEnd_2834965 : Nat := 4983230072969 + 3 ^ 40 * 2834965 * 2
def baseEnd_2834965 : Nat := 1455699683673605920099739

theorem tailTrace_2834965 : CollatzResearch.WordTrace tailWord_2834965 prefixEnd_2834965 1455699683673605920099739 := by
  unfold tailWord_2834965
  simp only [CollatzResearch.WordTrace]
  refine ⟨103399668174413453320090349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68933112116275635546726899 103399668174413453320090349)
  ·
    refine ⟨38774875565405044995033881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103399668174413453320090349 38774875565405044995033881)
    ·
      refine ⟨29081156674053783746275411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38774875565405044995033881 29081156674053783746275411)
      ·
        refine ⟨43621735011080675619413117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29081156674053783746275411 43621735011080675619413117)
        ·
          refine ⟨16358150629155253357279919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43621735011080675619413117 16358150629155253357279919)
          ·
            refine ⟨24537225943732880035919879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358150629155253357279919 24537225943732880035919879)
            ·
              refine ⟨36805838915599320053879819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24537225943732880035919879 36805838915599320053879819)
              ·
                refine ⟨55208758373398980080819729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36805838915599320053879819 55208758373398980080819729)
                ·
                  refine ⟨41406568780049235060614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55208758373398980080819729 41406568780049235060614797)
                  ·
                    refine ⟨15527463292518463147730549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41406568780049235060614797 15527463292518463147730549)
                    ·
                      refine ⟨1455699683673605920099739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15527463292518463147730549 1455699683673605920099739)
                      ·
                        rfl

theorem cell23_2834965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2834965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834965 prefixEnd_2834965 := by exact prefixLift 2834965
  have htrace : WordTrace (prefixWord ++ tailWord_2834965) baseStart_2834965 baseEnd_2834965 := by
    simpa [prefixWord, tailWord_2834965, baseEnd_2834965] using wordTrace_append hprefix tailTrace_2834965
  have hstable : (prefixWord ++ tailWord_2834965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834965).length < 2 ^ (prefixWord ++ tailWord_2834965).sum := by decide
  have hdescent : baseEnd_2834965 < baseStart_2834965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834975 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2834975 : Nat := 118140960795 + 2834975 * 2 ^ 59
def prefixEnd_2834975 : Nat := 4983230072969 + 3 ^ 40 * 2834975 * 2
def baseEnd_2834975 : Nat := 1455704818480150880974693

theorem tailTrace_2834975 : CollatzResearch.WordTrace tailWord_2834975 prefixEnd_2834975 1455704818480150880974693 := by
  unfold tailWord_2834975
  simp only [CollatzResearch.WordTrace]
  refine ⟨103400032904377225027954379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68933355269584816685302919 103400032904377225027954379)
  ·
    refine ⟨155100049356565837541931569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103400032904377225027954379 155100049356565837541931569)
    ·
      refine ⟨116325037017424378156448677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155100049356565837541931569 116325037017424378156448677)
      ·
        refine ⟨21810944440767070904334127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116325037017424378156448677 21810944440767070904334127)
        ·
          refine ⟨32716416661150606356501191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21810944440767070904334127 32716416661150606356501191)
          ·
            refine ⟨49074624991725909534751787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32716416661150606356501191 49074624991725909534751787)
            ·
              refine ⟨73611937487588864302127681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49074624991725909534751787 73611937487588864302127681)
              ·
                refine ⟨55208953115691648226595761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73611937487588864302127681 55208953115691648226595761)
                ·
                  refine ⟨41406714836768736169946821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55208953115691648226595761 41406714836768736169946821)
                  ·
                    refine ⟨7763759031894138031865029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41406714836768736169946821 7763759031894138031865029)
                    ·
                      refine ⟨1455704818480150880974693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7763759031894138031865029 1455704818480150880974693)
                      ·
                        rfl

theorem cell23_2834975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2834975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834975 prefixEnd_2834975 := by exact prefixLift 2834975
  have htrace : WordTrace (prefixWord ++ tailWord_2834975) baseStart_2834975 baseEnd_2834975 := by
    simpa [prefixWord, tailWord_2834975, baseEnd_2834975] using wordTrace_append hprefix tailTrace_2834975
  have hstable : (prefixWord ++ tailWord_2834975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834975).length < 2 ^ (prefixWord ++ tailWord_2834975).sum := by decide
  have hdescent : baseEnd_2834975 < baseStart_2834975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834979 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 4, 2]
def baseStart_2834979 : Nat := 118140960795 + 2834979 * 2 ^ 59
def prefixEnd_2834979 : Nat := 4983230072969 + 3 ^ 40 * 2834979 * 2
def baseEnd_2834979 : Nat := 1455706872402768865324675

theorem tailTrace_2834979 : CollatzResearch.WordTrace tailWord_2834979 prefixEnd_2834979 1455706872402768865324675 := by
  unfold tailWord_2834979
  simp only [CollatzResearch.WordTrace]
  refine ⟨103400178796362733711099991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68933452530908489140733327 103400178796362733711099991)
  ·
    refine ⟨155100268194544100566649987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103400178796362733711099991 155100268194544100566649987)
    ·
      refine ⟨232650402291816150849974981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155100268194544100566649987 232650402291816150849974981)
      ·
        refine ⟨43621950429715528284370309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232650402291816150849974981 43621950429715528284370309)
        ·
          refine ⟨8179115705571661553319433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43621950429715528284370309 8179115705571661553319433)
          ·
            refine ⟨6134336779178746164989575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8179115705571661553319433 6134336779178746164989575)
            ·
              refine ⟨9201505168768119247484363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134336779178746164989575 9201505168768119247484363)
              ·
                refine ⟨13802257753152178871226545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201505168768119247484363 13802257753152178871226545)
                ·
                  refine ⟨10351693314864134153419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13802257753152178871226545 10351693314864134153419909)
                  ·
                    refine ⟨1940942496537025153766233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10351693314864134153419909 1940942496537025153766233)
                    ·
                      refine ⟨1455706872402768865324675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1940942496537025153766233 1455706872402768865324675)
                      ·
                        rfl

theorem cell23_2834979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_2834979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834979 prefixEnd_2834979 := by exact prefixLift 2834979
  have htrace : WordTrace (prefixWord ++ tailWord_2834979) baseStart_2834979 baseEnd_2834979 := by
    simpa [prefixWord, tailWord_2834979, baseEnd_2834979] using wordTrace_append hprefix tailTrace_2834979
  have hstable : (prefixWord ++ tailWord_2834979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834979).length < 2 ^ (prefixWord ++ tailWord_2834979).sum := by decide
  have hdescent : baseEnd_2834979 < baseStart_2834979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834996 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2834996 : Nat := 118140960795 + 2834996 * 2 ^ 59
def prefixEnd_2834996 : Nat := 4983230072969 + 3 ^ 40 * 2834996 * 2
def baseEnd_2834996 : Nat := 1455715601573895298812097

theorem tailTrace_2834996 : CollatzResearch.WordTrace tailWord_2834996 prefixEnd_2834996 1455715601573895298812097 := by
  unfold tailWord_2834996
  simp only [CollatzResearch.WordTrace]
  refine ⟨51700399418650572807234421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68933865891534097076312561 51700399418650572807234421)
  ·
    refine ⟨4846912445498491200678227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51700399418650572807234421 4846912445498491200678227)
    ·
      refine ⟨7270368668247736801017341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846912445498491200678227 7270368668247736801017341)
      ·
        refine ⟨2726388250592901300381503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7270368668247736801017341 2726388250592901300381503)
        ·
          refine ⟨4089582375889351950572255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726388250592901300381503 4089582375889351950572255)
          ·
            refine ⟨6134373563834027925858383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089582375889351950572255 6134373563834027925858383)
            ·
              refine ⟨9201560345751041888787575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134373563834027925858383 9201560345751041888787575)
              ·
                refine ⟨13802340518626562833181363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201560345751041888787575 13802340518626562833181363)
                ·
                  refine ⟨20703510777939844249772045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802340518626562833181363 20703510777939844249772045)
                  ·
                    refine ⟨7763816541727441593664517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20703510777939844249772045 7763816541727441593664517)
                    ·
                      refine ⟨1455715601573895298812097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7763816541727441593664517 1455715601573895298812097)
                      ·
                        rfl

theorem cell23_2834996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2834996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2834996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2834996 prefixEnd_2834996 := by exact prefixLift 2834996
  have htrace : WordTrace (prefixWord ++ tailWord_2834996) baseStart_2834996 baseEnd_2834996 := by
    simpa [prefixWord, tailWord_2834996, baseEnd_2834996] using wordTrace_append hprefix tailTrace_2834996
  have hstable : (prefixWord ++ tailWord_2834996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834996).length < 2 ^ (prefixWord ++ tailWord_2834996).sum := by decide
  have hdescent : baseEnd_2834996 < baseStart_2834996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835029 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2835029 : Nat := 118140960795 + 2835029 * 2 ^ 59
def prefixEnd_2835029 : Nat := 4983230072969 + 3 ^ 40 * 2835029 * 2
def baseEnd_2835029 : Nat := 1455732546435493669699445

theorem tailTrace_2835029 : CollatzResearch.WordTrace tailWord_2835029 prefixEnd_2835029 1455732546435493669699445 := by
  unfold tailWord_2835029
  simp only [CollatzResearch.WordTrace]
  refine ⟨103402002446181592250420141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68934668297454394833613427 103402002446181592250420141)
  ·
    refine ⟨38775750917318097093907553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103402002446181592250420141 38775750917318097093907553)
    ·
      refine ⟨29081813187988572820430665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38775750917318097093907553 29081813187988572820430665)
      ·
        refine ⟨21811359890991429615322999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29081813187988572820430665 21811359890991429615322999)
        ·
          refine ⟨32717039836487144422984499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21811359890991429615322999 32717039836487144422984499)
          ·
            refine ⟨49075559754730716634476749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32717039836487144422984499 49075559754730716634476749)
            ·
              refine ⟨18403334908024018737928781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49075559754730716634476749 18403334908024018737928781)
              ·
                refine ⟨6901250590509007026723293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18403334908024018737928781 6901250590509007026723293)
                ·
                  refine ⟨2587968971440877635021235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6901250590509007026723293 2587968971440877635021235)
                  ·
                    refine ⟨3881953457161316452531853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2587968971440877635021235 3881953457161316452531853)
                    ·
                      refine ⟨1455732546435493669699445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3881953457161316452531853 1455732546435493669699445)
                      ·
                        rfl

theorem cell23_2835029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2835029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835029 prefixEnd_2835029 := by exact prefixLift 2835029
  have htrace : WordTrace (prefixWord ++ tailWord_2835029) baseStart_2835029 baseEnd_2835029 := by
    simpa [prefixWord, tailWord_2835029, baseEnd_2835029] using wordTrace_append hprefix tailTrace_2835029
  have hstable : (prefixWord ++ tailWord_2835029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835029).length < 2 ^ (prefixWord ++ tailWord_2835029).sum := by decide
  have hdescent : baseEnd_2835029 < baseStart_2835029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835036 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 6]
def baseStart_2835036 : Nat := 118140960795 + 2835036 * 2 ^ 59
def prefixEnd_2835036 : Nat := 4983230072969 + 3 ^ 40 * 2835036 * 2
def baseEnd_2835036 : Nat := 161748460088897238034657

theorem tailTrace_2835036 : CollatzResearch.WordTrace tailWord_2835036 prefixEnd_2835036 161748460088897238034657 := by
  unfold tailWord_2835036
  simp only [CollatzResearch.WordTrace]
  refine ⟨51701128878578116222962481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68934838504770821630616641 51701128878578116222962481)
  ·
    refine ⟨38775846658933587167221861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51701128878578116222962481 38775846658933587167221861)
    ·
      refine ⟨7270471248550047593854099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38775846658933587167221861 7270471248550047593854099)
      ·
        refine ⟨10905706872825071390781149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7270471248550047593854099 10905706872825071390781149)
        ·
          refine ⟨4089640077309401771542931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10905706872825071390781149 4089640077309401771542931)
          ·
            refine ⟨6134460115964102657314397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089640077309401771542931 6134460115964102657314397)
            ·
              refine ⟨2300422543486538496492899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6134460115964102657314397 2300422543486538496492899)
              ·
                refine ⟨3450633815229807744739349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300422543486538496492899 3450633815229807744739349)
                ·
                  refine ⟨161748460088897238034657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3450633815229807744739349 161748460088897238034657)
                  ·
                    rfl

theorem cell23_2835036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_2835036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835036 prefixEnd_2835036 := by exact prefixLift 2835036
  have htrace : WordTrace (prefixWord ++ tailWord_2835036) baseStart_2835036 baseEnd_2835036 := by
    simpa [prefixWord, tailWord_2835036, baseEnd_2835036] using wordTrace_append hprefix tailTrace_2835036
  have hstable : (prefixWord ++ tailWord_2835036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835036).length < 2 ^ (prefixWord ++ tailWord_2835036).sum := by decide
  have hdescent : baseEnd_2835036 < baseStart_2835036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835052 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2835052 : Nat := 118140960795 + 2835052 * 2 ^ 59
def prefixEnd_2835052 : Nat := 4983230072969 + 3 ^ 40 * 2835052 * 2
def baseEnd_2835052 : Nat := 1455744356490547079711839

theorem tailTrace_2835052 : CollatzResearch.WordTrace tailWord_2835052 prefixEnd_2835052 1455744356490547079711839 := by
  unfold tailWord_2835052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51701420662549133589253705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68935227550065511452338273 51701420662549133589253705)
  ·
    refine ⟨38776065496911850191940279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51701420662549133589253705 38776065496911850191940279)
    ·
      refine ⟨58164098245367775287910419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38776065496911850191940279 58164098245367775287910419)
      ·
        refine ⟨87246147368051662931865629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58164098245367775287910419 87246147368051662931865629)
        ·
          refine ⟨32717305263019373599449611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87246147368051662931865629 32717305263019373599449611)
          ·
            refine ⟨49075957894529060399174417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32717305263019373599449611 49075957894529060399174417)
            ·
              refine ⟨36806968420896795299380813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49075957894529060399174417 36806968420896795299380813)
              ·
                refine ⟨13802613157836298237267805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36806968420896795299380813 13802613157836298237267805)
                ·
                  refine ⟨5175979934188611838975427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13802613157836298237267805 5175979934188611838975427)
                  ·
                    refine ⟨7763969901282917758463141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5175979934188611838975427 7763969901282917758463141)
                    ·
                      refine ⟨1455744356490547079711839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7763969901282917758463141 1455744356490547079711839)
                      ·
                        rfl

theorem cell23_2835052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2835052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835052 prefixEnd_2835052 := by exact prefixLift 2835052
  have htrace : WordTrace (prefixWord ++ tailWord_2835052) baseStart_2835052 baseEnd_2835052 := by
    simpa [prefixWord, tailWord_2835052, baseEnd_2835052] using wordTrace_append hprefix tailTrace_2835052
  have hstable : (prefixWord ++ tailWord_2835052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835052).length < 2 ^ (prefixWord ++ tailWord_2835052).sum := by decide
  have hdescent : baseEnd_2835052 < baseStart_2835052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835072 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_2835072 : Nat := 118140960795 + 2835072 * 2 ^ 59
def prefixEnd_2835072 : Nat := 4983230072969 + 3 ^ 40 * 2835072 * 2
def baseEnd_2835072 : Nat := 1455754626103637001461747

theorem tailTrace_2835072 : CollatzResearch.WordTrace tailWord_2835072 prefixEnd_2835072 1455754626103637001461747 := by
  unfold tailWord_2835072
  simp only [CollatzResearch.WordTrace]
  refine ⟨51701785392512905297117735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68935713856683873729490313 51701785392512905297117735)
  ·
    refine ⟨77552678088769357945676603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51701785392512905297117735 77552678088769357945676603)
    ·
      refine ⟨116329017133154036918514905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77552678088769357945676603 116329017133154036918514905)
      ·
        refine ⟨87246762849865527688886179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116329017133154036918514905 87246762849865527688886179)
        ·
          refine ⟨130870144274798291533329269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87246762849865527688886179 130870144274798291533329269)
          ·
            refine ⟨12269076025762339831249619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130870144274798291533329269 12269076025762339831249619)
            ·
              refine ⟨18403614038643509746874429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269076025762339831249619 18403614038643509746874429)
              ·
                refine ⟨6901355264491316155077911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18403614038643509746874429 6901355264491316155077911)
                ·
                  refine ⟨10352032896736974232616867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901355264491316155077911 10352032896736974232616867)
                  ·
                    refine ⟨15528049345105461348925301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10352032896736974232616867 15528049345105461348925301)
                    ·
                      refine ⟨1455754626103637001461747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15528049345105461348925301 1455754626103637001461747)
                      ·
                        rfl

theorem cell23_2835072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_2835072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835072 prefixEnd_2835072 := by exact prefixLift 2835072
  have htrace : WordTrace (prefixWord ++ tailWord_2835072) baseStart_2835072 baseEnd_2835072 := by
    simpa [prefixWord, tailWord_2835072, baseEnd_2835072] using wordTrace_append hprefix tailTrace_2835072
  have hstable : (prefixWord ++ tailWord_2835072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835072).length < 2 ^ (prefixWord ++ tailWord_2835072).sum := by decide
  have hdescent : baseEnd_2835072 < baseStart_2835072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835074 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2835074 : Nat := 118140960795 + 2835074 * 2 ^ 59
def prefixEnd_2835074 : Nat := 4983230072969 + 3 ^ 40 * 2835074 * 2
def baseEnd_2835074 : Nat := 485251884354981997878913

theorem tailTrace_2835074 : CollatzResearch.WordTrace tailWord_2835074 prefixEnd_2835074 485251884354981997878913 := by
  unfold tailWord_2835074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25850910932754641233952069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68935762487345709957205517 25850910932754641233952069)
  ·
    refine ⟨4847045799891495231366013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25850910932754641233952069 4847045799891495231366013)
    ·
      refine ⟨1817642174959310711762255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4847045799891495231366013 1817642174959310711762255)
      ·
        refine ⟨2726463262438966067643383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817642174959310711762255 2726463262438966067643383)
        ·
          refine ⟨4089694893658449101465075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726463262438966067643383 4089694893658449101465075)
          ·
            refine ⟨6134542340487673652197613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089694893658449101465075 6134542340487673652197613)
            ·
              refine ⟨2300453377682877619574105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6134542340487673652197613 2300453377682877619574105)
              ·
                refine ⟨1725340033262158214680579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300453377682877619574105 1725340033262158214680579)
                ·
                  refine ⟨2588010049893237322020869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725340033262158214680579 2588010049893237322020869)
                  ·
                    refine ⟨485251884354981997878913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2588010049893237322020869 485251884354981997878913)
                    ·
                      rfl

theorem cell23_2835074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2835074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835074 prefixEnd_2835074 := by exact prefixLift 2835074
  have htrace : WordTrace (prefixWord ++ tailWord_2835074) baseStart_2835074 baseEnd_2835074 := by
    simpa [prefixWord, tailWord_2835074, baseEnd_2835074] using wordTrace_append hprefix tailTrace_2835074
  have hstable : (prefixWord ++ tailWord_2835074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835074).length < 2 ^ (prefixWord ++ tailWord_2835074).sum := by decide
  have hdescent : baseEnd_2835074 < baseStart_2835074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835075 : List Nat := [1, 1, 1, 3, 3, 1, 13]
def baseStart_2835075 : Nat := 118140960795 + 2835075 * 2 ^ 59
def prefixEnd_2835075 : Nat := 4983230072969 + 3 ^ 40 * 2835075 * 2
def baseEnd_2835075 : Nat := 17972298352414820860793

theorem tailTrace_2835075 : CollatzResearch.WordTrace tailWord_2835075 prefixEnd_2835075 17972298352414820860793 := by
  unfold tailWord_2835075
  simp only [CollatzResearch.WordTrace]
  refine ⟨103403680204014942106594679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68935786802676628071063119 103403680204014942106594679)
  ·
    refine ⟨155105520306022413159892019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103403680204014942106594679 155105520306022413159892019)
    ·
      refine ⟨232658280459033619739838029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155105520306022413159892019 232658280459033619739838029)
      ·
        refine ⟨87246855172137607402439261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232658280459033619739838029 87246855172137607402439261)
        ·
          refine ⟨32717570689551602775914723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87246855172137607402439261 32717570689551602775914723)
          ·
            refine ⟨49076356034327404163872085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32717570689551602775914723 49076356034327404163872085)
            ·
              refine ⟨17972298352414820860793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 49076356034327404163872085 17972298352414820860793)
              ·
                rfl

theorem cell23_2835075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 13].length) (baseStart_2835075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835075 prefixEnd_2835075 := by exact prefixLift 2835075
  have htrace : WordTrace (prefixWord ++ tailWord_2835075) baseStart_2835075 baseEnd_2835075 := by
    simpa [prefixWord, tailWord_2835075, baseEnd_2835075] using wordTrace_append hprefix tailTrace_2835075
  have hstable : (prefixWord ++ tailWord_2835075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835075).length < 2 ^ (prefixWord ++ tailWord_2835075).sum := by decide
  have hdescent : baseEnd_2835075 < baseStart_2835075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835079 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 2, 4]
def baseStart_2835079 : Nat := 118140960795 + 2835079 * 2 ^ 59
def prefixEnd_2835079 : Nat := 4983230072969 + 3 ^ 40 * 2835079 * 2
def baseEnd_2835079 : Nat := 485252740156072824691405

theorem tailTrace_2835079 : CollatzResearch.WordTrace tailWord_2835079 prefixEnd_2835079 485252740156072824691405 := by
  unfold tailWord_2835079
  simp only [CollatzResearch.WordTrace]
  refine ⟨103403826096000450789740291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68935884064000300526493527 103403826096000450789740291)
  ·
    refine ⟨155105739144000676184610437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103403826096000450789740291 155105739144000676184610437)
    ·
      refine ⟨29082326089500126784614457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155105739144000676184610437 29082326089500126784614457)
      ·
        refine ⟨21811744567125095088460843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29082326089500126784614457 21811744567125095088460843)
        ·
          refine ⟨32717616850687642632691265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21811744567125095088460843 32717616850687642632691265)
          ·
            refine ⟨24538212638015731974518449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32717616850687642632691265 24538212638015731974518449)
            ·
              refine ⟨18403659478511798980888837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24538212638015731974518449 18403659478511798980888837)
              ·
                refine ⟨3450686152220962308916657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18403659478511798980888837 3450686152220962308916657)
                ·
                  refine ⟨2588014614165721731687493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450686152220962308916657 2588014614165721731687493)
                  ·
                    refine ⟨485252740156072824691405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2588014614165721731687493 485252740156072824691405)
                    ·
                      rfl

theorem cell23_2835079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_2835079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835079 prefixEnd_2835079 := by exact prefixLift 2835079
  have htrace : WordTrace (prefixWord ++ tailWord_2835079) baseStart_2835079 baseEnd_2835079 := by
    simpa [prefixWord, tailWord_2835079, baseEnd_2835079] using wordTrace_append hprefix tailTrace_2835079
  have hstable : (prefixWord ++ tailWord_2835079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835079).length < 2 ^ (prefixWord ++ tailWord_2835079).sum := by decide
  have hdescent : baseEnd_2835079 < baseStart_2835079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835119 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_2835119 : Nat := 118140960795 + 2835119 * 2 ^ 59
def prefixEnd_2835119 : Nat := 4983230072969 + 3 ^ 40 * 2835119 * 2
def baseEnd_2835119 : Nat := 1455778759694398317574031

theorem tailTrace_2835119 : CollatzResearch.WordTrace tailWord_2835119 prefixEnd_2835119 1455778759694398317574031 := by
  unfold tailWord_2835119
  simp only [CollatzResearch.WordTrace]
  refine ⟨103405285015855537621196411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68936856677237025080797607 103405285015855537621196411)
  ·
    refine ⟨155107927523783306431794617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103405285015855537621196411 155107927523783306431794617)
    ·
      refine ⟨116330945642837479823845963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155107927523783306431794617 116330945642837479823845963)
      ·
        refine ⟨174496418464256219735768945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116330945642837479823845963 174496418464256219735768945)
        ·
          refine ⟨130872313848192164801826709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174496418464256219735768945 130872313848192164801826709)
          ·
            refine ⟨6134639711634007725085627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130872313848192164801826709 6134639711634007725085627)
            ·
              refine ⟨9201959567451011587628441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134639711634007725085627 9201959567451011587628441)
              ·
                refine ⟨6901469675588258690721331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9201959567451011587628441 6901469675588258690721331)
                ·
                  refine ⟨10352204513382388036081997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901469675588258690721331 10352204513382388036081997)
                  ·
                    refine ⟨3882076692518395513530749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10352204513382388036081997 3882076692518395513530749)
                    ·
                      refine ⟨1455778759694398317574031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882076692518395513530749 1455778759694398317574031)
                      ·
                        rfl

theorem cell23_2835119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_2835119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835119 prefixEnd_2835119 := by exact prefixLift 2835119
  have htrace : WordTrace (prefixWord ++ tailWord_2835119) baseStart_2835119 baseEnd_2835119 := by
    simpa [prefixWord, tailWord_2835119, baseEnd_2835119] using wordTrace_append hprefix tailTrace_2835119
  have hstable : (prefixWord ++ tailWord_2835119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835119).length < 2 ^ (prefixWord ++ tailWord_2835119).sum := by decide
  have hdescent : baseEnd_2835119 < baseStart_2835119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835126 : List Nat := [5, 1, 3, 1, 3, 10]
def baseStart_2835126 : Nat := 118140960795 + 2835126 * 2 ^ 59
def prefixEnd_2835126 : Nat := 4983230072969 + 3 ^ 40 * 2835126 * 2
def baseEnd_2835126 : Nat := 5990873885016377737393

theorem tailTrace_2835126 : CollatzResearch.WordTrace tailWord_2835126 prefixEnd_2835126 5990873885016377737393 := by
  unfold tailWord_2835126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462846270426886113543827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68937026884553451877800821 6462846270426886113543827)
  ·
    refine ⟨9694269405640329170315741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462846270426886113543827 9694269405640329170315741)
    ·
      refine ⟨3635351027115123438868403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9694269405640329170315741 3635351027115123438868403)
      ·
        refine ⟨5453026540672685158302605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635351027115123438868403 5453026540672685158302605)
        ·
          refine ⟨2044884952752256934363477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5453026540672685158302605 2044884952752256934363477)
          ·
            refine ⟨5990873885016377737393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2044884952752256934363477 5990873885016377737393)
            ·
              rfl

theorem cell23_2835126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 10].length) (baseStart_2835126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835126 prefixEnd_2835126 := by exact prefixLift 2835126
  have htrace : WordTrace (prefixWord ++ tailWord_2835126) baseStart_2835126 baseEnd_2835126 := by
    simpa [prefixWord, tailWord_2835126, baseEnd_2835126] using wordTrace_append hprefix tailTrace_2835126
  have hstable : (prefixWord ++ tailWord_2835126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835126).length < 2 ^ (prefixWord ++ tailWord_2835126).sum := by decide
  have hdescent : baseEnd_2835126 < baseStart_2835126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835136 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_2835136 : Nat := 118140960795 + 2835136 * 2 ^ 59
def prefixEnd_2835136 : Nat := 4983230072969 + 3 ^ 40 * 2835136 * 2
def baseEnd_2835136 : Nat := 1455787488865524751061453

theorem tailTrace_2835136 : CollatzResearch.WordTrace tailWord_2835136 prefixEnd_2835136 1455787488865524751061453 := by
  unfold tailWord_2835136
  simp only [CollatzResearch.WordTrace]
  refine ⟨51702952528396974762282631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68937270037862633016376841 51702952528396974762282631)
  ·
    refine ⟨77554428792595462143423947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51702952528396974762282631 77554428792595462143423947)
    ·
      refine ⟨116331643188893193215135921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77554428792595462143423947 116331643188893193215135921)
      ·
        refine ⟨87248732391669894911351941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116331643188893193215135921 87248732391669894911351941)
        ·
          refine ⟨16359137323438105295878489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87248732391669894911351941 16359137323438105295878489)
          ·
            refine ⟨12269352992578578971908867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16359137323438105295878489 12269352992578578971908867)
            ·
              refine ⟨18404029488867868457863301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269352992578578971908867 18404029488867868457863301)
              ·
                refine ⟨3450755529162725335849369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18404029488867868457863301 3450755529162725335849369)
                ·
                  refine ⟨2588066646872044001887027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450755529162725335849369 2588066646872044001887027)
                  ·
                    refine ⟨3882099970308066002830541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588066646872044001887027 3882099970308066002830541)
                    ·
                      refine ⟨1455787488865524751061453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882099970308066002830541 1455787488865524751061453)
                      ·
                        rfl

theorem cell23_2835136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_2835136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835136 prefixEnd_2835136 := by exact prefixLift 2835136
  have htrace : WordTrace (prefixWord ++ tailWord_2835136) baseStart_2835136 baseEnd_2835136 := by
    simpa [prefixWord, tailWord_2835136, baseEnd_2835136] using wordTrace_append hprefix tailTrace_2835136
  have hstable : (prefixWord ++ tailWord_2835136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835136).length < 2 ^ (prefixWord ++ tailWord_2835136).sum := by decide
  have hdescent : baseEnd_2835136 < baseStart_2835136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835146 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_2835146 : Nat := 118140960795 + 2835146 * 2 ^ 59
def prefixEnd_2835146 : Nat := 4983230072969 + 3 ^ 40 * 2835146 * 2
def baseEnd_2835146 : Nat := 1455792623672069711936407

theorem tailTrace_2835146 : CollatzResearch.WordTrace tailWord_2835146 prefixEnd_2835146 1455792623672069711936407 := by
  unfold tailWord_2835146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25851567446689430308107323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68937513191171814154952861 25851567446689430308107323)
  ·
    refine ⟨38777351170034145462160985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25851567446689430308107323 38777351170034145462160985)
    ·
      refine ⟨29083013377525609096620739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38777351170034145462160985 29083013377525609096620739)
      ·
        refine ⟨43624520066288413644931109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29083013377525609096620739 43624520066288413644931109)
        ·
          refine ⟨8179597512429077558424583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43624520066288413644931109 8179597512429077558424583)
          ·
            refine ⟨12269396268643616337636875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179597512429077558424583 12269396268643616337636875)
            ·
              refine ⟨18404094402965424506455313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269396268643616337636875 18404094402965424506455313)
              ·
                refine ⟨13803070802224068379841485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18404094402965424506455313 13803070802224068379841485)
                ·
                  refine ⟨5176151550834025642440557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13803070802224068379841485 5176151550834025642440557)
                  ·
                    refine ⟨1941056831562759615915209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5176151550834025642440557 1941056831562759615915209)
                    ·
                      refine ⟨1455792623672069711936407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941056831562759615915209 1455792623672069711936407)
                      ·
                        rfl

theorem cell23_2835146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_2835146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835146 prefixEnd_2835146 := by exact prefixLift 2835146
  have htrace : WordTrace (prefixWord ++ tailWord_2835146) baseStart_2835146 baseEnd_2835146 := by
    simpa [prefixWord, tailWord_2835146, baseEnd_2835146] using wordTrace_append hprefix tailTrace_2835146
  have hstable : (prefixWord ++ tailWord_2835146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835146).length < 2 ^ (prefixWord ++ tailWord_2835146).sum := by decide
  have hdescent : baseEnd_2835146 < baseStart_2835146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835209 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_2835209 : Nat := 118140960795 + 2835209 * 2 ^ 59
def prefixEnd_2835209 : Nat := 4983230072969 + 3 ^ 40 * 2835209 * 2
def baseEnd_2835209 : Nat := 1455824972953302965448617

theorem tailTrace_2835209 : CollatzResearch.WordTrace tailWord_2835209 prefixEnd_2835209 1455824972953302965448617 := by
  unfold tailWord_2835209
  simp only [CollatzResearch.WordTrace]
  refine ⟨103408567585529482991972681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68939045057019655327981787 103408567585529482991972681)
  ·
    refine ⟨77556425689147112243979511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103408567585529482991972681 77556425689147112243979511)
    ·
      refine ⟨116334638533720668365969267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77556425689147112243979511 116334638533720668365969267)
      ·
        refine ⟨174501957800581002548953901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116334638533720668365969267 174501957800581002548953901)
        ·
          refine ⟨65438234175217875955857713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174501957800581002548953901 65438234175217875955857713)
          ·
            refine ⟨49078675631413406966893285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65438234175217875955857713 49078675631413406966893285)
            ·
              refine ⟨9202251680890013806292491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49078675631413406966893285 9202251680890013806292491)
              ·
                refine ⟨13803377521335020709438737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9202251680890013806292491 13803377521335020709438737)
                ·
                  refine ⟨10352533141001265532079053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13803377521335020709438737 10352533141001265532079053)
                  ·
                    refine ⟨3882199927875474574529645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10352533141001265532079053 3882199927875474574529645)
                    ·
                      refine ⟨1455824972953302965448617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882199927875474574529645 1455824972953302965448617)
                      ·
                        rfl

theorem cell23_2835209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_2835209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835209 prefixEnd_2835209 := by exact prefixLift 2835209
  have htrace : WordTrace (prefixWord ++ tailWord_2835209) baseStart_2835209 baseEnd_2835209 := by
    simpa [prefixWord, tailWord_2835209, baseEnd_2835209] using wordTrace_append hprefix tailTrace_2835209
  have hstable : (prefixWord ++ tailWord_2835209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835209).length < 2 ^ (prefixWord ++ tailWord_2835209).sum := by decide
  have hdescent : baseEnd_2835209 < baseStart_2835209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835210 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_2835210 : Nat := 118140960795 + 2835210 * 2 ^ 59
def prefixEnd_2835210 : Nat := 4983230072969 + 3 ^ 40 * 2835210 * 2
def baseEnd_2835210 : Nat := 1455825486433957461536113

theorem tailTrace_2835210 : CollatzResearch.WordTrace tailWord_2835210 prefixEnd_2835210 1455825486433957461536113 := by
  unfold tailWord_2835210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25852151014631465040689771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68939069372350573441839389 25852151014631465040689771)
  ·
    refine ⟨38778226521947197561034657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25852151014631465040689771 38778226521947197561034657)
    ·
      refine ⟨29083669891460398170775993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38778226521947197561034657 29083669891460398170775993)
      ·
        refine ⟨21812752418595298628081995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29083669891460398170775993 21812752418595298628081995)
        ·
          refine ⟨32719128627892947942122993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21812752418595298628081995 32719128627892947942122993)
          ·
            refine ⟨24539346470919710956592245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32719128627892947942122993 24539346470919710956592245)
            ·
              refine ⟨2300563731648722902180523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24539346470919710956592245 2300563731648722902180523)
              ·
                refine ⟨3450845597473084353270785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300563731648722902180523 3450845597473084353270785)
                ·
                  refine ⟨2588134198104813264953089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450845597473084353270785 2588134198104813264953089)
                  ·
                    refine ⟨1941100648578609948714817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588134198104813264953089 1941100648578609948714817)
                    ·
                      refine ⟨1455825486433957461536113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941100648578609948714817 1455825486433957461536113)
                      ·
                        rfl

theorem cell23_2835210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_2835210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835210 prefixEnd_2835210 := by exact prefixLift 2835210
  have htrace : WordTrace (prefixWord ++ tailWord_2835210) baseStart_2835210 baseEnd_2835210 := by
    simpa [prefixWord, tailWord_2835210, baseEnd_2835210] using wordTrace_append hprefix tailTrace_2835210
  have hstable : (prefixWord ++ tailWord_2835210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835210).length < 2 ^ (prefixWord ++ tailWord_2835210).sum := by decide
  have hdescent : baseEnd_2835210 < baseStart_2835210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835246 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2835246 : Nat := 118140960795 + 2835246 * 2 ^ 59
def prefixEnd_2835246 : Nat := 4983230072969 + 3 ^ 40 * 2835246 * 2
def baseEnd_2835246 : Nat := 485281323912506440228649

theorem tailTrace_2835246 : CollatzResearch.WordTrace tailWord_2835246 prefixEnd_2835246 485281323912506440228649 := by
  unfold tailWord_2835246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12926239635799429788883699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68939944724263625540713061 12926239635799429788883699)
  ·
    refine ⟨19389359453699144683325549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12926239635799429788883699 19389359453699144683325549)
    ·
      refine ⟨7271009795137179256247081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19389359453699144683325549 7271009795137179256247081)
      ·
        refine ⟨5453257346352884442185311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7271009795137179256247081 5453257346352884442185311)
        ·
          refine ⟨8179886019529326663277967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453257346352884442185311 8179886019529326663277967)
          ·
            refine ⟨12269829029293989994916951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179886019529326663277967 12269829029293989994916951)
            ·
              refine ⟨18404743543940984992375427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269829029293989994916951 18404743543940984992375427)
              ·
                refine ⟨27607115315911477488563141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18404743543940984992375427 27607115315911477488563141)
                ·
                  refine ⟨5176334121733402029105589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27607115315911477488563141 5176334121733402029105589)
                  ·
                    refine ⟨485281323912506440228649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5176334121733402029105589 485281323912506440228649)
                    ·
                      rfl

theorem cell23_2835246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2835246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835246 prefixEnd_2835246 := by exact prefixLift 2835246
  have htrace : WordTrace (prefixWord ++ tailWord_2835246) baseStart_2835246 baseEnd_2835246 := by
    simpa [prefixWord, tailWord_2835246, baseEnd_2835246] using wordTrace_append hprefix tailTrace_2835246
  have hstable : (prefixWord ++ tailWord_2835246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835246).length < 2 ^ (prefixWord ++ tailWord_2835246).sum := by decide
  have hdescent : baseEnd_2835246 < baseStart_2835246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835269 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_2835269 : Nat := 118140960795 + 2835269 * 2 ^ 59
def prefixEnd_2835269 : Nat := 4983230072969 + 3 ^ 40 * 2835269 * 2
def baseEnd_2835269 : Nat := 1455855781792572730698341

theorem tailTrace_2835269 : CollatzResearch.WordTrace tailWord_2835269 prefixEnd_2835269 1455855781792572730698341 := by
  unfold tailWord_2835269
  simp only [CollatzResearch.WordTrace]
  refine ⟨103410755965312113239156861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68940503976874742159437907 103410755965312113239156861)
  ·
    refine ⟨38779033486992042464683823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103410755965312113239156861 38779033486992042464683823)
    ·
      refine ⟨58168550230488063697025735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38779033486992042464683823 58168550230488063697025735)
      ·
        refine ⟨87252825345732095545538603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58168550230488063697025735 87252825345732095545538603)
        ·
          refine ⟨130879238018598143318307905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87252825345732095545538603 130879238018598143318307905)
          ·
            refine ⟨98159428513948607488730929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130879238018598143318307905 98159428513948607488730929)
            ·
              refine ⟨73619571385461455616548197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98159428513948607488730929 73619571385461455616548197)
              ·
                refine ⟨13803669634774022928102787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73619571385461455616548197 13803669634774022928102787)
                ·
                  refine ⟨20705504452161034392154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13803669634774022928102787 20705504452161034392154181)
                  ·
                    refine ⟨3882282084780193948528909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20705504452161034392154181 3882282084780193948528909)
                    ·
                      refine ⟨1455855781792572730698341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882282084780193948528909 1455855781792572730698341)
                      ·
                        rfl

theorem cell23_2835269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_2835269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835269 prefixEnd_2835269 := by exact prefixLift 2835269
  have htrace : WordTrace (prefixWord ++ tailWord_2835269) baseStart_2835269 baseEnd_2835269 := by
    simpa [prefixWord, tailWord_2835269, baseEnd_2835269] using wordTrace_append hprefix tailTrace_2835269
  have hstable : (prefixWord ++ tailWord_2835269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835269).length < 2 ^ (prefixWord ++ tailWord_2835269).sum := by decide
  have hdescent : baseEnd_2835269 < baseStart_2835269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835309 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2835309 : Nat := 118140960795 + 2835309 * 2 ^ 59
def prefixEnd_2835309 : Nat := 4983230072969 + 3 ^ 40 * 2835309 * 2
def baseEnd_2835309 : Nat := 1455876321018752574198157

theorem tailTrace_2835309 : CollatzResearch.WordTrace tailWord_2835309 prefixEnd_2835309 1455876321018752574198157 := by
  unfold tailWord_2835309
  simp only [CollatzResearch.WordTrace]
  refine ⟨103412214885167200070612981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68941476590111466713741987 103412214885167200070612981)
  ·
    refine ⟨9694895145484425006619967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103412214885167200070612981 9694895145484425006619967)
    ·
      refine ⟨14542342718226637509929951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694895145484425006619967 14542342718226637509929951)
      ·
        refine ⟨21813514077339956264894927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14542342718226637509929951 21813514077339956264894927)
        ·
          refine ⟨32720271116009934397342391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21813514077339956264894927 32720271116009934397342391)
          ·
            refine ⟨49080406674014901596013587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32720271116009934397342391 49080406674014901596013587)
            ·
              refine ⟨73620610011022352394020381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49080406674014901596013587 73620610011022352394020381)
              ·
                refine ⟨27607728754133382147757643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73620610011022352394020381 27607728754133382147757643)
                ·
                  refine ⟨41411593131200073221636465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27607728754133382147757643 41411593131200073221636465)
                  ·
                    refine ⟨31058694848400054916227349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41411593131200073221636465 31058694848400054916227349)
                    ·
                      refine ⟨1455876321018752574198157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31058694848400054916227349 1455876321018752574198157)
                      ·
                        rfl

theorem cell23_2835309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2835309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835309 prefixEnd_2835309 := by exact prefixLift 2835309
  have htrace : WordTrace (prefixWord ++ tailWord_2835309) baseStart_2835309 baseEnd_2835309 := by
    simpa [prefixWord, tailWord_2835309, baseEnd_2835309] using wordTrace_append hprefix tailTrace_2835309
  have hstable : (prefixWord ++ tailWord_2835309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835309).length < 2 ^ (prefixWord ++ tailWord_2835309).sum := by decide
  have hdescent : baseEnd_2835309 < baseStart_2835309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835333 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_2835333 : Nat := 118140960795 + 2835333 * 2 ^ 59
def prefixEnd_2835333 : Nat := 4983230072969 + 3 ^ 40 * 2835333 * 2
def baseEnd_2835333 : Nat := 1455888644554460480298047

theorem tailTrace_2835333 : CollatzResearch.WordTrace tailWord_2835333 prefixEnd_2835333 1455888644554460480298047 := by
  unfold tailWord_2835333
  simp only [CollatzResearch.WordTrace]
  refine ⟨103413090237080252169486653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68942060158053501446324435 103413090237080252169486653)
  ·
    refine ⟨38779908838905094563557495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103413090237080252169486653 38779908838905094563557495)
    ·
      refine ⟨58169863258357641845336243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38779908838905094563557495 58169863258357641845336243)
      ·
        refine ⟨87254794887536462768004365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58169863258357641845336243 87254794887536462768004365)
        ·
          refine ⟨32720548082826173538001637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87254794887536462768004365 32720548082826173538001637)
          ·
            refine ⟨6135102765529907538375307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32720548082826173538001637 6135102765529907538375307)
            ·
              refine ⟨9202654148294861307562961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135102765529907538375307 9202654148294861307562961)
              ·
                refine ⟨6901990611221145980672221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9202654148294861307562961 6901990611221145980672221)
                ·
                  refine ⟨2588246479207929742752083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6901990611221145980672221 2588246479207929742752083)
                  ·
                    refine ⟨3882369718811894614128125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588246479207929742752083 3882369718811894614128125)
                    ·
                      refine ⟨1455888644554460480298047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882369718811894614128125 1455888644554460480298047)
                      ·
                        rfl

theorem cell23_2835333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_2835333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835333 prefixEnd_2835333 := by exact prefixLift 2835333
  have htrace : WordTrace (prefixWord ++ tailWord_2835333) baseStart_2835333 baseEnd_2835333 := by
    simpa [prefixWord, tailWord_2835333, baseEnd_2835333] using wordTrace_append hprefix tailTrace_2835333
  have hstable : (prefixWord ++ tailWord_2835333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835333).length < 2 ^ (prefixWord ++ tailWord_2835333).sum := by decide
  have hdescent : baseEnd_2835333 < baseStart_2835333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835336 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_2835336 : Nat := 118140960795 + 2835336 * 2 ^ 59
def prefixEnd_2835336 : Nat := 4983230072969 + 3 ^ 40 * 2835336 * 2
def baseEnd_2835336 : Nat := 485296728332141322853511

theorem tailTrace_2835336 : CollatzResearch.WordTrace tailWord_2835336 prefixEnd_2835336 485296728332141322853511 := by
  unfold tailWord_2835336
  simp only [CollatzResearch.WordTrace]
  refine ⟨51706599828034691840922931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68942133104046255787897241 51706599828034691840922931)
  ·
    refine ⟨77559899742052037761384397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51706599828034691840922931 77559899742052037761384397)
    ·
      refine ⟨29084962403269514160519149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77559899742052037761384397 29084962403269514160519149)
      ·
        refine ⟨10906860901226067810194681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29084962403269514160519149 10906860901226067810194681)
        ·
          refine ⟨8180145675919550857646011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10906860901226067810194681 8180145675919550857646011)
          ·
            refine ⟨12270218513879326286469017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180145675919550857646011 12270218513879326286469017)
            ·
              refine ⟨9202663885409494714851763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12270218513879326286469017 9202663885409494714851763)
              ·
                refine ⟨13803995828114242072277645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9202663885409494714851763 13803995828114242072277645)
                ·
                  refine ⟨5176498435542840777104117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13803995828114242072277645 5176498435542840777104117)
                  ·
                    refine ⟨485296728332141322853511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5176498435542840777104117 485296728332141322853511)
                    ·
                      rfl

theorem cell23_2835336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_2835336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835336 prefixEnd_2835336 := by exact prefixLift 2835336
  have htrace : WordTrace (prefixWord ++ tailWord_2835336) baseStart_2835336 baseEnd_2835336 := by
    simpa [prefixWord, tailWord_2835336, baseEnd_2835336] using wordTrace_append hprefix tailTrace_2835336
  have hstable : (prefixWord ++ tailWord_2835336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835336).length < 2 ^ (prefixWord ++ tailWord_2835336).sum := by decide
  have hdescent : baseEnd_2835336 < baseStart_2835336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835369 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_2835369 : Nat := 118140960795 + 2835369 * 2 ^ 59
def prefixEnd_2835369 : Nat := 4983230072969 + 3 ^ 40 * 2835369 * 2
def baseEnd_2835369 : Nat := 1455907129858022339447881

theorem tailTrace_2835369 : CollatzResearch.WordTrace tailWord_2835369 prefixEnd_2835369 1455907129858022339447881 := by
  unfold tailWord_2835369
  simp only [CollatzResearch.WordTrace]
  refine ⟨103414403264949830317797161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68942935509966553545198107 103414403264949830317797161)
  ·
    refine ⟨77560802448712372738347871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103414403264949830317797161 77560802448712372738347871)
    ·
      refine ⟨116341203673068559107521807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77560802448712372738347871 116341203673068559107521807)
      ·
        refine ⟨174511805509602838661282711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116341203673068559107521807 174511805509602838661282711)
        ·
          refine ⟨261767708264404257991924067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174511805509602838661282711 261767708264404257991924067)
          ·
            refine ⟨392651562396606386987886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261767708264404257991924067 392651562396606386987886101)
            ·
              refine ⟨18405541987340924390057161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392651562396606386987886101 18405541987340924390057161)
              ·
                refine ⟨13804156490505693292542871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18405541987340924390057161 13804156490505693292542871)
                ·
                  refine ⟨20706234735758539938814307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13804156490505693292542871 20706234735758539938814307)
                  ·
                    refine ⟨31059352103637809908221461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20706234735758539938814307 31059352103637809908221461)
                    ·
                      refine ⟨1455907129858022339447881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31059352103637809908221461 1455907129858022339447881)
                      ·
                        rfl

theorem cell23_2835369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_2835369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835369 prefixEnd_2835369 := by exact prefixLift 2835369
  have htrace : WordTrace (prefixWord ++ tailWord_2835369) baseStart_2835369 baseEnd_2835369 := by
    simpa [prefixWord, tailWord_2835369, baseEnd_2835369] using wordTrace_append hprefix tailTrace_2835369
  have hstable : (prefixWord ++ tailWord_2835369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835369).length < 2 ^ (prefixWord ++ tailWord_2835369).sum := by decide
  have hdescent : baseEnd_2835369 < baseStart_2835369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835390 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_2835390 : Nat := 118140960795 + 2835390 * 2 ^ 59
def prefixEnd_2835390 : Nat := 4983230072969 + 3 ^ 40 * 2835390 * 2
def baseEnd_2835390 : Nat := 1455917912951766757285285

theorem tailTrace_2835390 : CollatzResearch.WordTrace tailWord_2835390 prefixEnd_2835390 1455917912951766757285285 := by
  unfold tailWord_2835390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12926896149734218863038953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68943446131915833936207749 12926896149734218863038953)
  ·
    refine ⟨9695172112300664147279215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12926896149734218863038953 9695172112300664147279215)
    ·
      refine ⟨14542758168450996220918823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9695172112300664147279215 14542758168450996220918823)
      ·
        refine ⟨21814137252676494331378235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14542758168450996220918823 21814137252676494331378235)
        ·
          refine ⟨32721205879014741497067353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21814137252676494331378235 32721205879014741497067353)
          ·
            refine ⟨24540904409261056122800515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32721205879014741497067353 24540904409261056122800515)
            ·
              refine ⟨36811356613891584184200773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24540904409261056122800515 36811356613891584184200773)
              ·
                refine ⟨6902129365104672034537645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36811356613891584184200773 6902129365104672034537645)
                ·
                  refine ⟨2588298511914252012951617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6902129365104672034537645 2588298511914252012951617)
                  ·
                    refine ⟨1941223883935689009713713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588298511914252012951617 1941223883935689009713713)
                    ·
                      refine ⟨1455917912951766757285285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941223883935689009713713 1455917912951766757285285)
                      ·
                        rfl

theorem cell23_2835390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_2835390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835390 prefixEnd_2835390 := by exact prefixLift 2835390
  have htrace : WordTrace (prefixWord ++ tailWord_2835390) baseStart_2835390 baseEnd_2835390 := by
    simpa [prefixWord, tailWord_2835390, baseEnd_2835390] using wordTrace_append hprefix tailTrace_2835390
  have hstable : (prefixWord ++ tailWord_2835390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835390).length < 2 ^ (prefixWord ++ tailWord_2835390).sum := by decide
  have hdescent : baseEnd_2835390 < baseStart_2835390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835407 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 1, 2, 2]
def baseStart_2835407 : Nat := 118140960795 + 2835407 * 2 ^ 59
def prefixEnd_2835407 : Nat := 4983230072969 + 3 ^ 40 * 2835407 * 2
def baseEnd_2835407 : Nat := 1455926642122893190772707

theorem tailTrace_2835407 : CollatzResearch.WordTrace tailWord_2835407 prefixEnd_2835407 1455926642122893190772707 := by
  unfold tailWord_2835407
  simp only [CollatzResearch.WordTrace]
  refine ⟨103415789238812162807680475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68943859492541441871786983 103415789238812162807680475)
  ·
    refine ⟨155123683858218244211520713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103415789238812162807680475 155123683858218244211520713)
    ·
      refine ⟨116342762893663683158640535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155123683858218244211520713 116342762893663683158640535)
      ·
        refine ⟨174514144340495524737960803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116342762893663683158640535 174514144340495524737960803)
        ·
          refine ⟨261771216510743287106941205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174514144340495524737960803 261771216510743287106941205)
          ·
            refine ⟨12270525773941091583137869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261771216510743287106941205 12270525773941091583137869)
            ·
              refine ⟨4601447165227909343676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12270525773941091583137869 4601447165227909343676701)
              ·
                refine ⟨1725542686960466003878763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4601447165227909343676701 1725542686960466003878763)
                ·
                  refine ⟨2588314030440699005818145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725542686960466003878763 2588314030440699005818145)
                  ·
                    refine ⟨1941235522830524254363609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588314030440699005818145 1941235522830524254363609)
                    ·
                      refine ⟨1455926642122893190772707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941235522830524254363609 1455926642122893190772707)
                      ·
                        rfl

theorem cell23_2835407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 2, 2].length) (baseStart_2835407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835407 prefixEnd_2835407 := by exact prefixLift 2835407
  have htrace : WordTrace (prefixWord ++ tailWord_2835407) baseStart_2835407 baseEnd_2835407 := by
    simpa [prefixWord, tailWord_2835407, baseEnd_2835407] using wordTrace_append hprefix tailTrace_2835407
  have hstable : (prefixWord ++ tailWord_2835407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835407).length < 2 ^ (prefixWord ++ tailWord_2835407).sum := by decide
  have hdescent : baseEnd_2835407 < baseStart_2835407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835410 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2835410 : Nat := 118140960795 + 2835410 * 2 ^ 59
def prefixEnd_2835410 : Nat := 4983230072969 + 3 ^ 40 * 2835410 * 2
def baseEnd_2835410 : Nat := 1455928182564856679035193

theorem tailTrace_2835410 : CollatzResearch.WordTrace tailWord_2835410 prefixEnd_2835410 1455928182564856679035193 := by
  unfold tailWord_2835410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853974664450323580009921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68943932438534196213359789 25853974664450323580009921)
  ·
    refine ⟨19390480998337742685007441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25853974664450323580009921 19390480998337742685007441)
    ·
      refine ⟨14542860748753307013755581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19390480998337742685007441 14542860748753307013755581)
      ·
        refine ⟨5453572780782490130158343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14542860748753307013755581 5453572780782490130158343)
        ·
          refine ⟨8180359171173735195237515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453572780782490130158343 8180359171173735195237515)
          ·
            refine ⟨12270538756760602792856273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180359171173735195237515 12270538756760602792856273)
            ·
              refine ⟨9202904067570452094642205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12270538756760602792856273 9202904067570452094642205)
              ·
                refine ⟨3451089025338919535490827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9202904067570452094642205 3451089025338919535490827)
                ·
                  refine ⟨5176633538008379303236241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451089025338919535490827 5176633538008379303236241)
                  ·
                    refine ⟨3882475153506284477427181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176633538008379303236241 3882475153506284477427181)
                    ·
                      refine ⟨1455928182564856679035193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882475153506284477427181 1455928182564856679035193)
                      ·
                        rfl

theorem cell23_2835410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2835410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835410 prefixEnd_2835410 := by exact prefixLift 2835410
  have htrace : WordTrace (prefixWord ++ tailWord_2835410) baseStart_2835410 baseEnd_2835410 := by
    simpa [prefixWord, tailWord_2835410, baseEnd_2835410] using wordTrace_append hprefix tailTrace_2835410
  have hstable : (prefixWord ++ tailWord_2835410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835410).length < 2 ^ (prefixWord ++ tailWord_2835410).sum := by decide
  have hdescent : baseEnd_2835410 < baseStart_2835410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835413 : List Nat := [1, 3, 2, 3, 4, 1, 9]
def baseStart_2835413 : Nat := 118140960795 + 2835413 * 2 ^ 59
def prefixEnd_2835413 : Nat := 4983230072969 + 3 ^ 40 * 2835413 * 2
def baseEnd_2835413 : Nat := 17974441024775557620959

theorem tailTrace_2835413 : CollatzResearch.WordTrace tailWord_2835413 prefixEnd_2835413 17974441024775557620959 := by
  unfold tailWord_2835413
  simp only [CollatzResearch.WordTrace]
  refine ⟨103416008076790425832398893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68944005384526950554932595 103416008076790425832398893)
  ·
    refine ⟨38781003028796409687149585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103416008076790425832398893 38781003028796409687149585)
    ·
      refine ⟨29085752271597307265362189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38781003028796409687149585 29085752271597307265362189)
      ·
        refine ⟨10907157101848990224510821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29085752271597307265362189 10907157101848990224510821)
        ·
          refine ⟨2045091956596685667095779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10907157101848990224510821 2045091956596685667095779)
          ·
            refine ⟨3067637934895028500643669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045091956596685667095779 3067637934895028500643669)
            ·
              refine ⟨17974441024775557620959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3067637934895028500643669 17974441024775557620959)
              ·
                rfl

theorem cell23_2835413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 9].length) (baseStart_2835413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835413 prefixEnd_2835413 := by exact prefixLift 2835413
  have htrace : WordTrace (prefixWord ++ tailWord_2835413) baseStart_2835413 baseEnd_2835413 := by
    simpa [prefixWord, tailWord_2835413, baseEnd_2835413] using wordTrace_append hprefix tailTrace_2835413
  have hstable : (prefixWord ++ tailWord_2835413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835413).length < 2 ^ (prefixWord ++ tailWord_2835413).sum := by decide
  have hdescent : baseEnd_2835413 < baseStart_2835413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835467 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 1, 3, 2]
def baseStart_2835467 : Nat := 118140960795 + 2835467 * 2 ^ 59
def prefixEnd_2835467 : Nat := 4983230072969 + 3 ^ 40 * 2835467 * 2
def baseEnd_2835467 : Nat := 1455957450962162956022431

theorem tailTrace_2835467 : CollatzResearch.WordTrace tailWord_2835467 prefixEnd_2835467 1455957450962162956022431 := by
  unfold tailWord_2835467
  simp only [CollatzResearch.WordTrace]
  refine ⟨103417977618594793054864655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68945318412396528703243103 103417977618594793054864655)
  ·
    refine ⟨155126966427892189582296983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103417977618594793054864655 155126966427892189582296983)
    ·
      refine ⟨232690449641838284373445475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155126966427892189582296983 232690449641838284373445475)
      ·
        refine ⟨349035674462757426560168213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232690449641838284373445475 349035674462757426560168213)
        ·
          refine ⟨16361047240441754370007885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 349035674462757426560168213 16361047240441754370007885)
          ·
            refine ⟨6135392715165657888752957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16361047240441754370007885 6135392715165657888752957)
            ·
              refine ⟨2300772268187121708282359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135392715165657888752957 2300772268187121708282359)
              ·
                refine ⟨3451158402280682562423539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300772268187121708282359 3451158402280682562423539)
                ·
                  refine ⟨5176737603421023843635309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451158402280682562423539 5176737603421023843635309)
                  ·
                    refine ⟨1941276601282883941363241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5176737603421023843635309 1941276601282883941363241)
                    ·
                      refine ⟨1455957450962162956022431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941276601282883941363241 1455957450962162956022431)
                      ·
                        rfl

theorem cell23_2835467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 3, 2].length) (baseStart_2835467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835467 prefixEnd_2835467 := by exact prefixLift 2835467
  have htrace : WordTrace (prefixWord ++ tailWord_2835467) baseStart_2835467 baseEnd_2835467 := by
    simpa [prefixWord, tailWord_2835467, baseEnd_2835467] using wordTrace_append hprefix tailTrace_2835467
  have hstable : (prefixWord ++ tailWord_2835467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835467).length < 2 ^ (prefixWord ++ tailWord_2835467).sum := by decide
  have hdescent : baseEnd_2835467 < baseStart_2835467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835576 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 8]
def baseStart_2835576 : Nat := 118140960795 + 2835576 * 2 ^ 59
def prefixEnd_2835576 : Nat := 4983230072969 + 3 ^ 40 * 2835576 * 2
def baseEnd_2835576 : Nat := 161779268928167003284381

theorem tailTrace_2835576 : CollatzResearch.WordTrace tailWord_2835576 prefixEnd_2835576 161779268928167003284381 := by
  unfold tailWord_2835576
  simp only [CollatzResearch.WordTrace]
  refine ⟨51710976587599952335291291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68947968783466603113721721 51710976587599952335291291)
  ·
    refine ⟨77566464881399928502936937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51710976587599952335291291 77566464881399928502936937)
    ·
      refine ⟨58174848661049946377202703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77566464881399928502936937 58174848661049946377202703)
      ·
        refine ⟨87262272991574919565804055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58174848661049946377202703 87262272991574919565804055)
        ·
          refine ⟨130893409487362379348706083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87262272991574919565804055 130893409487362379348706083)
          ·
            refine ⟨196340114231043569023059125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130893409487362379348706083 196340114231043569023059125)
            ·
              refine ⟨18406885709160334595911793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196340114231043569023059125 18406885709160334595911793)
              ·
                refine ⟨13805164281870250946933845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18406885709160334595911793 13805164281870250946933845)
                ·
                  refine ⟨161779268928167003284381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13805164281870250946933845 161779268928167003284381)
                  ·
                    rfl

theorem cell23_2835576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_2835576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835576 prefixEnd_2835576 := by exact prefixLift 2835576
  have htrace : WordTrace (prefixWord ++ tailWord_2835576) baseStart_2835576 baseEnd_2835576 := by
    simpa [prefixWord, tailWord_2835576, baseEnd_2835576] using wordTrace_append hprefix tailTrace_2835576
  have hstable : (prefixWord ++ tailWord_2835576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835576).length < 2 ^ (prefixWord ++ tailWord_2835576).sum := by decide
  have hdescent : baseEnd_2835576 < baseStart_2835576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835596 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2835596 : Nat := 118140960795 + 2835596 * 2 ^ 59
def prefixEnd_2835596 : Nat := 4983230072969 + 3 ^ 40 * 2835596 * 2
def baseEnd_2835596 : Nat := 1456023689966592951309337

theorem tailTrace_2835596 : CollatzResearch.WordTrace tailWord_2835596 prefixEnd_2835596 1456023689966592951309337 := by
  unfold tailWord_2835596
  simp only [CollatzResearch.WordTrace]
  refine ⟨51711341317563724043155321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68948455090084965390873761 51711341317563724043155321)
  ·
    refine ⟨38783505988172793032366491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51711341317563724043155321 38783505988172793032366491)
    ·
      refine ⟨58175258982259189548549737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38783505988172793032366491 58175258982259189548549737)
      ·
        refine ⟨43631444236694392161412303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58175258982259189548549737 43631444236694392161412303)
        ·
          refine ⟨65447166355041588242118455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43631444236694392161412303 65447166355041588242118455)
          ·
            refine ⟨98170749532562382363177683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65447166355041588242118455 98170749532562382363177683)
            ·
              refine ⟨147256124298843573544766525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98170749532562382363177683 147256124298843573544766525)
              ·
                refine ⟨55221046612066340079287447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147256124298843573544766525 55221046612066340079287447)
                ·
                  refine ⟨82831569918099510118931171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55221046612066340079287447 82831569918099510118931171)
                  ·
                    refine ⟨124247354877149265178396757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82831569918099510118931171 124247354877149265178396757)
                    ·
                      refine ⟨1456023689966592951309337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 124247354877149265178396757 1456023689966592951309337)
                      ·
                        rfl

theorem cell23_2835596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2835596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835596 prefixEnd_2835596 := by exact prefixLift 2835596
  have htrace : WordTrace (prefixWord ++ tailWord_2835596) baseStart_2835596 baseEnd_2835596 := by
    simpa [prefixWord, tailWord_2835596, baseEnd_2835596] using wordTrace_append hprefix tailTrace_2835596
  have hstable : (prefixWord ++ tailWord_2835596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835596).length < 2 ^ (prefixWord ++ tailWord_2835596).sum := by decide
  have hdescent : baseEnd_2835596 < baseStart_2835596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835610 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_2835610 : Nat := 118140960795 + 2835610 * 2 ^ 59
def prefixEnd_2835610 : Nat := 4983230072969 + 3 ^ 40 * 2835610 * 2
def baseEnd_2835610 : Nat := 161781208743972877392697

theorem tailTrace_2835610 : CollatzResearch.WordTrace tailWord_2835610 prefixEnd_2835610 161781208743972877392697 := by
  unfold tailWord_2835610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25855798314269182119330071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68948795504717818984880189 25855798314269182119330071)
  ·
    refine ⟨38783697471403773178995107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25855798314269182119330071 38783697471403773178995107)
    ·
      refine ⟨58175546207105659768492661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38783697471403773178995107 58175546207105659768492661)
      ·
        refine ⟨5453957456916155603296187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58175546207105659768492661 5453957456916155603296187)
        ·
          refine ⟨8180936185374233404944281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453957456916155603296187 8180936185374233404944281)
          ·
            refine ⟨6135702139030675053708211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8180936185374233404944281 6135702139030675053708211)
            ·
              refine ⟨9203553208546012580562317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135702139030675053708211 9203553208546012580562317)
              ·
                refine ⟨3451332453204754717710869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9203553208546012580562317 3451332453204754717710869)
                ·
                  refine ⟨161781208743972877392697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3451332453204754717710869 161781208743972877392697)
                  ·
                    rfl

theorem cell23_2835610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_2835610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835610 prefixEnd_2835610 := by exact prefixLift 2835610
  have htrace : WordTrace (prefixWord ++ tailWord_2835610) baseStart_2835610 baseEnd_2835610 := by
    simpa [prefixWord, tailWord_2835610, baseEnd_2835610] using wordTrace_append hprefix tailTrace_2835610
  have hstable : (prefixWord ++ tailWord_2835610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835610).length < 2 ^ (prefixWord ++ tailWord_2835610).sum := by decide
  have hdescent : baseEnd_2835610 < baseStart_2835610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835680 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_2835680 : Nat := 118140960795 + 2835680 * 2 ^ 59
def prefixEnd_2835680 : Nat := 4983230072969 + 3 ^ 40 * 2835680 * 2
def baseEnd_2835680 : Nat := 1456066822341570622658951

theorem tailTrace_2835680 : CollatzResearch.WordTrace tailWord_2835680 prefixEnd_2835680 1456066822341570622658951 := by
  unfold tailWord_2835680
  simp only [CollatzResearch.WordTrace]
  refine ⟨51712873183411565216184247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68950497577882086954912329 51712873183411565216184247)
  ·
    refine ⟨77569309775117347824276371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51712873183411565216184247 77569309775117347824276371)
    ·
      refine ⟨116353964662676021736414557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77569309775117347824276371 116353964662676021736414557)
      ·
        refine ⟨43632736748503508151155459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116353964662676021736414557 43632736748503508151155459)
        ·
          refine ⟨65449105122755262226733189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43632736748503508151155459 65449105122755262226733189)
          ·
            refine ⟨12271707210516611667512473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65449105122755262226733189 12271707210516611667512473)
            ·
              refine ⟨9203780407887458750634355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12271707210516611667512473 9203780407887458750634355)
              ·
                refine ⟨13805670611831188125951533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203780407887458750634355 13805670611831188125951533)
                ·
                  refine ⟨5177126479436695547231825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13805670611831188125951533 5177126479436695547231825)
                  ·
                    refine ⟨3882844859577521660423869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177126479436695547231825 3882844859577521660423869)
                    ·
                      refine ⟨1456066822341570622658951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882844859577521660423869 1456066822341570622658951)
                      ·
                        rfl

theorem cell23_2835680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_2835680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835680 prefixEnd_2835680 := by exact prefixLift 2835680
  have htrace : WordTrace (prefixWord ++ tailWord_2835680) baseStart_2835680 baseEnd_2835680 := by
    simpa [prefixWord, tailWord_2835680, baseEnd_2835680] using wordTrace_append hprefix tailTrace_2835680
  have hstable : (prefixWord ++ tailWord_2835680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835680).length < 2 ^ (prefixWord ++ tailWord_2835680).sum := by decide
  have hdescent : baseEnd_2835680 < baseStart_2835680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835690 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2835690 : Nat := 118140960795 + 2835690 * 2 ^ 59
def prefixEnd_2835690 : Nat := 4983230072969 + 3 ^ 40 * 2835690 * 2
def baseEnd_2835690 : Nat := 1456071957148115583533905

theorem tailTrace_2835690 : CollatzResearch.WordTrace tailWord_2835690 prefixEnd_2835690 1456071957148115583533905 := by
  unfold tailWord_2835690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25856527774196725535058131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68950740731191268093488349 25856527774196725535058131)
  ·
    refine ⟨38784791661295088302587197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25856527774196725535058131 38784791661295088302587197)
    ·
      refine ⟨14544296872985658113470199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38784791661295088302587197 14544296872985658113470199)
      ·
        refine ⟨21816445309478487170205299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14544296872985658113470199 21816445309478487170205299)
        ·
          refine ⟨32724667964217730755307949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21816445309478487170205299 32724667964217730755307949)
          ·
            refine ⟨12271750486581649033240481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32724667964217730755307949 12271750486581649033240481)
            ·
              refine ⟨9203812864936236774930361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12271750486581649033240481 9203812864936236774930361)
              ·
                refine ⟨6902859648702177581197771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9203812864936236774930361 6902859648702177581197771)
                ·
                  refine ⟨10354289473053266371796657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6902859648702177581197771 10354289473053266371796657)
                  ·
                    refine ⟨7765717104789949778847493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10354289473053266371796657 7765717104789949778847493)
                    ·
                      refine ⟨1456071957148115583533905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7765717104789949778847493 1456071957148115583533905)
                      ·
                        rfl

theorem cell23_2835690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2835690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835690 prefixEnd_2835690 := by exact prefixLift 2835690
  have htrace : WordTrace (prefixWord ++ tailWord_2835690) baseStart_2835690 baseEnd_2835690 := by
    simpa [prefixWord, tailWord_2835690, baseEnd_2835690] using wordTrace_append hprefix tailTrace_2835690
  have hstable : (prefixWord ++ tailWord_2835690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835690).length < 2 ^ (prefixWord ++ tailWord_2835690).sum := by decide
  have hdescent : baseEnd_2835690 < baseStart_2835690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835770 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_2835770 : Nat := 118140960795 + 2835770 * 2 ^ 59
def prefixEnd_2835770 : Nat := 4983230072969 + 3 ^ 40 * 2835770 * 2
def baseEnd_2835770 : Nat := 1456113035600475270533537

theorem tailTrace_2835770 : CollatzResearch.WordTrace tailWord_2835770 prefixEnd_2835770 1456113035600475270533537 := by
  unfold tailWord_2835770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857257234124268950786191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68952685957664717202096509 25857257234124268950786191)
  ·
    refine ⟨38785885851186403426179287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857257234124268950786191 38785885851186403426179287)
    ·
      refine ⟨58178828776779605139268931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38785885851186403426179287 58178828776779605139268931)
      ·
        refine ⟨87268243165169407708903397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58178828776779605139268931 87268243165169407708903397)
        ·
          refine ⟨16362795593469263945419387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87268243165169407708903397 16362795593469263945419387)
          ·
            refine ⟨24544193390203895918129081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16362795593469263945419387 24544193390203895918129081)
            ·
              refine ⟨18408145042652921938596811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24544193390203895918129081 18408145042652921938596811)
              ·
                refine ⟨27612217563979382907895217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18408145042652921938596811 27612217563979382907895217)
                ·
                  refine ⟨20709163172984537180921413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27612217563979382907895217 20709163172984537180921413)
                  ·
                    refine ⟨3882968094934600721422765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20709163172984537180921413 3882968094934600721422765)
                    ·
                      refine ⟨1456113035600475270533537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3882968094934600721422765 1456113035600475270533537)
                      ·
                        rfl

theorem cell23_2835770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_2835770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835770 prefixEnd_2835770 := by exact prefixLift 2835770
  have htrace : WordTrace (prefixWord ++ tailWord_2835770) baseStart_2835770 baseEnd_2835770 := by
    simpa [prefixWord, tailWord_2835770, baseEnd_2835770] using wordTrace_append hprefix tailTrace_2835770
  have hstable : (prefixWord ++ tailWord_2835770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835770).length < 2 ^ (prefixWord ++ tailWord_2835770).sum := by decide
  have hdescent : baseEnd_2835770 < baseStart_2835770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835818 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2835818 : Nat := 118140960795 + 2835818 * 2 ^ 59
def prefixEnd_2835818 : Nat := 4983230072969 + 3 ^ 40 * 2835818 * 2
def baseEnd_2835818 : Nat := 1456137682671891082733317

theorem tailTrace_2835818 : CollatzResearch.WordTrace tailWord_2835818 prefixEnd_2835818 1456137682671891082733317 := by
  unfold tailWord_2835818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857694910080795000223027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68953853093548786667261405 25857694910080795000223027)
  ·
    refine ⟨38786542365121192500334541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857694910080795000223027 38786542365121192500334541)
    ·
      refine ⟨14544953386920447187625453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38786542365121192500334541 14544953386920447187625453)
      ·
        refine ⟨5454357520095167695359545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14544953386920447187625453 5454357520095167695359545)
        ·
          refine ⟨4090768140071375771519659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5454357520095167695359545 4090768140071375771519659)
          ·
            refine ⟨6136152210107063657279489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4090768140071375771519659 6136152210107063657279489)
            ·
              refine ⟨4602114157580297742959617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136152210107063657279489 4602114157580297742959617)
              ·
                refine ⟨3451585618185223307219713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602114157580297742959617 3451585618185223307219713)
                ·
                  refine ⟨2588689213638917480414785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451585618185223307219713 2588689213638917480414785)
                  ·
                    refine ⟨1941516910229188110311089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588689213638917480414785 1941516910229188110311089)
                    ·
                      refine ⟨1456137682671891082733317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941516910229188110311089 1456137682671891082733317)
                      ·
                        rfl

theorem cell23_2835818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2835818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835818 prefixEnd_2835818 := by exact prefixLift 2835818
  have htrace : WordTrace (prefixWord ++ tailWord_2835818) baseStart_2835818 baseEnd_2835818 := by
    simpa [prefixWord, tailWord_2835818, baseEnd_2835818] using wordTrace_append hprefix tailTrace_2835818
  have hstable : (prefixWord ++ tailWord_2835818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835818).length < 2 ^ (prefixWord ++ tailWord_2835818).sum := by decide
  have hdescent : baseEnd_2835818 < baseStart_2835818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835840 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_2835840 : Nat := 118140960795 + 2835840 * 2 ^ 59
def prefixEnd_2835840 : Nat := 4983230072969 + 3 ^ 40 * 2835840 * 2
def baseEnd_2835840 : Nat := 1456148979246289996658215

theorem tailTrace_2835840 : CollatzResearch.WordTrace tailWord_2835840 prefixEnd_2835840 1456148979246289996658215 := by
  unfold tailWord_2835840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51715791023121738879096487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68954388030828985172128649 51715791023121738879096487)
  ·
    refine ⟨77573686534682608318644731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51715791023121738879096487 77573686534682608318644731)
    ·
      refine ⟨116360529802023912477967097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77573686534682608318644731 116360529802023912477967097)
      ·
        refine ⟨87270397351517934358475323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116360529802023912477967097 87270397351517934358475323)
        ·
          refine ⟨130905596027276901537712985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87270397351517934358475323 130905596027276901537712985)
          ·
            refine ⟨98179197020457676153284739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130905596027276901537712985 98179197020457676153284739)
            ·
              refine ⟨147268795530686514229927109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98179197020457676153284739 147268795530686514229927109)
              ·
                refine ⟨27612899162003721418111333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147268795530686514229927109 27612899162003721418111333)
                ·
                  refine ⟨5177418592875697765895875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27612899162003721418111333 5177418592875697765895875)
                  ·
                    refine ⟨7766127889313546648843813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177418592875697765895875 7766127889313546648843813)
                    ·
                      refine ⟨1456148979246289996658215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7766127889313546648843813 1456148979246289996658215)
                      ·
                        rfl

theorem cell23_2835840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_2835840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835840 prefixEnd_2835840 := by exact prefixLift 2835840
  have htrace : WordTrace (prefixWord ++ tailWord_2835840) baseStart_2835840 baseEnd_2835840 := by
    simpa [prefixWord, tailWord_2835840, baseEnd_2835840] using wordTrace_append hprefix tailTrace_2835840
  have hstable : (prefixWord ++ tailWord_2835840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835840).length < 2 ^ (prefixWord ++ tailWord_2835840).sum := by decide
  have hdescent : baseEnd_2835840 < baseStart_2835840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835874 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2835874 : Nat := 118140960795 + 2835874 * 2 ^ 59
def prefixEnd_2835874 : Nat := 4983230072969 + 3 ^ 40 * 2835874 * 2
def baseEnd_2835874 : Nat := 1456166437588542863633059

theorem tailTrace_2835874 : CollatzResearch.WordTrace tailWord_2835874 prefixEnd_2835874 1456166437588542863633059 := by
  unfold tailWord_2835874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858205532030075391232669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68955214752080201043287117 25858205532030075391232669)
  ·
    refine ⟨9696827074511278271712251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25858205532030075391232669 9696827074511278271712251)
    ·
      refine ⟨14545240611766917407568377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9696827074511278271712251 14545240611766917407568377)
      ·
        refine ⟨10908930458825188055676283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14545240611766917407568377 10908930458825188055676283)
        ·
          refine ⟨16363395688237782083514425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10908930458825188055676283 16363395688237782083514425)
          ·
            refine ⟨12272546766178336562635819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16363395688237782083514425 12272546766178336562635819)
            ·
              refine ⟨18408820149267504843953729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272546766178336562635819 18408820149267504843953729)
              ·
                refine ⟨13806615111950628632965297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18408820149267504843953729 13806615111950628632965297)
                ·
                  refine ⟨10354961333962971474723973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13806615111950628632965297 10354961333962971474723973)
                  ·
                    refine ⟨1941555250118057151510745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10354961333962971474723973 1941555250118057151510745)
                    ·
                      refine ⟨1456166437588542863633059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941555250118057151510745 1456166437588542863633059)
                      ·
                        rfl

theorem cell23_2835874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2835874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835874 prefixEnd_2835874 := by exact prefixLift 2835874
  have htrace : WordTrace (prefixWord ++ tailWord_2835874) baseStart_2835874 baseEnd_2835874 := by
    simpa [prefixWord, tailWord_2835874, baseEnd_2835874] using wordTrace_append hprefix tailTrace_2835874
  have hstable : (prefixWord ++ tailWord_2835874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835874).length < 2 ^ (prefixWord ++ tailWord_2835874).sum := by decide
  have hdescent : baseEnd_2835874 < baseStart_2835874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835884 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_2835884 : Nat := 118140960795 + 2835884 * 2 ^ 59
def prefixEnd_2835884 : Nat := 4983230072969 + 3 ^ 40 * 2835884 * 2
def baseEnd_2835884 : Nat := 485390524131695941502671

theorem tailTrace_2835884 : CollatzResearch.WordTrace tailWord_2835884 prefixEnd_2835884 485390524131695941502671 := by
  unfold tailWord_2835884
  simp only [CollatzResearch.WordTrace]
  refine ⟨51716593429042036636397353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68955457905389382181863137 51716593429042036636397353)
  ·
    refine ⟨38787445071781527477298015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51716593429042036636397353 38787445071781527477298015)
    ·
      refine ⟨58181167607672291215947023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38787445071781527477298015 58181167607672291215947023)
      ·
        refine ⟨87271751411508436823920535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58181167607672291215947023 87271751411508436823920535)
        ·
          refine ⟨130907627117262655235880803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87271751411508436823920535 130907627117262655235880803)
          ·
            refine ⟨196361440675893982853821205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130907627117262655235880803 196361440675893982853821205)
            ·
              refine ⟨9204442531682530446272869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196361440675893982853821205 9204442531682530446272869)
              ·
                refine ⟨1725832974690474458676163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9204442531682530446272869 1725832974690474458676163)
                ·
                  refine ⟨2588749462035711688014245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725832974690474458676163 2588749462035711688014245)
                  ·
                    refine ⟨485390524131695941502671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2588749462035711688014245 485390524131695941502671)
                    ·
                      rfl

theorem cell23_2835884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_2835884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835884 prefixEnd_2835884 := by exact prefixLift 2835884
  have htrace : WordTrace (prefixWord ++ tailWord_2835884) baseStart_2835884 baseEnd_2835884 := by
    simpa [prefixWord, tailWord_2835884, baseEnd_2835884] using wordTrace_append hprefix tailTrace_2835884
  have hstable : (prefixWord ++ tailWord_2835884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835884).length < 2 ^ (prefixWord ++ tailWord_2835884).sum := by decide
  have hdescent : baseEnd_2835884 < baseStart_2835884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835941 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2835941 : Nat := 118140960795 + 2835941 * 2 ^ 59
def prefixEnd_2835941 : Nat := 4983230072969 + 3 ^ 40 * 2835941 * 2
def baseEnd_2835941 : Nat := 1456200840792394101495251

theorem tailTrace_2835941 : CollatzResearch.WordTrace tailWord_2835941 prefixEnd_2835941 1456200840792394101495251 := by
  unfold tailWord_2835941
  simp only [CollatzResearch.WordTrace]
  refine ⟨103435265818877572007619677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68956843879251714671746451 103435265818877572007619677)
  ·
    refine ⟨38788224682079089502857379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103435265818877572007619677 38788224682079089502857379)
    ·
      refine ⟨58182337023118634254286069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38788224682079089502857379 58182337023118634254286069)
      ·
        refine ⟨5454594095917371961339319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58182337023118634254286069 5454594095917371961339319)
        ·
          refine ⟨8181891143876057942008979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5454594095917371961339319 8181891143876057942008979)
          ·
            refine ⟨12272836715814086913013469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8181891143876057942008979 12272836715814086913013469)
            ·
              refine ⟨4602313768430282592380051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12272836715814086913013469 4602313768430282592380051)
              ·
                refine ⟨6903470652645423888570077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602313768430282592380051 6903470652645423888570077)
                ·
                  refine ⟨2588801494742033958213779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6903470652645423888570077 2588801494742033958213779)
                  ·
                    refine ⟨3883202242113050937320669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588801494742033958213779 3883202242113050937320669)
                    ·
                      refine ⟨1456200840792394101495251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883202242113050937320669 1456200840792394101495251)
                      ·
                        rfl

theorem cell23_2835941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2835941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835941 prefixEnd_2835941 := by exact prefixLift 2835941
  have htrace : WordTrace (prefixWord ++ tailWord_2835941) baseStart_2835941 baseEnd_2835941 := by
    simpa [prefixWord, tailWord_2835941, baseEnd_2835941] using wordTrace_append hprefix tailTrace_2835941
  have hstable : (prefixWord ++ tailWord_2835941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835941).length < 2 ^ (prefixWord ++ tailWord_2835941).sum := by decide
  have hdescent : baseEnd_2835941 < baseStart_2835941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835947 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 6, 2]
def baseStart_2835947 : Nat := 118140960795 + 2835947 * 2 ^ 59
def prefixEnd_2835947 : Nat := 4983230072969 + 3 ^ 40 * 2835947 * 2
def baseEnd_2835947 : Nat := 1456203921676321078020223

theorem tailTrace_2835947 : CollatzResearch.WordTrace tailWord_2835947 prefixEnd_2835947 1456203921676321078020223 := by
  unfold tailWord_2835947
  simp only [CollatzResearch.WordTrace]
  refine ⟨103435484656855835032338095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68956989771237223354892063 103435484656855835032338095)
  ·
    refine ⟨155153226985283752548507143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103435484656855835032338095 155153226985283752548507143)
    ·
      refine ⟨232729840477925628822760715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155153226985283752548507143 232729840477925628822760715)
      ·
        refine ⟨349094760716888443234141073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232729840477925628822760715 349094760716888443234141073)
        ·
          refine ⟨261821070537666332425605805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349094760716888443234141073 261821070537666332425605805)
          ·
            refine ⟨98182901451624874659602177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261821070537666332425605805 98182901451624874659602177)
            ·
              refine ⟨73637176088718655994701633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98182901451624874659602177 73637176088718655994701633)
              ·
                refine ⟨55227882066538991996026225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73637176088718655994701633 55227882066538991996026225)
                ·
                  refine ⟨41420911549904243997019669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55227882066538991996026225 41420911549904243997019669)
                  ·
                    refine ⟨1941605228901761437360297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41420911549904243997019669 1941605228901761437360297)
                    ·
                      refine ⟨1456203921676321078020223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941605228901761437360297 1456203921676321078020223)
                      ·
                        rfl

theorem cell23_2835947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6, 2].length) (baseStart_2835947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835947 prefixEnd_2835947 := by exact prefixLift 2835947
  have htrace : WordTrace (prefixWord ++ tailWord_2835947) baseStart_2835947 baseEnd_2835947 := by
    simpa [prefixWord, tailWord_2835947, baseEnd_2835947] using wordTrace_append hprefix tailTrace_2835947
  have hstable : (prefixWord ++ tailWord_2835947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835947).length < 2 ^ (prefixWord ++ tailWord_2835947).sum := by decide
  have hdescent : baseEnd_2835947 < baseStart_2835947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835964 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2835964 : Nat := 118140960795 + 2835964 * 2 ^ 59
def prefixEnd_2835964 : Nat := 4983230072969 + 3 ^ 40 * 2835964 * 2
def baseEnd_2835964 : Nat := 1456212650847447511507645

theorem tailTrace_2835964 : CollatzResearch.WordTrace tailWord_2835964 prefixEnd_2835964 1456212650847447511507645 := by
  unfold tailWord_2835964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718052348897123467853473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68957403131862831290471297 51718052348897123467853473)
  ·
    refine ⟨38788539261672842600890105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51718052348897123467853473 38788539261672842600890105)
    ·
      refine ⟨29091404446254631950667579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38788539261672842600890105 29091404446254631950667579)
      ·
        refine ⟨43637106669381947926001369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29091404446254631950667579 43637106669381947926001369)
        ·
          refine ⟨32727830002036460944501027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43637106669381947926001369 32727830002036460944501027)
          ·
            refine ⟨49091745003054691416751541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32727830002036460944501027 49091745003054691416751541)
            ·
              refine ⟨4602351094036377320320457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49091745003054691416751541 4602351094036377320320457)
              ·
                refine ⟨3451763320527282990240343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602351094036377320320457 3451763320527282990240343)
                ·
                  refine ⟨5177644980790924485360515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451763320527282990240343 5177644980790924485360515)
                  ·
                    refine ⟨7766467471186386728040773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177644980790924485360515 7766467471186386728040773)
                    ·
                      refine ⟨1456212650847447511507645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7766467471186386728040773 1456212650847447511507645)
                      ·
                        rfl

theorem cell23_2835964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2835964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835964 prefixEnd_2835964 := by exact prefixLift 2835964
  have htrace : WordTrace (prefixWord ++ tailWord_2835964) baseStart_2835964 baseEnd_2835964 := by
    simpa [prefixWord, tailWord_2835964, baseEnd_2835964] using wordTrace_append hprefix tailTrace_2835964
  have hstable : (prefixWord ++ tailWord_2835964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835964).length < 2 ^ (prefixWord ++ tailWord_2835964).sum := by decide
  have hdescent : baseEnd_2835964 < baseStart_2835964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835977 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_2835977 : Nat := 118140960795 + 2835977 * 2 ^ 59
def prefixEnd_2835977 : Nat := 4983230072969 + 3 ^ 40 * 2835977 * 2
def baseEnd_2835977 : Nat := 1456219326095955960645085

theorem tailTrace_2835977 : CollatzResearch.WordTrace tailWord_2835977 prefixEnd_2835977 1456219326095955960645085 := by
  unfold tailWord_2835977
  simp only [CollatzResearch.WordTrace]
  refine ⟨103436578846747150155930185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68957719231164766770620123 103436578846747150155930185)
  ·
    refine ⟨77577434135060362616947639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103436578846747150155930185 77577434135060362616947639)
    ·
      refine ⟨116366151202590543925421459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77577434135060362616947639 116366151202590543925421459)
      ·
        refine ⟨174549226803885815888132189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116366151202590543925421459 174549226803885815888132189)
        ·
          refine ⟨65455960051457180958049571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174549226803885815888132189 65455960051457180958049571)
          ·
            refine ⟨98183940077185771437074357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65455960051457180958049571 98183940077185771437074357)
            ·
              refine ⟨9204744382236166072225721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98183940077185771437074357 9204744382236166072225721)
              ·
                refine ⟨6903558286677124554169291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9204744382236166072225721 6903558286677124554169291)
                ·
                  refine ⟨10355337430015686831253937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903558286677124554169291 10355337430015686831253937)
                  ·
                    refine ⟨7766503072511765123440453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10355337430015686831253937 7766503072511765123440453)
                    ·
                      refine ⟨1456219326095955960645085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7766503072511765123440453 1456219326095955960645085)
                      ·
                        rfl

theorem cell23_2835977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_2835977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835977 prefixEnd_2835977 := by exact prefixLift 2835977
  have htrace : WordTrace (prefixWord ++ tailWord_2835977) baseStart_2835977 baseEnd_2835977 := by
    simpa [prefixWord, tailWord_2835977, baseEnd_2835977] using wordTrace_append hprefix tailTrace_2835977
  have hstable : (prefixWord ++ tailWord_2835977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835977).length < 2 ^ (prefixWord ++ tailWord_2835977).sum := by decide
  have hdescent : baseEnd_2835977 < baseStart_2835977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835992 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2835992 : Nat := 118140960795 + 2835992 * 2 ^ 59
def prefixEnd_2835992 : Nat := 4983230072969 + 3 ^ 40 * 2835992 * 2
def baseEnd_2835992 : Nat := 1456227028305773401957517

theorem tailTrace_2835992 : CollatzResearch.WordTrace tailWord_2835992 prefixEnd_2835992 1456227028305773401957517 := by
  unfold tailWord_2835992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718562970846403858863115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68958083961128538478484153 51718562970846403858863115)
  ·
    refine ⟨77577844456269605788294673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51718562970846403858863115 77577844456269605788294673)
    ·
      refine ⟨58183383342202204341221005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77577844456269605788294673 58183383342202204341221005)
      ·
        refine ⟨21818768753325826627957877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58183383342202204341221005 21818768753325826627957877)
        ·
          refine ⟨2045509570624296246371051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21818768753325826627957877 2045509570624296246371051)
          ·
            refine ⟨3068264355936444369556577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045509570624296246371051 3068264355936444369556577)
            ·
              refine ⟨2301198266952333277167433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068264355936444369556577 2301198266952333277167433)
              ·
                refine ⟨1725898700214249957875575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301198266952333277167433 1725898700214249957875575)
                ·
                  refine ⟨2588848050321374936813363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725898700214249957875575 2588848050321374936813363)
                  ·
                    refine ⟨3883272075482062405220045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588848050321374936813363 3883272075482062405220045)
                    ·
                      refine ⟨1456227028305773401957517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883272075482062405220045 1456227028305773401957517)
                      ·
                        rfl

theorem cell23_2835992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2835992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2835992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2835992 prefixEnd_2835992 := by exact prefixLift 2835992
  have htrace : WordTrace (prefixWord ++ tailWord_2835992) baseStart_2835992 baseEnd_2835992 := by
    simpa [prefixWord, tailWord_2835992, baseEnd_2835992] using wordTrace_append hprefix tailTrace_2835992
  have hstable : (prefixWord ++ tailWord_2835992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835992).length < 2 ^ (prefixWord ++ tailWord_2835992).sum := by decide
  have hdescent : baseEnd_2835992 < baseStart_2835992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836057 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2836057 : Nat := 118140960795 + 2836057 * 2 ^ 59
def prefixEnd_2836057 : Nat := 4983230072969 + 3 ^ 40 * 2836057 * 2
def baseEnd_2836057 : Nat := 1456260404548315647644717

theorem tailTrace_2836057 : CollatzResearch.WordTrace tailWord_2836057 prefixEnd_2836057 1456260404548315647644717 := by
  unfold tailWord_2836057
  simp only [CollatzResearch.WordTrace]
  refine ⟨103439496686457323818842425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68959664457638215879228283 103439496686457323818842425)
  ·
    refine ⟨77579622514842992864131819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103439496686457323818842425 77579622514842992864131819)
    ·
      refine ⟨116369433772264489296197729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77579622514842992864131819 116369433772264489296197729)
      ·
        refine ⟨87277075329198366972148297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116369433772264489296197729 87277075329198366972148297)
        ·
          refine ⟨65457806496898775229111223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87277075329198366972148297 65457806496898775229111223)
          ·
            refine ⟨98186709745348162843666835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65457806496898775229111223 98186709745348162843666835)
            ·
              refine ⟨147280064618022244265500253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98186709745348162843666835 147280064618022244265500253)
              ·
                refine ⟨55230024231758341599562595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147280064618022244265500253 55230024231758341599562595)
                ·
                  refine ⟨82845036347637512399343893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55230024231758341599562595 82845036347637512399343893)
                  ·
                    refine ⟨3883361078795508393719245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82845036347637512399343893 3883361078795508393719245)
                    ·
                      refine ⟨1456260404548315647644717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883361078795508393719245 1456260404548315647644717)
                      ·
                        rfl

theorem cell23_2836057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2836057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836057 prefixEnd_2836057 := by exact prefixLift 2836057
  have htrace : WordTrace (prefixWord ++ tailWord_2836057) baseStart_2836057 baseEnd_2836057 := by
    simpa [prefixWord, tailWord_2836057, baseEnd_2836057] using wordTrace_append hprefix tailTrace_2836057
  have hstable : (prefixWord ++ tailWord_2836057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836057).length < 2 ^ (prefixWord ++ tailWord_2836057).sum := by decide
  have hdescent : baseEnd_2836057 < baseStart_2836057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836071 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_2836071 : Nat := 118140960795 + 2836071 * 2 ^ 59
def prefixEnd_2836071 : Nat := 4983230072969 + 3 ^ 40 * 2836071 * 2
def baseEnd_2836071 : Nat := 1456267593277478592869653

theorem tailTrace_2836071 : CollatzResearch.WordTrace tailWord_2836071 prefixEnd_2836071 1456267593277478592869653 := by
  unfold tailWord_2836071
  simp only [CollatzResearch.WordTrace]
  refine ⟨103440007308406604209852067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68960004872271069473234711 103440007308406604209852067)
  ·
    refine ⟨155160010962609906314778101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103440007308406604209852067 155160010962609906314778101)
    ·
      refine ⟨14546251027744678717010447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155160010962609906314778101 14546251027744678717010447)
      ·
        refine ⟨21819376541617018075515671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546251027744678717010447 21819376541617018075515671)
        ·
          refine ⟨32729064812425527113273507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21819376541617018075515671 32729064812425527113273507)
          ·
            refine ⟨49093597218638290669910261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32729064812425527113273507 49093597218638290669910261)
            ·
              refine ⟨4602524739247339750304087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49093597218638290669910261 4602524739247339750304087)
              ·
                refine ⟨6903787108871009625456131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602524739247339750304087 6903787108871009625456131)
                ·
                  refine ⟨10355680663306514438184197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903787108871009625456131 10355680663306514438184197)
                  ·
                    refine ⟨1941690124369971457159537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10355680663306514438184197 1941690124369971457159537)
                    ·
                      refine ⟨1456267593277478592869653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941690124369971457159537 1456267593277478592869653)
                      ·
                        rfl

theorem cell23_2836071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_2836071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836071 prefixEnd_2836071 := by exact prefixLift 2836071
  have htrace : WordTrace (prefixWord ++ tailWord_2836071) baseStart_2836071 baseEnd_2836071 := by
    simpa [prefixWord, tailWord_2836071, baseEnd_2836071] using wordTrace_append hprefix tailTrace_2836071
  have hstable : (prefixWord ++ tailWord_2836071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836071).length < 2 ^ (prefixWord ++ tailWord_2836071).sum := by decide
  have hdescent : baseEnd_2836071 < baseStart_2836071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836141 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2836141 : Nat := 118140960795 + 2836141 * 2 ^ 59
def prefixEnd_2836141 : Nat := 4983230072969 + 3 ^ 40 * 2836141 * 2
def baseEnd_2836141 : Nat := 485434512307764439664777

theorem tailTrace_2836141 : CollatzResearch.WordTrace tailWord_2836141 prefixEnd_2836141 485434512307764439664777 := by
  unfold tailWord_2836141
  simp only [CollatzResearch.WordTrace]
  refine ⟨103442560418153006164900277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68961706945435337443266851 103442560418153006164900277)
  ·
    refine ⟨9697740039201844327959401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103442560418153006164900277 9697740039201844327959401)
    ·
      refine ⟨7273305029401383245969551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9697740039201844327959401 7273305029401383245969551)
      ·
        refine ⟨10909957544102074868954327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273305029401383245969551 10909957544102074868954327)
        ·
          refine ⟨16364936316153112303431491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909957544102074868954327 16364936316153112303431491)
          ·
            refine ⟨24547404474229668455147237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16364936316153112303431491 24547404474229668455147237)
            ·
              refine ⟨4602638338918062835340107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24547404474229668455147237 4602638338918062835340107)
              ·
                refine ⟨6903957508377094253010161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602638338918062835340107 6903957508377094253010161)
                ·
                  refine ⟨5177968131282820689757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6903957508377094253010161 5177968131282820689757621)
                  ·
                    refine ⟨485434512307764439664777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5177968131282820689757621 485434512307764439664777)
                    ·
                      rfl

theorem cell23_2836141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2836141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836141 prefixEnd_2836141 := by exact prefixLift 2836141
  have htrace : WordTrace (prefixWord ++ tailWord_2836141) baseStart_2836141 baseEnd_2836141 := by
    simpa [prefixWord, tailWord_2836141, baseEnd_2836141] using wordTrace_append hprefix tailTrace_2836141
  have hstable : (prefixWord ++ tailWord_2836141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836141).length < 2 ^ (prefixWord ++ tailWord_2836141).sum := by decide
  have hdescent : baseEnd_2836141 < baseStart_2836141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836144 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_2836144 : Nat := 118140960795 + 2836144 * 2 ^ 59
def prefixEnd_2836144 : Nat := 4983230072969 + 3 ^ 40 * 2836144 * 2
def baseEnd_2836144 : Nat := 1456305077365256807256817

theorem tailTrace_2836144 : CollatzResearch.WordTrace tailWord_2836144 prefixEnd_2836144 1456305077365256807256817 := by
  unfold tailWord_2836144
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721334918571068838629743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68961779891428091784839657 51721334918571068838629743)
  ·
    refine ⟨77582002377856603257944615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51721334918571068838629743 77582002377856603257944615)
    ·
      refine ⟨116373003566784904886916923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77582002377856603257944615 116373003566784904886916923)
      ·
        refine ⟨174559505350177357330375385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116373003566784904886916923 174559505350177357330375385)
        ·
          refine ⟨130919629012633017997781539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174559505350177357330375385 130919629012633017997781539)
          ·
            refine ⟨196379443518949526996672309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130919629012633017997781539 196379443518949526996672309)
            ·
              refine ⟨18410572829901518155938029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196379443518949526996672309 18410572829901518155938029)
              ·
                refine ⟨6903964811213069308476761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18410572829901518155938029 6903964811213069308476761)
                ·
                  refine ⟨5177973608409801981357571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6903964811213069308476761 5177973608409801981357571)
                  ·
                    refine ⟨7766960412614702972036357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177973608409801981357571 7766960412614702972036357)
                    ·
                      refine ⟨1456305077365256807256817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7766960412614702972036357 1456305077365256807256817)
                      ·
                        rfl

theorem cell23_2836144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_2836144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836144 prefixEnd_2836144 := by exact prefixLift 2836144
  have htrace : WordTrace (prefixWord ++ tailWord_2836144) baseStart_2836144 baseEnd_2836144 := by
    simpa [prefixWord, tailWord_2836144, baseEnd_2836144] using wordTrace_append hprefix tailTrace_2836144
  have hstable : (prefixWord ++ tailWord_2836144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836144).length < 2 ^ (prefixWord ++ tailWord_2836144).sum := by decide
  have hdescent : baseEnd_2836144 < baseStart_2836144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836162 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2836162 : Nat := 118140960795 + 2836162 * 2 ^ 59
def prefixEnd_2836162 : Nat := 4983230072969 + 3 ^ 40 * 2836162 * 2
def baseEnd_2836162 : Nat := 161812702224115304092415

theorem tailTrace_2836162 : CollatzResearch.WordTrace tailWord_2836162 prefixEnd_2836162 161812702224115304092415 := by
  unfold tailWord_2836162
  simp only [CollatzResearch.WordTrace]
  refine ⟨25860831587769231687853685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68962217567384617834276493 25860831587769231687853685)
  ·
    refine ⟨2424452961353365470736283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25860831587769231687853685 2424452961353365470736283)
    ·
      refine ⟨3636679442030048206104425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424452961353365470736283 3636679442030048206104425)
      ·
        refine ⟨2727509581522536154578319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3636679442030048206104425 2727509581522536154578319)
        ·
          refine ⟨4091264372283804231867479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727509581522536154578319 4091264372283804231867479)
          ·
            refine ⟨6136896558425706347801219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091264372283804231867479 6136896558425706347801219)
            ·
              refine ⟨9205344837638559521701829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136896558425706347801219 9205344837638559521701829)
              ·
                refine ⟨1726002157057229910319093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9205344837638559521701829 1726002157057229910319093)
                ·
                  refine ⟨161812702224115304092415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1726002157057229910319093 161812702224115304092415)
                  ·
                    rfl

theorem cell23_2836162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2836162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836162 prefixEnd_2836162 := by exact prefixLift 2836162
  have htrace : WordTrace (prefixWord ++ tailWord_2836162) baseStart_2836162 baseEnd_2836162 := by
    simpa [prefixWord, tailWord_2836162, baseEnd_2836162] using wordTrace_append hprefix tailTrace_2836162
  have hstable : (prefixWord ++ tailWord_2836162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836162).length < 2 ^ (prefixWord ++ tailWord_2836162).sum := by decide
  have hdescent : baseEnd_2836162 < baseStart_2836162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836164 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2836164 : Nat := 118140960795 + 2836164 * 2 ^ 59
def prefixEnd_2836164 : Nat := 4983230072969 + 3 ^ 40 * 2836164 * 2
def baseEnd_2836164 : Nat := 1456315346978346729006725

theorem tailTrace_2836164 : CollatzResearch.WordTrace tailWord_2836164 prefixEnd_2836164 1456315346978346729006725 := by
  unfold tailWord_2836164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721699648534840546493773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68962266198046454061991697 51721699648534840546493773)
  ·
    refine ⟨19395637368200565204935165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51721699648534840546493773 19395637368200565204935165)
    ·
      refine ⟨7273364013075211951850687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19395637368200565204935165 7273364013075211951850687)
      ·
        refine ⟨10910046019612817927776031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273364013075211951850687 10910046019612817927776031)
        ·
          refine ⟨16365069029419226891664047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10910046019612817927776031 16365069029419226891664047)
          ·
            refine ⟨24547603544128840337496071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16365069029419226891664047 24547603544128840337496071)
            ·
              refine ⟨36821405316193260506244107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24547603544128840337496071 36821405316193260506244107)
              ·
                refine ⟨55232107974289890759366161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36821405316193260506244107 55232107974289890759366161)
                ·
                  refine ⟨41424080980717418069524621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55232107974289890759366161 41424080980717418069524621)
                  ·
                    refine ⟨15534030367769031776071733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41424080980717418069524621 15534030367769031776071733)
                    ·
                      refine ⟨1456315346978346729006725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15534030367769031776071733 1456315346978346729006725)
                      ·
                        rfl

theorem cell23_2836164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2836164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836164 prefixEnd_2836164 := by exact prefixLift 2836164
  have htrace : WordTrace (prefixWord ++ tailWord_2836164) baseStart_2836164 baseEnd_2836164 := by
    simpa [prefixWord, tailWord_2836164, baseEnd_2836164] using wordTrace_append hprefix tailTrace_2836164
  have hstable : (prefixWord ++ tailWord_2836164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836164).length < 2 ^ (prefixWord ++ tailWord_2836164).sum := by decide
  have hdescent : baseEnd_2836164 < baseStart_2836164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836178 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2836178 : Nat := 118140960795 + 2836178 * 2 ^ 59
def prefixEnd_2836178 : Nat := 4983230072969 + 3 ^ 40 * 2836178 * 2
def baseEnd_2836178 : Nat := 1456322535707509674231661

theorem tailTrace_2836178 : CollatzResearch.WordTrace tailWord_2836178 prefixEnd_2836178 1456322535707509674231661 := by
  unfold tailWord_2836178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25860977479754740370999297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68962606612679307655998125 25860977479754740370999297)
  ·
    refine ⟨19395733109816055278249473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25860977479754740370999297 19395733109816055278249473)
    ·
      refine ⟨14546799832362041458687105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19395733109816055278249473 14546799832362041458687105)
      ·
        refine ⟨10910099874271531094015329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14546799832362041458687105 10910099874271531094015329)
        ·
          refine ⟨8182574905703648320511497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910099874271531094015329 8182574905703648320511497)
          ·
            refine ⟨6136931179277736240383623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8182574905703648320511497 6136931179277736240383623)
            ·
              refine ⟨9205396768916604360575435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136931179277736240383623 9205396768916604360575435)
              ·
                refine ⟨13808095153374906540863153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205396768916604360575435 13808095153374906540863153)
                ·
                  refine ⟨10356071365031179905647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13808095153374906540863153 10356071365031179905647365)
                  ·
                    refine ⟨1941763380943346232308881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10356071365031179905647365 1941763380943346232308881)
                    ·
                      refine ⟨1456322535707509674231661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941763380943346232308881 1456322535707509674231661)
                      ·
                        rfl

theorem cell23_2836178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2836178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836178 prefixEnd_2836178 := by exact prefixLift 2836178
  have htrace : WordTrace (prefixWord ++ tailWord_2836178) baseStart_2836178 baseEnd_2836178 := by
    simpa [prefixWord, tailWord_2836178, baseEnd_2836178] using wordTrace_append hprefix tailTrace_2836178
  have hstable : (prefixWord ++ tailWord_2836178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836178).length < 2 ^ (prefixWord ++ tailWord_2836178).sum := by decide
  have hdescent : baseEnd_2836178 < baseStart_2836178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836184 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 6]
def baseStart_2836184 : Nat := 118140960795 + 2836184 * 2 ^ 59
def prefixEnd_2836184 : Nat := 4983230072969 + 3 ^ 40 * 2836184 * 2
def baseEnd_2836184 : Nat := 161813957399048516750737

theorem tailTrace_2836184 : CollatzResearch.WordTrace tailWord_2836184 prefixEnd_2836184 161813957399048516750737 := by
  unfold tailWord_2836184
  simp only [CollatzResearch.WordTrace]
  refine ⟨51722064378498612254357803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68962752504664816339143737 51722064378498612254357803)
  ·
    refine ⟨77583096567747918381536705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51722064378498612254357803 77583096567747918381536705)
    ·
      refine ⟨58187322425810938786152529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77583096567747918381536705 58187322425810938786152529)
      ·
        refine ⟨43640491819358204089614397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58187322425810938786152529 43640491819358204089614397)
        ·
          refine ⟨16365184432259326533605399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43640491819358204089614397 16365184432259326533605399)
          ·
            refine ⟨24547776648388989800408099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16365184432259326533605399 24547776648388989800408099)
            ·
              refine ⟨36821664972583484700612149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24547776648388989800408099 36821664972583484700612149)
              ·
                refine ⟨3452031091179701690682389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36821664972583484700612149 3452031091179701690682389)
                ·
                  refine ⟨161813957399048516750737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3452031091179701690682389 161813957399048516750737)
                  ·
                    rfl

theorem cell23_2836184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_2836184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836184 prefixEnd_2836184 := by exact prefixLift 2836184
  have htrace : WordTrace (prefixWord ++ tailWord_2836184) baseStart_2836184 baseEnd_2836184 := by
    simpa [prefixWord, tailWord_2836184, baseEnd_2836184] using wordTrace_append hprefix tailTrace_2836184
  have hstable : (prefixWord ++ tailWord_2836184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836184).length < 2 ^ (prefixWord ++ tailWord_2836184).sum := by decide
  have hdescent : baseEnd_2836184 < baseStart_2836184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836195 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2836195 : Nat := 118140960795 + 2836195 * 2 ^ 59
def prefixEnd_2836195 : Nat := 4983230072969 + 3 ^ 40 * 2836195 * 2
def baseEnd_2836195 : Nat := 1456331264878636107719083

theorem tailTrace_2836195 : CollatzResearch.WordTrace tailWord_2836195 prefixEnd_2836195 1456331264878636107719083 := by
  unfold tailWord_2836195
  simp only [CollatzResearch.WordTrace]
  refine ⟨103444529959957373387366039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68963019973304915591577359 103444529959957373387366039)
  ·
    refine ⟨155166794939936060081049059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103444529959957373387366039 155166794939936060081049059)
    ·
      refine ⟨232750192409904090121573589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155166794939936060081049059 232750192409904090121573589)
      ·
        refine ⟨5455082634607127112224381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 232750192409904090121573589 5455082634607127112224381)
        ·
          refine ⟨2045655987977672667084143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5455082634607127112224381 2045655987977672667084143)
          ·
            refine ⟨3068483981966509000626215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045655987977672667084143 3068483981966509000626215)
            ·
              refine ⟨4602725972949763500939323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068483981966509000626215 4602725972949763500939323)
              ·
                refine ⟨6904088959424645251408985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602725972949763500939323 6904088959424645251408985)
                ·
                  refine ⟨5178066719568483938556739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904088959424645251408985 5178066719568483938556739)
                  ·
                    refine ⟨7767100079352725907835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5178066719568483938556739 7767100079352725907835109)
                    ·
                      refine ⟨1456331264878636107719083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7767100079352725907835109 1456331264878636107719083)
                      ·
                        rfl

theorem cell23_2836195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2836195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836195 prefixEnd_2836195 := by exact prefixLift 2836195
  have htrace : WordTrace (prefixWord ++ tailWord_2836195) baseStart_2836195 baseEnd_2836195 := by
    simpa [prefixWord, tailWord_2836195, baseEnd_2836195] using wordTrace_append hprefix tailTrace_2836195
  have hstable : (prefixWord ++ tailWord_2836195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836195).length < 2 ^ (prefixWord ++ tailWord_2836195).sum := by decide
  have hdescent : baseEnd_2836195 < baseStart_2836195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836205 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2836205 : Nat := 118140960795 + 2836205 * 2 ^ 59
def prefixEnd_2836205 : Nat := 4983230072969 + 3 ^ 40 * 2836205 * 2
def baseEnd_2836205 : Nat := 485445466561727022864679

theorem tailTrace_2836205 : CollatzResearch.WordTrace tailWord_2836205 prefixEnd_2836205 485445466561727022864679 := by
  unfold tailWord_2836205
  simp only [CollatzResearch.WordTrace]
  refine ⟨103444894689921145095230069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68963263126614096730153379 103444894689921145095230069)
  ·
    refine ⟨9697958877180107352677819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103444894689921145095230069 9697958877180107352677819)
    ·
      refine ⟨14546938315770161029016729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697958877180107352677819 14546938315770161029016729)
      ·
        refine ⟨10910203736827620771762547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14546938315770161029016729 10910203736827620771762547)
        ·
          refine ⟨16365305605241431157643821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10910203736827620771762547 16365305605241431157643821)
          ·
            refine ⟨6136989601965536684116433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16365305605241431157643821 6136989601965536684116433)
            ·
              refine ⟨4602742201474152513087325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136989601965536684116433 4602742201474152513087325)
              ·
                refine ⟨1726028325552807192407747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4602742201474152513087325 1726028325552807192407747)
                ·
                  refine ⟨2589042488329210788611621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726028325552807192407747 2589042488329210788611621)
                  ·
                    refine ⟨485445466561727022864679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589042488329210788611621 485445466561727022864679)
                    ·
                      rfl

theorem cell23_2836205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2836205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836205 prefixEnd_2836205 := by exact prefixLift 2836205
  have htrace : WordTrace (prefixWord ++ tailWord_2836205) baseStart_2836205 baseEnd_2836205 := by
    simpa [prefixWord, tailWord_2836205, baseEnd_2836205] using wordTrace_append hprefix tailTrace_2836205
  have hstable : (prefixWord ++ tailWord_2836205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836205).length < 2 ^ (prefixWord ++ tailWord_2836205).sum := by decide
  have hdescent : baseEnd_2836205 < baseStart_2836205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836228 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2836228 : Nat := 118140960795 + 2836228 * 2 ^ 59
def prefixEnd_2836228 : Nat := 4983230072969 + 3 ^ 40 * 2836228 * 2
def baseEnd_2836228 : Nat := 1456348209740234478606431

theorem tailTrace_2836228 : CollatzResearch.WordTrace tailWord_2836228 prefixEnd_2836228 1456348209740234478606431 := by
  unfold tailWord_2836228
  simp only [CollatzResearch.WordTrace]
  refine ⟨51722866784418910011658669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68963822379225213348878225 51722866784418910011658669)
  ·
    refine ⟨19396075044157091254372001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51722866784418910011658669 19396075044157091254372001)
    ·
      refine ⟨14547056283117818440779001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19396075044157091254372001 14547056283117818440779001)
      ·
        refine ⟨10910292212338363830584251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14547056283117818440779001 10910292212338363830584251)
        ·
          refine ⟨16365438318507545745876377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10910292212338363830584251 16365438318507545745876377)
          ·
            refine ⟨12274078738880659309407283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16365438318507545745876377 12274078738880659309407283)
            ·
              refine ⟨18411118108320988964110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12274078738880659309407283 18411118108320988964110925)
              ·
                refine ⟨6904169290620370861541597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18411118108320988964110925 6904169290620370861541597)
                ·
                  refine ⟨2589063483982639073078099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904169290620370861541597 2589063483982639073078099)
                  ·
                    refine ⟨3883595225973958609617149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589063483982639073078099 3883595225973958609617149)
                    ·
                      refine ⟨1456348209740234478606431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883595225973958609617149 1456348209740234478606431)
                      ·
                        rfl

theorem cell23_2836228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2836228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836228 prefixEnd_2836228 := by exact prefixLift 2836228
  have htrace : WordTrace (prefixWord ++ tailWord_2836228) baseStart_2836228 baseEnd_2836228 := by
    simpa [prefixWord, tailWord_2836228, baseEnd_2836228] using wordTrace_append hprefix tailTrace_2836228
  have hstable : (prefixWord ++ tailWord_2836228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836228).length < 2 ^ (prefixWord ++ tailWord_2836228).sum := by decide
  have hdescent : baseEnd_2836228 < baseStart_2836228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836261 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_2836261 : Nat := 118140960795 + 2836261 * 2 ^ 59
def prefixEnd_2836261 : Nat := 4983230072969 + 3 ^ 40 * 2836261 * 2
def baseEnd_2836261 : Nat := 485455051533944283164593

theorem tailTrace_2836261 : CollatzResearch.WordTrace tailWord_2836261 prefixEnd_2836261 485455051533944283164593 := by
  unfold tailWord_2836261
  simp only [CollatzResearch.WordTrace]
  refine ⟨103446937177718266659268637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68964624785145511106179091 103446937177718266659268637)
  ·
    refine ⟨38792601441644349997225739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103446937177718266659268637 38792601441644349997225739)
    ·
      refine ⟨58188902162466524995838609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38792601441644349997225739 58188902162466524995838609)
      ·
        refine ⟨43641676621849893746878957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58188902162466524995838609 43641676621849893746878957)
        ·
          refine ⟨16365628733193710155079609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43641676621849893746878957 16365628733193710155079609)
          ·
            refine ⟨12274221549895282616309707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16365628733193710155079609 12274221549895282616309707)
            ·
              refine ⟨18411332324842923924464561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12274221549895282616309707 18411332324842923924464561)
              ·
                refine ⟨13808499243632192943348421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18411332324842923924464561 13808499243632192943348421)
                ·
                  refine ⟨2589093608181036176877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13808499243632192943348421 2589093608181036176877829)
                  ·
                    refine ⟨485455051533944283164593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589093608181036176877829 485455051533944283164593)
                    ·
                      rfl

theorem cell23_2836261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_2836261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836261 prefixEnd_2836261 := by exact prefixLift 2836261
  have htrace : WordTrace (prefixWord ++ tailWord_2836261) baseStart_2836261 baseEnd_2836261 := by
    simpa [prefixWord, tailWord_2836261, baseEnd_2836261] using wordTrace_append hprefix tailTrace_2836261
  have hstable : (prefixWord ++ tailWord_2836261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836261).length < 2 ^ (prefixWord ++ tailWord_2836261).sum := by decide
  have hdescent : baseEnd_2836261 < baseStart_2836261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836274 : List Nat := [3, 2, 1, 1, 3, 2, 11]
def baseStart_2836274 : Nat := 118140960795 + 2836274 * 2 ^ 59
def prefixEnd_2836274 : Nat := 4983230072969 + 3 ^ 40 * 2836274 * 2
def baseEnd_2836274 : Nat := 17979899133954830847299

theorem tailTrace_2836274 : CollatzResearch.WordTrace tailWord_2836274 prefixEnd_2836274 17979899133954830847299 := by
  unfold tailWord_2836274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25861852831667792469872969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68964940884447446586327917 25861852831667792469872969)
  ·
    refine ⟨19396389623750844352404727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25861852831667792469872969 19396389623750844352404727)
    ·
      refine ⟨29094584435626266528607091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396389623750844352404727 29094584435626266528607091)
      ·
        refine ⟨43641876653439399792910637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29094584435626266528607091 43641876653439399792910637)
        ·
          refine ⟨16365703745039774922341489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43641876653439399792910637 16365703745039774922341489)
          ·
            refine ⟨12274277808779831191756117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16365703745039774922341489 12274277808779831191756117)
            ·
              refine ⟨17979899133954830847299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12274277808779831191756117 17979899133954830847299)
              ·
                rfl

theorem cell23_2836274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 11].length) (baseStart_2836274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836274 prefixEnd_2836274 := by exact prefixLift 2836274
  have htrace : WordTrace (prefixWord ++ tailWord_2836274) baseStart_2836274 baseEnd_2836274 := by
    simpa [prefixWord, tailWord_2836274, baseEnd_2836274] using wordTrace_append hprefix tailTrace_2836274
  have hstable : (prefixWord ++ tailWord_2836274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836274).length < 2 ^ (prefixWord ++ tailWord_2836274).sum := by decide
  have hdescent : baseEnd_2836274 < baseStart_2836274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836305 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_2836305 : Nat := 118140960795 + 2836305 * 2 ^ 59
def prefixEnd_2836305 : Nat := 4983230072969 + 3 ^ 40 * 2836305 * 2
def baseEnd_2836305 : Nat := 1456387747750630677343577

theorem tailTrace_2836305 : CollatzResearch.WordTrace tailWord_2836305 prefixEnd_2836305 1456387747750630677343577 := by
  unfold tailWord_2836305
  simp only [CollatzResearch.WordTrace]
  refine ⟨103448541989558862173870369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68965694659705908115913579 103448541989558862173870369)
  ·
    refine ⟨77586406492169146630402777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103448541989558862173870369 77586406492169146630402777)
    ·
      refine ⟨58189804869126859972802083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77586406492169146630402777 58189804869126859972802083)
      ·
        refine ⟨87284707303690289959203125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58189804869126859972802083 87284707303690289959203125)
        ·
          refine ⟨8182941309720964683675293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87284707303690289959203125 8182941309720964683675293)
          ·
            refine ⟨3068602991145361756378235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8182941309720964683675293 3068602991145361756378235)
            ·
              refine ⟨4602904486718042634567353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068602991145361756378235 4602904486718042634567353)
              ·
                refine ⟨3452178365038531975925515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602904486718042634567353 3452178365038531975925515)
                ·
                  refine ⟨5178267547557797963888273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452178365038531975925515 5178267547557797963888273)
                  ·
                    refine ⟨3883700660668348472916205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178267547557797963888273 3883700660668348472916205)
                    ·
                      refine ⟨1456387747750630677343577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883700660668348472916205 1456387747750630677343577)
                      ·
                        rfl

theorem cell23_2836305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_2836305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836305 prefixEnd_2836305 := by exact prefixLift 2836305
  have htrace : WordTrace (prefixWord ++ tailWord_2836305) baseStart_2836305 baseEnd_2836305 := by
    simpa [prefixWord, tailWord_2836305, baseEnd_2836305] using wordTrace_append hprefix tailTrace_2836305
  have hstable : (prefixWord ++ tailWord_2836305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836305).length < 2 ^ (prefixWord ++ tailWord_2836305).sum := by decide
  have hdescent : baseEnd_2836305 < baseStart_2836305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836322 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_2836322 : Nat := 118140960795 + 2836322 * 2 ^ 59
def prefixEnd_2836322 : Nat := 4983230072969 + 3 ^ 40 * 2836322 * 2
def baseEnd_2836322 : Nat := 1456396476921757110830999

theorem tailTrace_2836322 : CollatzResearch.WordTrace tailWord_2836322 prefixEnd_2836322 1456396476921757110830999 := by
  unfold tailWord_2836322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25862290507624318519309805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68966108020331516051492813 25862290507624318519309805)
  ·
    refine ⟨9698358940359119444741177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25862290507624318519309805 9698358940359119444741177)
    ·
      refine ⟨7273769205269339583555883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9698358940359119444741177 7273769205269339583555883)
      ·
        refine ⟨10910653807904009375333825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273769205269339583555883 10910653807904009375333825)
        ·
          refine ⟨8182990355928007031500369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910653807904009375333825 8182990355928007031500369)
          ·
            refine ⟨6137242766946005273625277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8182990355928007031500369 6137242766946005273625277)
            ·
              refine ⟨2301466037604751977609479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6137242766946005273625277 2301466037604751977609479)
              ·
                refine ⟨3452199056407127966414219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301466037604751977609479 3452199056407127966414219)
                ·
                  refine ⟨5178298584610691949621329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452199056407127966414219 5178298584610691949621329)
                  ·
                    refine ⟨3883723938458018962215997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178298584610691949621329 3883723938458018962215997)
                    ·
                      refine ⟨1456396476921757110830999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883723938458018962215997 1456396476921757110830999)
                      ·
                        rfl

theorem cell23_2836322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_2836322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836322 prefixEnd_2836322 := by exact prefixLift 2836322
  have htrace : WordTrace (prefixWord ++ tailWord_2836322) baseStart_2836322 baseEnd_2836322 := by
    simpa [prefixWord, tailWord_2836322, baseEnd_2836322] using wordTrace_append hprefix tailTrace_2836322
  have hstable : (prefixWord ++ tailWord_2836322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836322).length < 2 ^ (prefixWord ++ tailWord_2836322).sum := by decide
  have hdescent : baseEnd_2836322 < baseStart_2836322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836341 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2836341 : Nat := 118140960795 + 2836341 * 2 ^ 59
def prefixEnd_2836341 : Nat := 4983230072969 + 3 ^ 40 * 2836341 * 2
def baseEnd_2836341 : Nat := 1456406233054192536493411

theorem tailTrace_2836341 : CollatzResearch.WordTrace tailWord_2836341 prefixEnd_2836341 1456406233054192536493411 := by
  unfold tailWord_2836341
  simp only [CollatzResearch.WordTrace]
  refine ⟨103449855017428440322180877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68966570011618960214787251 103449855017428440322180877)
  ·
    refine ⟨38793695631535665120817829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103449855017428440322180877 38793695631535665120817829)
    ·
      refine ⟨7273817930912937210153343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38793695631535665120817829 7273817930912937210153343)
      ·
        refine ⟨10910726896369405815230015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273817930912937210153343 10910726896369405815230015)
        ·
          refine ⟨16366090344554108722845023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10910726896369405815230015 16366090344554108722845023)
          ·
            refine ⟨24549135516831163084267535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16366090344554108722845023 24549135516831163084267535)
            ·
              refine ⟨36823703275246744626401303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24549135516831163084267535 36823703275246744626401303)
              ·
                refine ⟨55235554912870116939601955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36823703275246744626401303 55235554912870116939601955)
                ·
                  refine ⟨82853332369305175409402933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55235554912870116939601955 82853332369305175409402933)
                  ·
                    refine ⟨7767499909622360194631525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82853332369305175409402933 7767499909622360194631525)
                    ·
                      refine ⟨1456406233054192536493411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7767499909622360194631525 1456406233054192536493411)
                      ·
                        rfl

theorem cell23_2836341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2836341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836341 prefixEnd_2836341 := by exact prefixLift 2836341
  have htrace : WordTrace (prefixWord ++ tailWord_2836341) baseStart_2836341 baseEnd_2836341 := by
    simpa [prefixWord, tailWord_2836341, baseEnd_2836341] using wordTrace_append hprefix tailTrace_2836341
  have hstable : (prefixWord ++ tailWord_2836341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836341).length < 2 ^ (prefixWord ++ tailWord_2836341).sum := by decide
  have hdescent : baseEnd_2836341 < baseStart_2836341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836361 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_2836361 : Nat := 118140960795 + 2836361 * 2 ^ 59
def prefixEnd_2836361 : Nat := 4983230072969 + 3 ^ 40 * 2836361 * 2
def baseEnd_2836361 : Nat := 1456416502667282458243319

theorem tailTrace_2836361 : CollatzResearch.WordTrace tailWord_2836361 prefixEnd_2836361 1456416502667282458243319 := by
  unfold tailWord_2836361
  simp only [CollatzResearch.WordTrace]
  refine ⟨103450584477355983737908937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68967056318237322491939291 103450584477355983737908937)
  ·
    refine ⟨77587938358016987803431703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103450584477355983737908937 77587938358016987803431703)
    ·
      refine ⟨116381907537025481705147555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77587938358016987803431703 116381907537025481705147555)
      ·
        refine ⟨174572861305538222557721333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116381907537025481705147555 174572861305538222557721333)
        ·
          refine ⟨16366205747394208364786375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174572861305538222557721333 16366205747394208364786375)
          ·
            refine ⟨24549308621091312547179563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16366205747394208364786375 24549308621091312547179563)
            ·
              refine ⟨36823962931636968820769345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24549308621091312547179563 36823962931636968820769345)
              ·
                refine ⟨27617972198727726615577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36823962931636968820769345 27617972198727726615577009)
                ·
                  refine ⟨20713479149045794961682757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27617972198727726615577009 20713479149045794961682757)
                  ·
                    refine ⟨3883777340446086555315517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20713479149045794961682757 3883777340446086555315517)
                    ·
                      refine ⟨1456416502667282458243319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883777340446086555315517 1456416502667282458243319)
                      ·
                        rfl

theorem cell23_2836361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_2836361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836361 prefixEnd_2836361 := by exact prefixLift 2836361
  have htrace : WordTrace (prefixWord ++ tailWord_2836361) baseStart_2836361 baseEnd_2836361 := by
    simpa [prefixWord, tailWord_2836361, baseEnd_2836361] using wordTrace_append hprefix tailTrace_2836361
  have hstable : (prefixWord ++ tailWord_2836361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836361).length < 2 ^ (prefixWord ++ tailWord_2836361).sum := by decide
  have hdescent : baseEnd_2836361 < baseStart_2836361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836431 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_2836431 : Nat := 118140960795 + 2836431 * 2 ^ 59
def prefixEnd_2836431 : Nat := 4983230072969 + 3 ^ 40 * 2836431 * 2
def baseEnd_2836431 : Nat := 1456452446313097184367997

theorem tailTrace_2836431 : CollatzResearch.WordTrace tailWord_2836431 prefixEnd_2836431 1456452446313097184367997 := by
  unfold tailWord_2836431
  simp only [CollatzResearch.WordTrace]
  refine ⟨103453137587102385692957147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68968758391401590461971431 103453137587102385692957147)
  ·
    refine ⟨155179706380653578539435721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103453137587102385692957147 155179706380653578539435721)
    ·
      refine ⟨116384779785490183904576791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155179706380653578539435721 116384779785490183904576791)
      ·
        refine ⟨174577169678235275856865187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116384779785490183904576791 174577169678235275856865187)
        ·
          refine ⟨261865754517352913785297781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174577169678235275856865187 261865754517352913785297781)
          ·
            refine ⟨24549914486001835667371667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261865754517352913785297781 24549914486001835667371667)
            ·
              refine ⟨36824871729002753501057501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24549914486001835667371667 36824871729002753501057501)
              ·
                refine ⟨13809326898376032562896563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36824871729002753501057501 13809326898376032562896563)
                ·
                  refine ⟨20713990347564048844344845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13809326898376032562896563 20713990347564048844344845)
                  ·
                    refine ⟨7767746380336518316629317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20713990347564048844344845 7767746380336518316629317)
                    ·
                      refine ⟨1456452446313097184367997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7767746380336518316629317 1456452446313097184367997)
                      ·
                        rfl

theorem cell23_2836431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_2836431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836431 prefixEnd_2836431 := by exact prefixLift 2836431
  have htrace : WordTrace (prefixWord ++ tailWord_2836431) baseStart_2836431 baseEnd_2836431 := by
    simpa [prefixWord, tailWord_2836431, baseEnd_2836431] using wordTrace_append hprefix tailTrace_2836431
  have hstable : (prefixWord ++ tailWord_2836431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836431).length < 2 ^ (prefixWord ++ tailWord_2836431).sum := by decide
  have hdescent : baseEnd_2836431 < baseStart_2836431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836445 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2836445 : Nat := 118140960795 + 2836445 * 2 ^ 59
def prefixEnd_2836445 : Nat := 4983230072969 + 3 ^ 40 * 2836445 * 2
def baseEnd_2836445 : Nat := 485486545014086709864311

theorem tailTrace_2836445 : CollatzResearch.WordTrace tailWord_2836445 prefixEnd_2836445 485486545014086709864311 := by
  unfold tailWord_2836445
  simp only [CollatzResearch.WordTrace]
  refine ⟨103453648209051666083966789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68969098806034444055977859 103453648209051666083966789)
  ·
    refine ⟨19397559039197187390743773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103453648209051666083966789 19397559039197187390743773)
    ·
      refine ⟨7274084639698945271528915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19397559039197187390743773 7274084639698945271528915)
      ·
        refine ⟨10911126959548417907293373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7274084639698945271528915 10911126959548417907293373)
        ·
          refine ⟨4091672609830656715235015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10911126959548417907293373 4091672609830656715235015)
          ·
            refine ⟨6137508914745985072852523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091672609830656715235015 6137508914745985072852523)
            ·
              refine ⟨9206263372118977609278785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137508914745985072852523 9206263372118977609278785)
              ·
                refine ⟨6904697529089233206959089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9206263372118977609278785 6904697529089233206959089)
                ·
                  refine ⟨5178523146816924905219317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904697529089233206959089 5178523146816924905219317)
                  ·
                    refine ⟨485486545014086709864311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5178523146816924905219317 485486545014086709864311)
                    ·
                      rfl

theorem cell23_2836445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2836445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836445 prefixEnd_2836445 := by exact prefixLift 2836445
  have htrace : WordTrace (prefixWord ++ tailWord_2836445) baseStart_2836445 baseEnd_2836445 := by
    simpa [prefixWord, tailWord_2836445, baseEnd_2836445] using wordTrace_append hprefix tailTrace_2836445
  have hstable : (prefixWord ++ tailWord_2836445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836445).length < 2 ^ (prefixWord ++ tailWord_2836445).sum := by decide
  have hdescent : baseEnd_2836445 < baseStart_2836445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2]
def baseStart_2836448 : Nat := 118140960795 + 2836448 * 2 ^ 59
def prefixEnd_2836448 : Nat := 4983230072969 + 3 ^ 40 * 2836448 * 2
def baseEnd_2836448 : Nat := 1456461175484223617855419

theorem tailTrace_2836448 : CollatzResearch.WordTrace tailWord_2836448 prefixEnd_2836448 1456461175484223617855419 := by
  unfold tailWord_2836448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51726878814020398798162999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68969171752027198397550665 51726878814020398798162999)
  ·
    refine ⟨77590318221030598197244499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51726878814020398798162999 77590318221030598197244499)
    ·
      refine ⟨116385477331545897295866749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77590318221030598197244499 116385477331545897295866749)
      ·
        refine ⟨43644553999329711485950031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116385477331545897295866749 43644553999329711485950031)
        ·
          refine ⟨65466830998994567228925047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43644553999329711485950031 65466830998994567228925047)
          ·
            refine ⟨98200246498491850843387571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65466830998994567228925047 98200246498491850843387571)
            ·
              refine ⟨147300369747737776265081357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98200246498491850843387571 147300369747737776265081357)
              ·
                refine ⟨55237638655401666099405509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147300369747737776265081357 55237638655401666099405509)
                ·
                  refine ⟨10357057247887812393638533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55237638655401666099405509 10357057247887812393638533)
                  ·
                    refine ⟨1941948233978964823807225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10357057247887812393638533 1941948233978964823807225)
                    ·
                      refine ⟨1456461175484223617855419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1941948233978964823807225 1456461175484223617855419)
                      ·
                        rfl

theorem cell23_2836448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_2836448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836448 prefixEnd_2836448 := by exact prefixLift 2836448
  have htrace : WordTrace (prefixWord ++ tailWord_2836448) baseStart_2836448 baseEnd_2836448 := by
    simpa [prefixWord, tailWord_2836448, baseEnd_2836448] using wordTrace_append hprefix tailTrace_2836448
  have hstable : (prefixWord ++ tailWord_2836448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836448).length < 2 ^ (prefixWord ++ tailWord_2836448).sum := by decide
  have hdescent : baseEnd_2836448 < baseStart_2836448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836485 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_2836485 : Nat := 118140960795 + 2836485 * 2 ^ 59
def prefixEnd_2836485 : Nat := 4983230072969 + 3 ^ 40 * 2836485 * 2
def baseEnd_2836485 : Nat := 1456480174268439973092749

theorem tailTrace_2836485 : CollatzResearch.WordTrace tailWord_2836485 prefixEnd_2836485 1456480174268439973092749 := by
  unfold tailWord_2836485
  simp only [CollatzResearch.WordTrace]
  refine ⟨103455107128906752915422909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68970071419271168610281939 103455107128906752915422909)
  ·
    refine ⟨38795665173340032343283591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103455107128906752915422909 38795665173340032343283591)
    ·
      refine ⟨58193497760010048514925387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38795665173340032343283591 58193497760010048514925387)
      ·
        refine ⟨87290246640015072772388081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58193497760010048514925387 87290246640015072772388081)
        ·
          refine ⟨65467684980011304579291061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87290246640015072772388081 65467684980011304579291061)
          ·
            refine ⟨6137595466876059804308537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65467684980011304579291061 6137595466876059804308537)
            ·
              refine ⟨4603196600157044853231403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137595466876059804308537 4603196600157044853231403)
              ·
                refine ⟨6904794900235567279847105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603196600157044853231403 6904794900235567279847105)
                ·
                  refine ⟨5178596175176675459885329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904794900235567279847105 5178596175176675459885329)
                  ·
                    refine ⟨3883947131382506594913997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178596175176675459885329 3883947131382506594913997)
                    ·
                      refine ⟨1456480174268439973092749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883947131382506594913997 1456480174268439973092749)
                      ·
                        rfl

theorem cell23_2836485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_2836485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836485 prefixEnd_2836485 := by exact prefixLift 2836485
  have htrace : WordTrace (prefixWord ++ tailWord_2836485) baseStart_2836485 baseEnd_2836485 := by
    simpa [prefixWord, tailWord_2836485, baseEnd_2836485] using wordTrace_append hprefix tailTrace_2836485
  have hstable : (prefixWord ++ tailWord_2836485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836485).length < 2 ^ (prefixWord ++ tailWord_2836485).sum := by decide
  have hdescent : baseEnd_2836485 < baseStart_2836485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836509 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2836509 : Nat := 118140960795 + 2836509 * 2 ^ 59
def prefixEnd_2836509 : Nat := 4983230072969 + 3 ^ 40 * 2836509 * 2
def baseEnd_2836509 : Nat := 485497499268049293064213

theorem tailTrace_2836509 : CollatzResearch.WordTrace tailWord_2836509 prefixEnd_2836509 485497499268049293064213 := by
  unfold tailWord_2836509
  simp only [CollatzResearch.WordTrace]
  refine ⟨103455982480819805014296581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68970654987213203342864387 103455982480819805014296581)
  ·
    refine ⟨19397996715153713440180609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103455982480819805014296581 19397996715153713440180609)
    ·
      refine ⟨14548497536365285080135457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19397996715153713440180609 14548497536365285080135457)
      ·
        refine ⟨10911373152273963810101593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14548497536365285080135457 10911373152273963810101593)
        ·
          refine ⟨8183529864205472857576195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10911373152273963810101593 8183529864205472857576195)
          ·
            refine ⟨12275294796308209286364293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8183529864205472857576195 12275294796308209286364293)
            ·
              refine ⟨2301617774307789241193305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12275294796308209286364293 2301617774307789241193305)
              ·
                refine ⟨1726213330730841930894979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301617774307789241193305 1726213330730841930894979)
                ·
                  refine ⟨2589319996096262896342469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726213330730841930894979 2589319996096262896342469)
                  ·
                    refine ⟨485497499268049293064213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589319996096262896342469 485497499268049293064213)
                    ·
                      rfl

theorem cell23_2836509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2836509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836509 prefixEnd_2836509 := by exact prefixLift 2836509
  have htrace : WordTrace (prefixWord ++ tailWord_2836509) baseStart_2836509 baseEnd_2836509 := by
    simpa [prefixWord, tailWord_2836509, baseEnd_2836509] using wordTrace_append hprefix tailTrace_2836509
  have hstable : (prefixWord ++ tailWord_2836509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836509).length < 2 ^ (prefixWord ++ tailWord_2836509).sum := by decide
  have hdescent : baseEnd_2836509 < baseStart_2836509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836515 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 3]
def baseStart_2836515 : Nat := 118140960795 + 2836515 * 2 ^ 59
def prefixEnd_2836515 : Nat := 4983230072969 + 3 ^ 40 * 2836515 * 2
def baseEnd_2836515 : Nat := 1456495578688074855717611

theorem tailTrace_2836515 : CollatzResearch.WordTrace tailWord_2836515 prefixEnd_2836515 1456495578688074855717611 := by
  unfold tailWord_2836515
  simp only [CollatzResearch.WordTrace]
  refine ⟨103456201318798068039014999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68970800879198712026009999 103456201318798068039014999)
  ·
    refine ⟨155184301978197102058522499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103456201318798068039014999 155184301978197102058522499)
    ·
      refine ⟨232776452967295653087783749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155184301978197102058522499 232776452967295653087783749)
      ·
        refine ⟨43645584931367934953959453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232776452967295653087783749 43645584931367934953959453)
        ·
          refine ⟨16367094349262975607734795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43645584931367934953959453 16367094349262975607734795)
          ·
            refine ⟨24550641523894463411602193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16367094349262975607734795 24550641523894463411602193)
            ·
              refine ⟨18412981142920847558701645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24550641523894463411602193 18412981142920847558701645)
              ·
                refine ⟨6904867928595317834513117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18412981142920847558701645 6904867928595317834513117)
                ·
                  refine ⟨2589325473223244187942419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904867928595317834513117 2589325473223244187942419)
                  ·
                    refine ⟨3883988209834866281913629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589325473223244187942419 3883988209834866281913629)
                    ·
                      refine ⟨1456495578688074855717611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3883988209834866281913629 1456495578688074855717611)
                      ·
                        rfl

theorem cell23_2836515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_2836515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836515 prefixEnd_2836515 := by exact prefixLift 2836515
  have htrace : WordTrace (prefixWord ++ tailWord_2836515) baseStart_2836515 baseEnd_2836515 := by
    simpa [prefixWord, tailWord_2836515, baseEnd_2836515] using wordTrace_append hprefix tailTrace_2836515
  have hstable : (prefixWord ++ tailWord_2836515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836515).length < 2 ^ (prefixWord ++ tailWord_2836515).sum := by decide
  have hdescent : baseEnd_2836515 < baseStart_2836515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836565 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2836565 : Nat := 118140960795 + 2836565 * 2 ^ 59
def prefixEnd_2836565 : Nat := 4983230072969 + 3 ^ 40 * 2836565 * 2
def baseEnd_2836565 : Nat := 485507084240266553364127

theorem tailTrace_2836565 : CollatzResearch.WordTrace tailWord_2836565 prefixEnd_2836565 485507084240266553364127 := by
  unfold tailWord_2836565
  simp only [CollatzResearch.WordTrace]
  refine ⟨103458024968616926578335149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68972016645744617718890099 103458024968616926578335149)
  ·
    refine ⟨38796759363231347466875681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103458024968616926578335149 38796759363231347466875681)
    ·
      refine ⟨29097569522423510600156761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38796759363231347466875681 29097569522423510600156761)
      ·
        refine ⟨21823177141817632950117571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29097569522423510600156761 21823177141817632950117571)
        ·
          refine ⟨32734765712726449425176357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21823177141817632950117571 32734765712726449425176357)
          ·
            refine ⟨6137768571136209267220567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32734765712726449425176357 6137768571136209267220567)
            ·
              refine ⟨9206652856704313900830851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137768571136209267220567 9206652856704313900830851)
              ·
                refine ⟨13809979285056470851246277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206652856704313900830851 13809979285056470851246277)
                ·
                  refine ⟨2589371115948088284608677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13809979285056470851246277 2589371115948088284608677)
                  ·
                    refine ⟨485507084240266553364127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589371115948088284608677 485507084240266553364127)
                    ·
                      rfl

theorem cell23_2836565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2836565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836565 prefixEnd_2836565 := by exact prefixLift 2836565
  have htrace : WordTrace (prefixWord ++ tailWord_2836565) baseStart_2836565 baseEnd_2836565 := by
    simpa [prefixWord, tailWord_2836565, baseEnd_2836565] using wordTrace_append hprefix tailTrace_2836565
  have hstable : (prefixWord ++ tailWord_2836565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836565).length < 2 ^ (prefixWord ++ tailWord_2836565).sum := by decide
  have hdescent : baseEnd_2836565 < baseStart_2836565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836566 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2836566 : Nat := 118140960795 + 2836566 * 2 ^ 59
def prefixEnd_2836566 : Nat := 4983230072969 + 3 ^ 40 * 2836566 * 2
def baseEnd_2836566 : Nat := 1456521766201454156179877

theorem tailTrace_2836566 : CollatzResearch.WordTrace tailWord_2836566 prefixEnd_2836566 1456521766201454156179877 := by
  unfold tailWord_2836566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466128840100831484320097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68972040961075535832747701 6466128840100831484320097)
  ·
    refine ⟨4849596630075623613240073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6466128840100831484320097 4849596630075623613240073)
    ·
      refine ⟨3637197472556717709930055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4849596630075623613240073 3637197472556717709930055)
      ·
        refine ⟨5455796208835076564895083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637197472556717709930055 5455796208835076564895083)
        ·
          refine ⟨8183694313252614847342625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455796208835076564895083 8183694313252614847342625)
          ·
            refine ⟨6137770734939461135506969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8183694313252614847342625 6137770734939461135506969)
            ·
              refine ⟨4603328051204595851630227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137770734939461135506969 4603328051204595851630227)
              ·
                refine ⟨6904992076806893777445341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603328051204595851630227 6904992076806893777445341)
                ·
                  refine ⟨2589372028802585166542003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904992076806893777445341 2589372028802585166542003)
                  ·
                    refine ⟨3884058043203877749813005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589372028802585166542003 3884058043203877749813005)
                    ·
                      refine ⟨1456521766201454156179877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884058043203877749813005 1456521766201454156179877)
                      ·
                        rfl

theorem cell23_2836566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2836566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836566 prefixEnd_2836566 := by exact prefixLift 2836566
  have htrace : WordTrace (prefixWord ++ tailWord_2836566) baseStart_2836566 baseEnd_2836566 := by
    simpa [prefixWord, tailWord_2836566, baseEnd_2836566] using wordTrace_append hprefix tailTrace_2836566
  have hstable : (prefixWord ++ tailWord_2836566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836566).length < 2 ^ (prefixWord ++ tailWord_2836566).sum := by decide
  have hdescent : baseEnd_2836566 < baseStart_2836566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836592 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_2836592 : Nat := 118140960795 + 2836592 * 2 ^ 59
def prefixEnd_2836592 : Nat := 4983230072969 + 3 ^ 40 * 2836592 * 2
def baseEnd_2836592 : Nat := 1456535116698471054454757

theorem tailTrace_2836592 : CollatzResearch.WordTrace tailWord_2836592 prefixEnd_2836592 1456535116698471054454757 := by
  unfold tailWord_2836592
  simp only [CollatzResearch.WordTrace]
  refine ⟨51729504869759555094784015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68972673159679406793045353 51729504869759555094784015)
  ·
    refine ⟨77594257304639332642176023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51729504869759555094784015 77594257304639332642176023)
    ·
      refine ⟨116391385956958998963264035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77594257304639332642176023 116391385956958998963264035)
      ·
        refine ⟨174587078935438498444896053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116391385956958998963264035 174587078935438498444896053)
        ·
          refine ⟨16367538650197359229209005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174587078935438498444896053 16367538650197359229209005)
          ·
            refine ⟨6137826993824009710953377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16367538650197359229209005 6137826993824009710953377)
            ·
              refine ⟨4603370245368007283215033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137826993824009710953377 4603370245368007283215033)
              ·
                refine ⟨3452527684026005462411275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603370245368007283215033 3452527684026005462411275)
                ·
                  refine ⟨5178791526039008193616913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452527684026005462411275 5178791526039008193616913)
                  ·
                    refine ⟨3884093644529256145212685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178791526039008193616913 3884093644529256145212685)
                    ·
                      refine ⟨1456535116698471054454757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884093644529256145212685 1456535116698471054454757)
                      ·
                        rfl

theorem cell23_2836592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_2836592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836592 prefixEnd_2836592 := by exact prefixLift 2836592
  have htrace : WordTrace (prefixWord ++ tailWord_2836592) baseStart_2836592 baseEnd_2836592 := by
    simpa [prefixWord, tailWord_2836592, baseEnd_2836592] using wordTrace_append hprefix tailTrace_2836592
  have hstable : (prefixWord ++ tailWord_2836592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836592).length < 2 ^ (prefixWord ++ tailWord_2836592).sum := by decide
  have hdescent : baseEnd_2836592 < baseStart_2836592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836639 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2836639 : Nat := 118140960795 + 2836639 * 2 ^ 59
def prefixEnd_2836639 : Nat := 4983230072969 + 3 ^ 40 * 2836639 * 2
def baseEnd_2836639 : Nat := 1456559250289232370567041

theorem tailTrace_2836639 : CollatzResearch.WordTrace tailWord_2836639 prefixEnd_2836639 1456559250289232370567041 := by
  unfold tailWord_2836639
  simp only [CollatzResearch.WordTrace]
  refine ⟨103460723970348837216528971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68973815980232558144352647 103460723970348837216528971)
  ·
    refine ⟨155191085955523255824793457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103460723970348837216528971 155191085955523255824793457)
    ·
      refine ⟨116393314466642441868595093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155191085955523255824793457 116393314466642441868595093)
      ·
        refine ⟨5455936615623864462590395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116393314466642441868595093 5455936615623864462590395)
        ·
          refine ⟨8183904923435796693885593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455936615623864462590395 8183904923435796693885593)
          ·
            refine ⟨6137928692576847520414195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8183904923435796693885593 6137928692576847520414195)
            ·
              refine ⟨9206893038865271280621293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137928692576847520414195 9206893038865271280621293)
              ·
                refine ⟨3452584889574476730232985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9206893038865271280621293 3452584889574476730232985)
                ·
                  refine ⟨2589438667180857547674739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452584889574476730232985 2589438667180857547674739)
                  ·
                    refine ⟨3884158000771286321512109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589438667180857547674739 3884158000771286321512109)
                    ·
                      refine ⟨1456559250289232370567041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884158000771286321512109 1456559250289232370567041)
                      ·
                        rfl

theorem cell23_2836639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2836639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836639 prefixEnd_2836639 := by exact prefixLift 2836639
  have htrace : WordTrace (prefixWord ++ tailWord_2836639) baseStart_2836639 baseEnd_2836639 := by
    simpa [prefixWord, tailWord_2836639, baseEnd_2836639] using wordTrace_append hprefix tailTrace_2836639
  have hstable : (prefixWord ++ tailWord_2836639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836639).length < 2 ^ (prefixWord ++ tailWord_2836639).sum := by decide
  have hdescent : baseEnd_2836639 < baseStart_2836639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836660 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2836660 : Nat := 118140960795 + 2836660 * 2 ^ 59
def prefixEnd_2836660 : Nat := 4983230072969 + 3 ^ 40 * 2836660 * 2
def baseEnd_2836660 : Nat := 1456570033382976788404445

theorem tailTrace_2836660 : CollatzResearch.WordTrace tailWord_2836660 prefixEnd_2836660 1456570033382976788404445 := by
  unfold tailWord_2836660
  simp only [CollatzResearch.WordTrace]
  refine ⟨51730744951636378901521717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68974326602181838535362289 51730744951636378901521717)
  ·
    refine ⟨4849757339215910522017661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51730744951636378901521717 4849757339215910522017661)
    ·
      refine ⟨1818659002205966445756623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4849757339215910522017661 1818659002205966445756623)
      ·
        refine ⟨2727988503308949668634935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818659002205966445756623 2727988503308949668634935)
        ·
          refine ⟨4091982754963424502952403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727988503308949668634935 4091982754963424502952403)
          ·
            refine ⟨6137974132445136754428605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091982754963424502952403 6137974132445136754428605)
            ·
              refine ⟨2301740299666926282910727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6137974132445136754428605 2301740299666926282910727)
              ·
                refine ⟨3452610449500389424366091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301740299666926282910727 3452610449500389424366091)
                ·
                  refine ⟨5178915674250584136549137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452610449500389424366091 5178915674250584136549137)
                  ·
                    refine ⟨3884186755687938102411853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178915674250584136549137 3884186755687938102411853)
                    ·
                      refine ⟨1456570033382976788404445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884186755687938102411853 1456570033382976788404445)
                      ·
                        rfl

theorem cell23_2836660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2836660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836660 prefixEnd_2836660 := by exact prefixLift 2836660
  have htrace : WordTrace (prefixWord ++ tailWord_2836660) baseStart_2836660 baseEnd_2836660 := by
    simpa [prefixWord, tailWord_2836660, baseEnd_2836660] using wordTrace_append hprefix tailTrace_2836660
  have hstable : (prefixWord ++ tailWord_2836660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836660).length < 2 ^ (prefixWord ++ tailWord_2836660).sum := by decide
  have hdescent : baseEnd_2836660 < baseStart_2836660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836728 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_2836728 : Nat := 118140960795 + 2836728 * 2 ^ 59
def prefixEnd_2836728 : Nat := 4983230072969 + 3 ^ 40 * 2836728 * 2
def baseEnd_2836728 : Nat := 485534983355827507451377

theorem tailTrace_2836728 : CollatzResearch.WordTrace tailWord_2836728 prefixEnd_2836728 485534983355827507451377 := by
  unfold tailWord_2836728
  simp only [CollatzResearch.WordTrace]
  refine ⟨51731985033513202708259419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68975980044684270277679225 51731985033513202708259419)
  ·
    refine ⟨77597977550269804062389129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51731985033513202708259419 77597977550269804062389129)
    ·
      refine ⟨58198483162702353046791847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77597977550269804062389129 58198483162702353046791847)
      ·
        refine ⟨87297724744053529570187771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58198483162702353046791847 87297724744053529570187771)
        ·
          refine ⟨130946587116080294355281657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87297724744053529570187771 130946587116080294355281657)
          ·
            refine ⟨98209940337060220766461243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130946587116080294355281657 98209940337060220766461243)
            ·
              refine ⟨147314910505590331149691865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98209940337060220766461243 147314910505590331149691865)
              ·
                refine ⟨110486182879192748362268899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147314910505590331149691865 110486182879192748362268899)
                ·
                  refine ⟨165729274318789122543403349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110486182879192748362268899 165729274318789122543403349)
                  ·
                    refine ⟨485534983355827507451377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 165729274318789122543403349 485534983355827507451377)
                    ·
                      rfl

theorem cell23_2836728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_2836728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836728 prefixEnd_2836728 := by exact prefixLift 2836728
  have htrace : WordTrace (prefixWord ++ tailWord_2836728) baseStart_2836728 baseEnd_2836728 := by
    simpa [prefixWord, tailWord_2836728, baseEnd_2836728] using wordTrace_append hprefix tailTrace_2836728
  have hstable : (prefixWord ++ tailWord_2836728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836728).length < 2 ^ (prefixWord ++ tailWord_2836728).sum := by decide
  have hdescent : baseEnd_2836728 < baseStart_2836728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836735 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_2836735 : Nat := 118140960795 + 2836735 * 2 ^ 59
def prefixEnd_2836735 : Nat := 4983230072969 + 3 ^ 40 * 2836735 * 2
def baseEnd_2836735 : Nat := 1456608544432063994966599

theorem tailTrace_2836735 : CollatzResearch.WordTrace tailWord_2836735 prefixEnd_2836735 1456608544432063994966599 := by
  unfold tailWord_2836735
  simp only [CollatzResearch.WordTrace]
  refine ⟨103464225378001045612023659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68976150252000697074682439 103464225378001045612023659)
  ·
    refine ⟨155196338067001568418035489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103464225378001045612023659 155196338067001568418035489)
    ·
      refine ⟨116397253550251176313526617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155196338067001568418035489 116397253550251176313526617)
      ·
        refine ⟨87297940162688382235144963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116397253550251176313526617 87297940162688382235144963)
        ·
          refine ⟨130946910244032573352717445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87297940162688382235144963 130946910244032573352717445)
          ·
            refine ⟨24552545670756107503634521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130946910244032573352717445 24552545670756107503634521)
            ·
              refine ⟨18414409253067080627725891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24552545670756107503634521 18414409253067080627725891)
              ·
                refine ⟨27621613879600620941588837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18414409253067080627725891 27621613879600620941588837)
                ·
                  refine ⟨5179052602425116426547907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27621613879600620941588837 5179052602425116426547907)
                  ·
                    refine ⟨7768578903637674639821861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179052602425116426547907 7768578903637674639821861)
                    ·
                      refine ⟨1456608544432063994966599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7768578903637674639821861 1456608544432063994966599)
                      ·
                        rfl

theorem cell23_2836735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_2836735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836735 prefixEnd_2836735 := by exact prefixLift 2836735
  have htrace : WordTrace (prefixWord ++ tailWord_2836735) baseStart_2836735 baseEnd_2836735 := by
    simpa [prefixWord, tailWord_2836735, baseEnd_2836735] using wordTrace_append hprefix tailTrace_2836735
  have hstable : (prefixWord ++ tailWord_2836735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836735).length < 2 ^ (prefixWord ++ tailWord_2836735).sum := by decide
  have hdescent : baseEnd_2836735 < baseStart_2836735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836772 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2836772 : Nat := 118140960795 + 2836772 * 2 ^ 59
def prefixEnd_2836772 : Nat := 4983230072969 + 3 ^ 40 * 2836772 * 2
def baseEnd_2836772 : Nat := 1456627543216280350203929

theorem tailTrace_2836772 : CollatzResearch.WordTrace tailWord_2836772 prefixEnd_2836772 1456627543216280350203929 := by
  unfold tailWord_2836772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51732787439433500465560285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68977049919244667287413713 51732787439433500465560285)
  ·
    refine ⟨19399795289787562674585107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51732787439433500465560285 19399795289787562674585107)
    ·
      refine ⟨29099692934681344011877661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399795289787562674585107 29099692934681344011877661)
      ·
        refine ⟨10912384850505504004454123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29099692934681344011877661 10912384850505504004454123)
        ·
          refine ⟨16368577275758256006681185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10912384850505504004454123 16368577275758256006681185)
          ·
            refine ⟨12276432956818692005010889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16368577275758256006681185 12276432956818692005010889)
            ·
              refine ⟨9207324717614019003758167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12276432956818692005010889 9207324717614019003758167)
              ·
                refine ⟨13810987076421028505637251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207324717614019003758167 13810987076421028505637251)
                ·
                  refine ⟨20716480614631542758455877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13810987076421028505637251 20716480614631542758455877)
                  ·
                    refine ⟨3884340115243414267210477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20716480614631542758455877 3884340115243414267210477)
                    ·
                      refine ⟨1456627543216280350203929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884340115243414267210477 1456627543216280350203929)
                      ·
                        rfl

theorem cell23_2836772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2836772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836772 prefixEnd_2836772 := by exact prefixLift 2836772
  have htrace : WordTrace (prefixWord ++ tailWord_2836772) baseStart_2836772 baseEnd_2836772 := by
    simpa [prefixWord, tailWord_2836772, baseEnd_2836772] using wordTrace_append hprefix tailTrace_2836772
  have hstable : (prefixWord ++ tailWord_2836772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836772).length < 2 ^ (prefixWord ++ tailWord_2836772).sum := by decide
  have hdescent : baseEnd_2836772 < baseStart_2836772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836796 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_2836796 : Nat := 118140960795 + 2836796 * 2 ^ 59
def prefixEnd_2836796 : Nat := 4983230072969 + 3 ^ 40 * 2836796 * 2
def baseEnd_2836796 : Nat := 485546622250662752101273

theorem tailTrace_2836796 : CollatzResearch.WordTrace tailWord_2836796 prefixEnd_2836796 485546622250662752101273 := by
  unfold tailWord_2836796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51733225115390026514997121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68977633487186702019996161 51733225115390026514997121)
  ·
    refine ⟨38799918836542519886247841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51733225115390026514997121 38799918836542519886247841)
    ·
      refine ⟨29099939127406889914685881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38799918836542519886247841 29099939127406889914685881)
      ·
        refine ⟨21824954345555167436014411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29099939127406889914685881 21824954345555167436014411)
        ·
          refine ⟨32737431518332751154021617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21824954345555167436014411 32737431518332751154021617)
          ·
            refine ⟨24553073638749563365516213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32737431518332751154021617 24553073638749563365516213)
            ·
              refine ⟨2301850653632771565517145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24553073638749563365516213 2301850653632771565517145)
              ·
                refine ⟨1726387990224578674137859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301850653632771565517145 1726387990224578674137859)
                ·
                  refine ⟨2589581985336868011206789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726387990224578674137859 2589581985336868011206789)
                  ·
                    refine ⟨485546622250662752101273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589581985336868011206789 485546622250662752101273)
                    ·
                      rfl

theorem cell23_2836796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_2836796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836796 prefixEnd_2836796 := by exact prefixLift 2836796
  have htrace : WordTrace (prefixWord ++ tailWord_2836796) baseStart_2836796 baseEnd_2836796 := by
    simpa [prefixWord, tailWord_2836796, baseEnd_2836796] using wordTrace_append hprefix tailTrace_2836796
  have hstable : (prefixWord ++ tailWord_2836796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836796).length < 2 ^ (prefixWord ++ tailWord_2836796).sum := by decide
  have hdescent : baseEnd_2836796 < baseStart_2836796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836836 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_2836836 : Nat := 118140960795 + 2836836 * 2 ^ 59
def prefixEnd_2836836 : Nat := 4983230072969 + 3 ^ 40 * 2836836 * 2
def baseEnd_2836836 : Nat := 1456660405978168099803635

theorem tailTrace_2836836 : CollatzResearch.WordTrace tailWord_2836836 prefixEnd_2836836 1456660405978168099803635 := by
  unfold tailWord_2836836
  simp only [CollatzResearch.WordTrace]
  refine ⟨51733954575317569930725181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68978606100423426574300241 51733954575317569930725181)
  ·
    refine ⟨19400232965744088724021943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51733954575317569930725181 19400232965744088724021943)
    ·
      refine ⟨29100349448616133086032915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19400232965744088724021943 29100349448616133086032915)
      ·
        refine ⟨43650524172924199629049373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29100349448616133086032915 43650524172924199629049373)
        ·
          refine ⟨16368946564846574860893515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43650524172924199629049373 16368946564846574860893515)
          ·
            refine ⟨24553419847269862291340273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16368946564846574860893515 24553419847269862291340273)
            ·
              refine ⟨18415064885452396718505205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24553419847269862291340273 18415064885452396718505205)
              ·
                refine ⟨1726412333011162192359863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18415064885452396718505205 1726412333011162192359863)
                ·
                  refine ⟨2589618499516743288539795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726412333011162192359863 2589618499516743288539795)
                  ·
                    refine ⟨3884427749275114932809693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589618499516743288539795 3884427749275114932809693)
                    ·
                      refine ⟨1456660405978168099803635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884427749275114932809693 1456660405978168099803635)
                      ·
                        rfl

theorem cell23_2836836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_2836836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836836 prefixEnd_2836836 := by exact prefixLift 2836836
  have htrace : WordTrace (prefixWord ++ tailWord_2836836) baseStart_2836836 baseEnd_2836836 := by
    simpa [prefixWord, tailWord_2836836, baseEnd_2836836] using wordTrace_append hprefix tailTrace_2836836
  have hstable : (prefixWord ++ tailWord_2836836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836836).length < 2 ^ (prefixWord ++ tailWord_2836836).sum := by decide
  have hdescent : baseEnd_2836836 < baseStart_2836836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836853 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2836853 : Nat := 118140960795 + 2836853 * 2 ^ 59
def prefixEnd_2836853 : Nat := 4983230072969 + 3 ^ 40 * 2836853 * 2
def baseEnd_2836853 : Nat := 1456669135149294533291057

theorem tailTrace_2836853 : CollatzResearch.WordTrace tailWord_2836853 prefixEnd_2836853 1456669135149294533291057 := by
  unfold tailWord_2836853
  simp only [CollatzResearch.WordTrace]
  refine ⟨103468529191573551764819213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68979019461049034509879475 103468529191573551764819213)
  ·
    refine ⟨38800698446840081911807205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103468529191573551764819213 38800698446840081911807205)
    ·
      refine ⟨7275130958782515358463851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38800698446840081911807205 7275130958782515358463851)
      ·
        refine ⟨10912696438173773037695777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7275130958782515358463851 10912696438173773037695777)
        ·
          refine ⟨8184522328630329778271833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912696438173773037695777 8184522328630329778271833)
          ·
            refine ⟨6138391746472747333703875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184522328630329778271833 6138391746472747333703875)
            ·
              refine ⟨9207587619709121000555813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138391746472747333703875 9207587619709121000555813)
              ·
                refine ⟨1726422678695460187604215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9207587619709121000555813 1726422678695460187604215)
                ·
                  refine ⟨2589634018043190281406323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726422678695460187604215 2589634018043190281406323)
                  ·
                    refine ⟨3884451027064785422109485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589634018043190281406323 3884451027064785422109485)
                    ·
                      refine ⟨1456669135149294533291057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884451027064785422109485 1456669135149294533291057)
                      ·
                        rfl

theorem cell23_2836853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2836853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836853 prefixEnd_2836853 := by exact prefixLift 2836853
  have htrace : WordTrace (prefixWord ++ tailWord_2836853) baseStart_2836853 baseEnd_2836853 := by
    simpa [prefixWord, tailWord_2836853, baseEnd_2836853] using wordTrace_append hprefix tailTrace_2836853
  have hstable : (prefixWord ++ tailWord_2836853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836853).length < 2 ^ (prefixWord ++ tailWord_2836853).sum := by decide
  have hdescent : baseEnd_2836853 < baseStart_2836853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836855 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2836855 : Nat := 118140960795 + 2836855 * 2 ^ 59
def prefixEnd_2836855 : Nat := 4983230072969 + 3 ^ 40 * 2836855 * 2
def baseEnd_2836855 : Nat := 1456670162110603525466047

theorem tailTrace_2836855 : CollatzResearch.WordTrace tailWord_2836855 prefixEnd_2836855 1456670162110603525466047 := by
  unfold tailWord_2836855
  simp only [CollatzResearch.WordTrace]
  refine ⟨103468602137566306106392019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68979068091710870737594679 103468602137566306106392019)
  ·
    refine ⟨155202903206349459159588029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103468602137566306106392019 155202903206349459159588029)
    ·
      refine ⟨58201088702381047184845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155202903206349459159588029 58201088702381047184845511)
      ·
        refine ⟨87301633053571570777268267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58201088702381047184845511 87301633053571570777268267)
        ·
          refine ⟨130952449580357356165902401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87301633053571570777268267 130952449580357356165902401)
          ·
            refine ⟨98214337185268017124426801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130952449580357356165902401 98214337185268017124426801)
            ·
              refine ⟨73660752888951012843320101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98214337185268017124426801 73660752888951012843320101)
              ·
                refine ⟨13811391166678314908122519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73660752888951012843320101 13811391166678314908122519)
                ·
                  refine ⟨20717086750017472362183779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13811391166678314908122519 20717086750017472362183779)
                  ·
                    refine ⟨31075630125026208543275669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20717086750017472362183779 31075630125026208543275669)
                    ·
                      refine ⟨1456670162110603525466047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31075630125026208543275669 1456670162110603525466047)
                      ·
                        rfl

theorem cell23_2836855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2836855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836855 prefixEnd_2836855 := by exact prefixLift 2836855
  have htrace : WordTrace (prefixWord ++ tailWord_2836855) baseStart_2836855 baseEnd_2836855 := by
    simpa [prefixWord, tailWord_2836855, baseEnd_2836855] using wordTrace_append hprefix tailTrace_2836855
  have hstable : (prefixWord ++ tailWord_2836855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836855).length < 2 ^ (prefixWord ++ tailWord_2836855).sum := by decide
  have hdescent : baseEnd_2836855 < baseStart_2836855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836876 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_2836876 : Nat := 118140960795 + 2836876 * 2 ^ 59
def prefixEnd_2836876 : Nat := 4983230072969 + 3 ^ 40 * 2836876 * 2
def baseEnd_2836876 : Nat := 1456680945204347943303451

theorem tailTrace_2836876 : CollatzResearch.WordTrace tailWord_2836876 prefixEnd_2836876 1456680945204347943303451 := by
  unfold tailWord_2836876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51734684035245113346453241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68979578713660151128604321 51734684035245113346453241)
  ·
    refine ⟨38801013026433835009839931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51734684035245113346453241 38801013026433835009839931)
    ·
      refine ⟨58201519539650752514759897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38801013026433835009839931 58201519539650752514759897)
      ·
        refine ⟨43651139654738064386069923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58201519539650752514759897 43651139654738064386069923)
        ·
          refine ⟨65476709482107096579104885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43651139654738064386069923 65476709482107096579104885)
          ·
            refine ⟨6138441513947540304291083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65476709482107096579104885 6138441513947540304291083)
            ·
              refine ⟨9207662270921310456436625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138441513947540304291083 9207662270921310456436625)
              ·
                refine ⟨6905746703190982842327469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9207662270921310456436625 6905746703190982842327469)
                ·
                  refine ⟨2589655013696618565872801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6905746703190982842327469 2589655013696618565872801)
                  ·
                    refine ⟨1942241260272463924404601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2589655013696618565872801 1942241260272463924404601)
                    ·
                      refine ⟨1456680945204347943303451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942241260272463924404601 1456680945204347943303451)
                      ·
                        rfl

theorem cell23_2836876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_2836876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836876 prefixEnd_2836876 := by exact prefixLift 2836876
  have htrace : WordTrace (prefixWord ++ tailWord_2836876) baseStart_2836876 baseEnd_2836876 := by
    simpa [prefixWord, tailWord_2836876, baseEnd_2836876] using wordTrace_append hprefix tailTrace_2836876
  have hstable : (prefixWord ++ tailWord_2836876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836876).length < 2 ^ (prefixWord ++ tailWord_2836876).sum := by decide
  have hdescent : baseEnd_2836876 < baseStart_2836876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836893 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_2836893 : Nat := 118140960795 + 2836893 * 2 ^ 59
def prefixEnd_2836893 : Nat := 4983230072969 + 3 ^ 40 * 2836893 * 2
def baseEnd_2836893 : Nat := 1456689674375474376790873

theorem tailTrace_2836893 : CollatzResearch.WordTrace tailWord_2836893 prefixEnd_2836893 1456689674375474376790873 := by
  unfold tailWord_2836893
  simp only [CollatzResearch.WordTrace]
  refine ⟨103469988111428638596275333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68979992074285759064183555 103469988111428638596275333)
  ·
    refine ⟨19400622770892869736801625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103469988111428638596275333 19400622770892869736801625)
    ·
      refine ⟨14550467078169652302601219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19400622770892869736801625 14550467078169652302601219)
      ·
        refine ⟨21825700617254478453901829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550467078169652302601219 21825700617254478453901829)
        ·
          refine ⟨4092318865735214710106593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21825700617254478453901829 4092318865735214710106593)
          ·
            refine ⟨3069239149301411032579945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092318865735214710106593 3069239149301411032579945)
            ·
              refine ⟨2301929361976058274434959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3069239149301411032579945 2301929361976058274434959)
              ·
                refine ⟨3452894042964087411652439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301929361976058274434959 3452894042964087411652439)
                ·
                  refine ⟨5179341064446131117478659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452894042964087411652439 5179341064446131117478659)
                  ·
                    refine ⟨7769011596669196676217989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179341064446131117478659 7769011596669196676217989)
                    ·
                      refine ⟨1456689674375474376790873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7769011596669196676217989 1456689674375474376790873)
                      ·
                        rfl

theorem cell23_2836893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_2836893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836893 prefixEnd_2836893 := by exact prefixLift 2836893
  have htrace : WordTrace (prefixWord ++ tailWord_2836893) baseStart_2836893 baseEnd_2836893 := by
    simpa [prefixWord, tailWord_2836893, baseEnd_2836893] using wordTrace_append hprefix tailTrace_2836893
  have hstable : (prefixWord ++ tailWord_2836893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836893).length < 2 ^ (prefixWord ++ tailWord_2836893).sum := by decide
  have hdescent : baseEnd_2836893 < baseStart_2836893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836896 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3]
def baseStart_2836896 : Nat := 118140960795 + 2836896 * 2 ^ 59
def prefixEnd_2836896 : Nat := 4983230072969 + 3 ^ 40 * 2836896 * 2
def baseEnd_2836896 : Nat := 1456691214817437865053359

theorem tailTrace_2836896 : CollatzResearch.WordTrace tailWord_2836896 prefixEnd_2836896 1456691214817437865053359 := by
  unfold tailWord_2836896
  simp only [CollatzResearch.WordTrace]
  refine ⟨51735048765208885054317271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68980065020278513405756361 51735048765208885054317271)
  ·
    refine ⟨77602573147813327581475907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51735048765208885054317271 77602573147813327581475907)
    ·
      refine ⟨116403859721719991372213861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77602573147813327581475907 116403859721719991372213861)
      ·
        refine ⟨21825723697822498382290099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116403859721719991372213861 21825723697822498382290099)
        ·
          refine ⟨32738585546733747573435149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21825723697822498382290099 32738585546733747573435149)
          ·
            refine ⟨12276969580025155340038181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32738585546733747573435149 12276969580025155340038181)
            ·
              refine ⟨2301931796254716626257159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12276969580025155340038181 2301931796254716626257159)
              ·
                refine ⟨3452897694382074939385739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301931796254716626257159 3452897694382074939385739)
                ·
                  refine ⟨5179346541573112409078609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452897694382074939385739 5179346541573112409078609)
                  ·
                    refine ⟨3884509906179834306808957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179346541573112409078609 3884509906179834306808957)
                    ·
                      refine ⟨1456691214817437865053359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884509906179834306808957 1456691214817437865053359)
                      ·
                        rfl

theorem cell23_2836896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_2836896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836896 prefixEnd_2836896 := by exact prefixLift 2836896
  have htrace : WordTrace (prefixWord ++ tailWord_2836896) baseStart_2836896 baseEnd_2836896 := by
    simpa [prefixWord, tailWord_2836896, baseEnd_2836896] using wordTrace_append hprefix tailTrace_2836896
  have hstable : (prefixWord ++ tailWord_2836896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836896).length < 2 ^ (prefixWord ++ tailWord_2836896).sum := by decide
  have hdescent : baseEnd_2836896 < baseStart_2836896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836926 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2836926 : Nat := 118140960795 + 2836926 * 2 ^ 59
def prefixEnd_2836926 : Nat := 4983230072969 + 3 ^ 40 * 2836926 * 2
def baseEnd_2836926 : Nat := 1456706619237072747678221

theorem tailTrace_2836926 : CollatzResearch.WordTrace tailWord_2836926 prefixEnd_2836926 1456706619237072747678221 := by
  unfold tailWord_2836926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933898965038635654028329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68980794480206056821484421 12933898965038635654028329)
  ·
    refine ⟨9700424223778976740521247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12933898965038635654028329 9700424223778976740521247)
    ·
      refine ⟨14550636335668465110781871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9700424223778976740521247 14550636335668465110781871)
      ·
        refine ⟨21825954503502697666172807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550636335668465110781871 21825954503502697666172807)
        ·
          refine ⟨32738931755254046499259211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21825954503502697666172807 32738931755254046499259211)
          ·
            refine ⟨49108397632881069748888817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32738931755254046499259211 49108397632881069748888817)
            ·
              refine ⟨36831298224660802311666613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49108397632881069748888817 36831298224660802311666613)
              ·
                refine ⟨3452934208561950216718745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36831298224660802311666613 3452934208561950216718745)
                ·
                  refine ⟨2589700656421462662539059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452934208561950216718745 2589700656421462662539059)
                  ·
                    refine ⟨3884550984632193993808589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589700656421462662539059 3884550984632193993808589)
                    ·
                      refine ⟨1456706619237072747678221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884550984632193993808589 1456706619237072747678221)
                      ·
                        rfl

theorem cell23_2836926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2836926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836926 prefixEnd_2836926 := by exact prefixLift 2836926
  have htrace : WordTrace (prefixWord ++ tailWord_2836926) baseStart_2836926 baseEnd_2836926 := by
    simpa [prefixWord, tailWord_2836926, baseEnd_2836926] using wordTrace_append hprefix tailTrace_2836926
  have hstable : (prefixWord ++ tailWord_2836926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836926).length < 2 ^ (prefixWord ++ tailWord_2836926).sum := by decide
  have hdescent : baseEnd_2836926 < baseStart_2836926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836936 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_2836936 : Nat := 118140960795 + 2836936 * 2 ^ 59
def prefixEnd_2836936 : Nat := 4983230072969 + 3 ^ 40 * 2836936 * 2
def baseEnd_2836936 : Nat := 1456711754043617708553175

theorem tailTrace_2836936 : CollatzResearch.WordTrace tailWord_2836936 prefixEnd_2836936 1456711754043617708553175 := by
  unfold tailWord_2836936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51735778225136428470045331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68981037633515237960060441 51735778225136428470045331)
  ·
    refine ⟨77603667337704642705067997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51735778225136428470045331 77603667337704642705067997)
    ·
      refine ⟨29101375251639241014400499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77603667337704642705067997 29101375251639241014400499)
      ·
        refine ⟨43652062877458861521600749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29101375251639241014400499 43652062877458861521600749)
        ·
          refine ⟨16369523579047073070600281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43652062877458861521600749 16369523579047073070600281)
          ·
            refine ⟨12277142684285304802950211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16369523579047073070600281 12277142684285304802950211)
            ·
              refine ⟨18415714026427957204425317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12277142684285304802950211 18415714026427957204425317)
              ·
                refine ⟨3452946379955241975829747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18415714026427957204425317 3452946379955241975829747)
                ·
                  refine ⟨5179419569932862963744621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452946379955241975829747 5179419569932862963744621)
                  ·
                    refine ⟨1942282338724823611404233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5179419569932862963744621 1942282338724823611404233)
                    ·
                      refine ⟨1456711754043617708553175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942282338724823611404233 1456711754043617708553175)
                      ·
                        rfl

theorem cell23_2836936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_2836936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836936 prefixEnd_2836936 := by exact prefixLift 2836936
  have htrace : WordTrace (prefixWord ++ tailWord_2836936) baseStart_2836936 baseEnd_2836936 := by
    simpa [prefixWord, tailWord_2836936, baseEnd_2836936] using wordTrace_append hprefix tailTrace_2836936
  have hstable : (prefixWord ++ tailWord_2836936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836936).length < 2 ^ (prefixWord ++ tailWord_2836936).sum := by decide
  have hdescent : baseEnd_2836936 < baseStart_2836936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836952 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_2836952 : Nat := 118140960795 + 2836952 * 2 ^ 59
def prefixEnd_2836952 : Nat := 4983230072969 + 3 ^ 40 * 2836952 * 2
def baseEnd_2836952 : Nat := 1456719969734089645953101

theorem tailTrace_2836952 : CollatzResearch.WordTrace tailWord_2836952 prefixEnd_2836952 1456719969734089645953101 := by
  unfold tailWord_2836952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51736070009107445836336555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68981426678809927781782073 51736070009107445836336555)
  ·
    refine ⟨77604105013661168754504833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51736070009107445836336555 77604105013661168754504833)
    ·
      refine ⟨58203078760245876565878625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77604105013661168754504833 58203078760245876565878625)
      ·
        refine ⟨43652309070184407424408969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58203078760245876565878625 43652309070184407424408969)
        ·
          refine ⟨32739231802638305568306727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43652309070184407424408969 32739231802638305568306727)
          ·
            refine ⟨49108847703957458352460091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32739231802638305568306727 49108847703957458352460091)
            ·
              refine ⟨73663271555936187528690137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49108847703957458352460091 73663271555936187528690137)
              ·
                refine ⟨55247453666952140646517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73663271555936187528690137 55247453666952140646517603)
                ·
                  refine ⟨82871180500428210969776405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55247453666952140646517603 82871180500428210969776405)
                  ·
                    refine ⟨3884586585957572389208269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82871180500428210969776405 3884586585957572389208269)
                    ·
                      refine ⟨1456719969734089645953101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884586585957572389208269 1456719969734089645953101)
                      ·
                        rfl

theorem cell23_2836952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_2836952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2836952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2836952 prefixEnd_2836952 := by exact prefixLift 2836952
  have htrace : WordTrace (prefixWord ++ tailWord_2836952) baseStart_2836952 baseEnd_2836952 := by
    simpa [prefixWord, tailWord_2836952, baseEnd_2836952] using wordTrace_append hprefix tailTrace_2836952
  have hstable : (prefixWord ++ tailWord_2836952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836952).length < 2 ^ (prefixWord ++ tailWord_2836952).sum := by decide
  have hdescent : baseEnd_2836952 < baseStart_2836952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837116 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_2837116 : Nat := 118140960795 + 2837116 * 2 ^ 59
def prefixEnd_2837116 : Nat := 4983230072969 + 3 ^ 40 * 2837116 * 2
def baseEnd_2837116 : Nat := 1456804180561427004302347

theorem tailTrace_2837116 : CollatzResearch.WordTrace tailWord_2837116 prefixEnd_2837116 1456804180561427004302347 := by
  unfold tailWord_2837116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739060794810373840821601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68985414393080498454428801 51739060794810373840821601)
  ·
    refine ⟨38804295596107780380616201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51739060794810373840821601 38804295596107780380616201)
    ·
      refine ⟨29103221697080835285462151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38804295596107780380616201 29103221697080835285462151)
      ·
        refine ⟨43654832545621252928193227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103221697080835285462151 43654832545621252928193227)
        ·
          refine ⟨65482248818431879392289841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43654832545621252928193227 65482248818431879392289841)
          ·
            refine ⟨49111686613823909544217381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65482248818431879392289841 49111686613823909544217381)
            ·
              refine ⟨9208441240091983039540759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49111686613823909544217381 9208441240091983039540759)
              ·
                refine ⟨13812661860137974559311139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208441240091983039540759 13812661860137974559311139)
                ·
                  refine ⟨20718992790206961838966709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13812661860137974559311139 20718992790206961838966709)
                  ·
                    refine ⟨1942405574081902672403129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20718992790206961838966709 1942405574081902672403129)
                    ·
                      refine ⟨1456804180561427004302347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942405574081902672403129 1456804180561427004302347)
                      ·
                        rfl

theorem cell23_2837116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_2837116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837116 prefixEnd_2837116 := by exact prefixLift 2837116
  have htrace : WordTrace (prefixWord ++ tailWord_2837116) baseStart_2837116 baseEnd_2837116 := by
    simpa [prefixWord, tailWord_2837116, baseEnd_2837116] using wordTrace_append hprefix tailTrace_2837116
  have hstable : (prefixWord ++ tailWord_2837116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837116).length < 2 ^ (prefixWord ++ tailWord_2837116).sum := by decide
  have hdescent : baseEnd_2837116 < baseStart_2837116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837117 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2837117 : Nat := 118140960795 + 2837117 * 2 ^ 59
def prefixEnd_2837117 : Nat := 4983230072969 + 3 ^ 40 * 2837117 * 2
def baseEnd_2837117 : Nat := 485601564680693833463281

theorem tailTrace_2837117 : CollatzResearch.WordTrace tailWord_2837117 prefixEnd_2837117 485601564680693833463281 := by
  unfold tailWord_2837117
  simp only [CollatzResearch.WordTrace]
  refine ⟨103478158062617124852429605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68985438708411416568286403 103478158062617124852429605)
  ·
    refine ⟨19402154636740710909830551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103478158062617124852429605 19402154636740710909830551)
    ·
      refine ⟨29103231955111066364745827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402154636740710909830551 29103231955111066364745827)
      ·
        refine ⟨43654847932666599547118741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103231955111066364745827 43654847932666599547118741)
        ·
          refine ⟨2046320996843746853771191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43654847932666599547118741 2046320996843746853771191)
          ·
            refine ⟨3069481495265620280656787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046320996843746853771191 3069481495265620280656787)
            ·
              refine ⟨4604222242898430420985181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069481495265620280656787 4604222242898430420985181)
              ·
                refine ⟨1726583341086911407869443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4604222242898430420985181 1726583341086911407869443)
                ·
                  refine ⟨2589875011630367111804165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726583341086911407869443 2589875011630367111804165)
                  ·
                    refine ⟨485601564680693833463281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589875011630367111804165 485601564680693833463281)
                    ·
                      rfl

theorem cell23_2837117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2837117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837117 prefixEnd_2837117 := by exact prefixLift 2837117
  have htrace : WordTrace (prefixWord ++ tailWord_2837117) baseStart_2837117 baseEnd_2837117 := by
    simpa [prefixWord, tailWord_2837117, baseEnd_2837117] using wordTrace_append hprefix tailTrace_2837117
  have hstable : (prefixWord ++ tailWord_2837117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837117).length < 2 ^ (prefixWord ++ tailWord_2837117).sum := by decide
  have hdescent : baseEnd_2837117 < baseStart_2837117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837129 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_2837129 : Nat := 118140960795 + 2837129 * 2 ^ 59
def prefixEnd_2837129 : Nat := 4983230072969 + 3 ^ 40 * 2837129 * 2
def baseEnd_2837129 : Nat := 1456810855809935453439787

theorem tailTrace_2837129 : CollatzResearch.WordTrace tailWord_2837129 prefixEnd_2837129 1456810855809935453439787 := by
  unfold tailWord_2837129
  simp only [CollatzResearch.WordTrace]
  refine ⟨103478595738573650901866441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68985730492382433934577627 103478595738573650901866441)
  ·
    refine ⟨77608946803930238176399831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103478595738573650901866441 77608946803930238176399831)
    ·
      refine ⟨116413420205895357264599747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77608946803930238176399831 116413420205895357264599747)
      ·
        refine ⟨174620130308843035896899621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116413420205895357264599747 174620130308843035896899621)
        ·
          refine ⟨32741274432908069230668679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174620130308843035896899621 32741274432908069230668679)
          ·
            refine ⟨49111911649362103846003019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32741274432908069230668679 49111911649362103846003019)
            ·
              refine ⟨73667867474043155769004529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49111911649362103846003019 73667867474043155769004529)
              ·
                refine ⟨55250900605532366826753397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73667867474043155769004529 55250900605532366826753397)
                ·
                  refine ⟨5179771931768659390008131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55250900605532366826753397 5179771931768659390008131)
                  ·
                    refine ⟨7769657897652989085012197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179771931768659390008131 7769657897652989085012197)
                    ·
                      refine ⟨1456810855809935453439787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7769657897652989085012197 1456810855809935453439787)
                      ·
                        rfl

theorem cell23_2837129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_2837129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837129 prefixEnd_2837129 := by exact prefixLift 2837129
  have htrace : WordTrace (prefixWord ++ tailWord_2837129) baseStart_2837129 baseEnd_2837129 := by
    simpa [prefixWord, tailWord_2837129, baseEnd_2837129] using wordTrace_append hprefix tailTrace_2837129
  have hstable : (prefixWord ++ tailWord_2837129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837129).length < 2 ^ (prefixWord ++ tailWord_2837129).sum := by decide
  have hdescent : baseEnd_2837129 < baseStart_2837129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837140 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2837140 : Nat := 118140960795 + 2837140 * 2 ^ 59
def prefixEnd_2837140 : Nat := 4983230072969 + 3 ^ 40 * 2837140 * 2
def baseEnd_2837140 : Nat := 1456816504097134910402237

theorem tailTrace_2837140 : CollatzResearch.WordTrace tailWord_2837140 prefixEnd_2837140 1456816504097134910402237 := by
  unfold tailWord_2837140
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739498470766899890258437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68985997961022533187011249 51739498470766899890258437)
  ·
    refine ⟨9701155963268793729423457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51739498470766899890258437 9701155963268793729423457)
    ·
      refine ⟨7275866972451595297067593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9701155963268793729423457 7275866972451595297067593)
      ·
        refine ⟨5456900229338696472800695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275866972451595297067593 5456900229338696472800695)
        ·
          refine ⟨8185350344008044709201043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456900229338696472800695 8185350344008044709201043)
          ·
            refine ⟨12278025516012067063801565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185350344008044709201043 12278025516012067063801565)
            ·
              refine ⟨4604259568504525148925587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12278025516012067063801565 4604259568504525148925587)
              ·
                refine ⟨6906389352756787723388381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604259568504525148925587 6906389352756787723388381)
                ·
                  refine ⟨2589896007283795396270643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6906389352756787723388381 2589896007283795396270643)
                  ·
                    refine ⟨3884844010925693094405965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589896007283795396270643 3884844010925693094405965)
                    ·
                      refine ⟨1456816504097134910402237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3884844010925693094405965 1456816504097134910402237)
                      ·
                        rfl

theorem cell23_2837140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2837140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837140 prefixEnd_2837140 := by exact prefixLift 2837140
  have htrace : WordTrace (prefixWord ++ tailWord_2837140) baseStart_2837140 baseEnd_2837140 := by
    simpa [prefixWord, tailWord_2837140, baseEnd_2837140] using wordTrace_append hprefix tailTrace_2837140
  have hstable : (prefixWord ++ tailWord_2837140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837140).length < 2 ^ (prefixWord ++ tailWord_2837140).sum := by decide
  have hdescent : baseEnd_2837140 < baseStart_2837140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837186 : List Nat := [3, 5, 1, 14]
def baseStart_2837186 : Nat := 118140960795 + 2837186 * 2 ^ 59
def prefixEnd_2837186 : Nat := 4983230072969 + 3 ^ 40 * 2837186 * 2
def baseEnd_2837186 : Nat := 666136316509941349075

theorem tailTrace_2837186 : CollatzResearch.WordTrace tailWord_2837186 prefixEnd_2837186 666136316509941349075 := by
  unfold tailWord_2837186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870168674841787409172853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68987116466244766424460941 25870168674841787409172853)
  ·
    refine ⟨2425328313266417569609955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25870168674841787409172853 2425328313266417569609955)
    ·
      refine ⟨3637992469899626354414933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425328313266417569609955 3637992469899626354414933)
      ·
        refine ⟨666136316509941349075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 3637992469899626354414933 666136316509941349075)
        ·
          rfl

theorem cell23_2837186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 14].length) (baseStart_2837186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837186 prefixEnd_2837186 := by exact prefixLift 2837186
  have htrace : WordTrace (prefixWord ++ tailWord_2837186) baseStart_2837186 baseEnd_2837186 := by
    simpa [prefixWord, tailWord_2837186, baseEnd_2837186] using wordTrace_append hprefix tailTrace_2837186
  have hstable : (prefixWord ++ tailWord_2837186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837186).length < 2 ^ (prefixWord ++ tailWord_2837186).sum := by decide
  have hdescent : baseEnd_2837186 < baseStart_2837186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837239 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2837239 : Nat := 118140960795 + 2837239 * 2 ^ 59
def prefixEnd_2837239 : Nat := 4983230072969 + 3 ^ 40 * 2837239 * 2
def baseEnd_2837239 : Nat := 1456867338681930023064281

theorem tailTrace_2837239 : CollatzResearch.WordTrace tailWord_2837239 prefixEnd_2837239 1456867338681930023064281 := by
  unfold tailWord_2837239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103482607768175139688370771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68988405178783426458913847 103482607768175139688370771)
  ·
    refine ⟨155223911652262709532556157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103482607768175139688370771 155223911652262709532556157)
    ·
      refine ⟨58208966869598516074708559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155223911652262709532556157 58208966869598516074708559)
      ·
        refine ⟨87313450304397774112062839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58208966869598516074708559 87313450304397774112062839)
        ·
          refine ⟨130970175456596661168094259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87313450304397774112062839 130970175456596661168094259)
          ·
            refine ⟨196455263184894991752141389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130970175456596661168094259 196455263184894991752141389)
            ·
              refine ⟨73670723694335621907053021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196455263184894991752141389 73670723694335621907053021)
              ·
                refine ⟨27626521385375858215144883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73670723694335621907053021 27626521385375858215144883)
                ·
                  refine ⟨41439782078063787322717325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27626521385375858215144883 41439782078063787322717325)
                  ·
                    refine ⟨15539918279273920246018997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41439782078063787322717325 15539918279273920246018997)
                    ·
                      refine ⟨1456867338681930023064281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15539918279273920246018997 1456867338681930023064281)
                      ·
                        rfl

theorem cell23_2837239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2837239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837239 prefixEnd_2837239 := by exact prefixLift 2837239
  have htrace : WordTrace (prefixWord ++ tailWord_2837239) baseStart_2837239 baseEnd_2837239 := by
    simpa [prefixWord, tailWord_2837239, baseEnd_2837239] using wordTrace_append hprefix tailTrace_2837239
  have hstable : (prefixWord ++ tailWord_2837239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837239).length < 2 ^ (prefixWord ++ tailWord_2837239).sum := by decide
  have hdescent : baseEnd_2837239 < baseStart_2837239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837276 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 7]
def baseStart_2837276 : Nat := 118140960795 + 2837276 * 2 ^ 59
def prefixEnd_2837276 : Nat := 4983230072969 + 3 ^ 40 * 2837276 * 2
def baseEnd_2837276 : Nat := 161876259718460708700179

theorem tailTrace_2837276 : CollatzResearch.WordTrace tailWord_2837276 prefixEnd_2837276 161876259718460708700179 := by
  unfold tailWord_2837276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51741978634520547503733841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68989304846027396671645121 51741978634520547503733841)
  ·
    refine ⟨38806483975890410627800381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51741978634520547503733841 38806483975890410627800381)
    ·
      refine ⟨14552431490958903985425143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38806483975890410627800381 14552431490958903985425143)
      ·
        refine ⟨21828647236438355978137715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14552431490958903985425143 21828647236438355978137715)
        ·
          refine ⟨32742970854657533967206573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21828647236438355978137715 32742970854657533967206573)
          ·
            refine ⟨12278614070496575237702465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32742970854657533967206573 12278614070496575237702465)
            ·
              refine ⟨9208960552872431428276849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12278614070496575237702465 9208960552872431428276849)
              ·
                refine ⟨6906720414654323571207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9208960552872431428276849 6906720414654323571207637)
                ·
                  refine ⟨161876259718460708700179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6906720414654323571207637 161876259718460708700179)
                  ·
                    rfl

theorem cell23_2837276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_2837276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837276 prefixEnd_2837276 := by exact prefixLift 2837276
  have htrace : WordTrace (prefixWord ++ tailWord_2837276) baseStart_2837276 baseEnd_2837276 := by
    simpa [prefixWord, tailWord_2837276, baseEnd_2837276] using wordTrace_append hprefix tailTrace_2837276
  have hstable : (prefixWord ++ tailWord_2837276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837276).length < 2 ^ (prefixWord ++ tailWord_2837276).sum := by decide
  have hdescent : baseEnd_2837276 < baseStart_2837276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837290 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2837290 : Nat := 118140960795 + 2837290 * 2 ^ 59
def prefixEnd_2837290 : Nat := 4983230072969 + 3 ^ 40 * 2837290 * 2
def baseEnd_2837290 : Nat := 1456893526195309323526547

theorem tailTrace_2837290 : CollatzResearch.WordTrace tailWord_2837290 prefixEnd_2837290 1456893526195309323526547 := by
  unfold tailWord_2837290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25871116972747593849619331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68989645260660250265651549 25871116972747593849619331)
  ·
    refine ⟨38806675459121390774428997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25871116972747593849619331 38806675459121390774428997)
    ·
      refine ⟨7276251648585260770205437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38806675459121390774428997 7276251648585260770205437)
      ·
        refine ⟨2728594368219472788827039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7276251648585260770205437 2728594368219472788827039)
        ·
          refine ⟨4092891552329209183240559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728594368219472788827039 4092891552329209183240559)
          ·
            refine ⟨6139337328493813774860839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092891552329209183240559 6139337328493813774860839)
            ·
              refine ⟨9209005992740720662291259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139337328493813774860839 9209005992740720662291259)
              ·
                refine ⟨13813508989111080993436889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9209005992740720662291259 13813508989111080993436889)
                ·
                  refine ⟨10360131741833310745077667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13813508989111080993436889 10360131741833310745077667)
                  ·
                    refine ⟨15540197612749966117616501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10360131741833310745077667 15540197612749966117616501)
                    ·
                      refine ⟨1456893526195309323526547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15540197612749966117616501 1456893526195309323526547)
                      ·
                        rfl

theorem cell23_2837290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2837290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837290 prefixEnd_2837290 := by exact prefixLift 2837290
  have htrace : WordTrace (prefixWord ++ tailWord_2837290) baseStart_2837290 baseEnd_2837290 := by
    simpa [prefixWord, tailWord_2837290, baseEnd_2837290] using wordTrace_append hprefix tailTrace_2837290
  have hstable : (prefixWord ++ tailWord_2837290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837290).length < 2 ^ (prefixWord ++ tailWord_2837290).sum := by decide
  have hdescent : baseEnd_2837290 < baseStart_2837290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837310 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2837310 : Nat := 118140960795 + 2837310 * 2 ^ 59
def prefixEnd_2837310 : Nat := 4983230072969 + 3 ^ 40 * 2837310 * 2
def baseEnd_2837310 : Nat := 161878199534266582808495

theorem tailTrace_2837310 : CollatzResearch.WordTrace tailWord_2837310 prefixEnd_2837310 161878199534266582808495 := by
  unfold tailWord_2837310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935649668864739851775673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68990131567278612542803589 12935649668864739851775673)
  ·
    refine ⟨9701737251648554888831755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12935649668864739851775673 9701737251648554888831755)
    ·
      refine ⟨14552605877472832333247633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701737251648554888831755 14552605877472832333247633)
      ·
        refine ⟨10914454408104624249935725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14552605877472832333247633 10914454408104624249935725)
        ·
          refine ⟨4092920403039234093725897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10914454408104624249935725 4092920403039234093725897)
          ·
            refine ⟨3069690302279425570294423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092920403039234093725897 3069690302279425570294423)
            ·
              refine ⟨4604535453419138355441635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069690302279425570294423 4604535453419138355441635)
              ·
                refine ⟨6906803180128707533162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604535453419138355441635 6906803180128707533162453)
                ·
                  refine ⟨161878199534266582808495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6906803180128707533162453 161878199534266582808495)
                  ·
                    rfl

theorem cell23_2837310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2837310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837310 prefixEnd_2837310 := by exact prefixLift 2837310
  have htrace : WordTrace (prefixWord ++ tailWord_2837310) baseStart_2837310 baseEnd_2837310 := by
    simpa [prefixWord, tailWord_2837310, baseEnd_2837310] using wordTrace_append hprefix tailTrace_2837310
  have hstable : (prefixWord ++ tailWord_2837310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837310).length < 2 ^ (prefixWord ++ tailWord_2837310).sum := by decide
  have hdescent : baseEnd_2837310 < baseStart_2837310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837326 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2837326 : Nat := 118140960795 + 2837326 * 2 ^ 59
def prefixEnd_2837326 : Nat := 4983230072969 + 3 ^ 40 * 2837326 * 2
def baseEnd_2837326 : Nat := 1456912011498871182676381

theorem tailTrace_2837326 : CollatzResearch.WordTrace tailWord_2837326 prefixEnd_2837326 1456912011498871182676381 := by
  unfold tailWord_2837326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935722614857494193348479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68990520612573302364525221 12935722614857494193348479)
  ·
    refine ⟨19403583922286241290022719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935722614857494193348479 19403583922286241290022719)
    ·
      refine ⟨29105375883429361935034079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19403583922286241290022719 29105375883429361935034079)
      ·
        refine ⟨43658063825144042902551119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29105375883429361935034079 43658063825144042902551119)
        ·
          refine ⟨65487095737716064353826679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43658063825144042902551119 65487095737716064353826679)
          ·
            refine ⟨98230643606574096530740019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65487095737716064353826679 98230643606574096530740019)
            ·
              refine ⟨147345965409861144796110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98230643606574096530740019 147345965409861144796110029)
              ·
                refine ⟨55254737028697929298541261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147345965409861144796110029 55254737028697929298541261)
                ·
                  refine ⟨20720526385761723486952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55254737028697929298541261 20720526385761723486952973)
                  ·
                    refine ⟨7770197394660646307607365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20720526385761723486952973 7770197394660646307607365)
                    ·
                      refine ⟨1456912011498871182676381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7770197394660646307607365 1456912011498871182676381)
                      ·
                        rfl

theorem cell23_2837326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2837326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837326 prefixEnd_2837326 := by exact prefixLift 2837326
  have htrace : WordTrace (prefixWord ++ tailWord_2837326) baseStart_2837326 baseEnd_2837326 := by
    simpa [prefixWord, tailWord_2837326, baseEnd_2837326] using wordTrace_append hprefix tailTrace_2837326
  have hstable : (prefixWord ++ tailWord_2837326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837326).length < 2 ^ (prefixWord ++ tailWord_2837326).sum := by decide
  have hdescent : baseEnd_2837326 < baseStart_2837326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837340 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2837340 : Nat := 118140960795 + 2837340 * 2 ^ 59
def prefixEnd_2837340 : Nat := 4983230072969 + 3 ^ 40 * 2837340 * 2
def baseEnd_2837340 : Nat := 485639733409344709300439

theorem tailTrace_2837340 : CollatzResearch.WordTrace tailWord_2837340 prefixEnd_2837340 485639733409344709300439 := by
  unfold tailWord_2837340
  simp only [CollatzResearch.WordTrace]
  refine ⟨51743145770404616968898737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68990861027206155958531649 51743145770404616968898737)
  ·
    refine ⟨38807359327803462726674053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51743145770404616968898737 38807359327803462726674053)
    ·
      refine ⟨7276379873963149261251385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38807359327803462726674053 7276379873963149261251385)
      ·
        refine ⟨5457284905472361945938539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7276379873963149261251385 5457284905472361945938539)
        ·
          refine ⟨8185927358208542918907809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457284905472361945938539 8185927358208542918907809)
          ·
            refine ⟨6139445518656407189180857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185927358208542918907809 6139445518656407189180857)
            ·
              refine ⟨4604584138992305391885643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139445518656407189180857 4604584138992305391885643)
              ·
                refine ⟨6906876208488458087828465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604584138992305391885643 6906876208488458087828465)
                ·
                  refine ⟨5180157156366343565871349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6906876208488458087828465 5180157156366343565871349)
                  ·
                    refine ⟨485639733409344709300439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5180157156366343565871349 485639733409344709300439)
                    ·
                      rfl

theorem cell23_2837340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2837340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837340 prefixEnd_2837340 := by exact prefixLift 2837340
  have htrace : WordTrace (prefixWord ++ tailWord_2837340) baseStart_2837340 baseEnd_2837340 := by
    simpa [prefixWord, tailWord_2837340, baseEnd_2837340] using wordTrace_append hprefix tailTrace_2837340
  have hstable : (prefixWord ++ tailWord_2837340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837340).length < 2 ^ (prefixWord ++ tailWord_2837340).sum := by decide
  have hdescent : baseEnd_2837340 < baseStart_2837340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837343 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_2837343 : Nat := 118140960795 + 2837343 * 2 ^ 59
def prefixEnd_2837343 : Nat := 4983230072969 + 3 ^ 40 * 2837343 * 2
def baseEnd_2837343 : Nat := 1456920740669997616163803

theorem tailTrace_2837343 : CollatzResearch.WordTrace tailWord_2837343 prefixEnd_2837343 1456920740669997616163803 := by
  unfold tailWord_2837343
  simp only [CollatzResearch.WordTrace]
  refine ⟨103486400959798365450156683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68990933973198910300104455 103486400959798365450156683)
  ·
    refine ⟨155229601439697548175235025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103486400959798365450156683 155229601439697548175235025)
    ·
      refine ⟨116422201079773161131426269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155229601439697548175235025 116422201079773161131426269)
      ·
        refine ⟨43658325404914935424284851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116422201079773161131426269 43658325404914935424284851)
        ·
          refine ⟨65487488107372403136427277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43658325404914935424284851 65487488107372403136427277)
          ·
            refine ⟨24557808040264651176160229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65487488107372403136427277 24557808040264651176160229)
            ·
              refine ⟨4604589007549622095530043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24557808040264651176160229 4604589007549622095530043)
              ·
                refine ⟨6906883511324433143295065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604589007549622095530043 6906883511324433143295065)
                ·
                  refine ⟨5180162633493324857471299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6906883511324433143295065 5180162633493324857471299)
                  ·
                    refine ⟨7770243950239987286206949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180162633493324857471299 7770243950239987286206949)
                    ·
                      refine ⟨1456920740669997616163803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7770243950239987286206949 1456920740669997616163803)
                      ·
                        rfl

theorem cell23_2837343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_2837343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837343 prefixEnd_2837343 := by exact prefixLift 2837343
  have htrace : WordTrace (prefixWord ++ tailWord_2837343) baseStart_2837343 baseEnd_2837343 := by
    simpa [prefixWord, tailWord_2837343, baseEnd_2837343] using wordTrace_append hprefix tailTrace_2837343
  have hstable : (prefixWord ++ tailWord_2837343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837343).length < 2 ^ (prefixWord ++ tailWord_2837343).sum := by decide
  have hdescent : baseEnd_2837343 < baseStart_2837343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837356 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2837356 : Nat := 118140960795 + 2837356 * 2 ^ 59
def prefixEnd_2837356 : Nat := 4983230072969 + 3 ^ 40 * 2837356 * 2
def baseEnd_2837356 : Nat := 1456927415918506065301243

theorem tailTrace_2837356 : CollatzResearch.WordTrace tailWord_2837356 prefixEnd_2837356 1456927415918506065301243 := by
  unfold tailWord_2837356
  simp only [CollatzResearch.WordTrace]
  refine ⟨51743437554375634335189961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68991250072500845780253281 51743437554375634335189961)
  ·
    refine ⟨38807578165781725751392471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51743437554375634335189961 38807578165781725751392471)
    ·
      refine ⟨58211367248672588627088707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38807578165781725751392471 58211367248672588627088707)
      ·
        refine ⟨87317050873008882940633061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58211367248672588627088707 87317050873008882940633061)
        ·
          refine ⟨16371947038689165551368699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87317050873008882940633061 16371947038689165551368699)
          ·
            refine ⟨24557920558033748327053049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16371947038689165551368699 24557920558033748327053049)
            ·
              refine ⟨18418440418525311245289787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24557920558033748327053049 18418440418525311245289787)
              ·
                refine ⟨27627660627787966867934681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18418440418525311245289787 27627660627787966867934681)
                ·
                  refine ⟨20720745470840975150951011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27627660627787966867934681 20720745470840975150951011)
                  ·
                    refine ⟨31081118206261462726426517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20720745470840975150951011 31081118206261462726426517)
                    ·
                      refine ⟨1456927415918506065301243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31081118206261462726426517 1456927415918506065301243)
                      ·
                        rfl

theorem cell23_2837356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2837356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837356 prefixEnd_2837356 := by exact prefixLift 2837356
  have htrace : WordTrace (prefixWord ++ tailWord_2837356) baseStart_2837356 baseEnd_2837356 := by
    simpa [prefixWord, tailWord_2837356, baseEnd_2837356] using wordTrace_append hprefix tailTrace_2837356
  have hstable : (prefixWord ++ tailWord_2837356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837356).length < 2 ^ (prefixWord ++ tailWord_2837356).sum := by decide
  have hdescent : baseEnd_2837356 < baseStart_2837356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837363 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3]
def baseStart_2837363 : Nat := 118140960795 + 2837363 * 2 ^ 59
def prefixEnd_2837363 : Nat := 4983230072969 + 3 ^ 40 * 2837363 * 2
def baseEnd_2837363 : Nat := 1456931010283087537913711

theorem tailTrace_2837363 : CollatzResearch.WordTrace tailWord_2837363 prefixEnd_2837363 1456931010283087537913711 := by
  unfold tailWord_2837363
  simp only [CollatzResearch.WordTrace]
  refine ⟨103487130419725908865884743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68991420279817272577256495 103487130419725908865884743)
  ·
    refine ⟨155230695629588863298827115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103487130419725908865884743 155230695629588863298827115)
    ·
      refine ⟨232846043444383294948240673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155230695629588863298827115 232846043444383294948240673)
      ·
        refine ⟨174634532583287471211180505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232846043444383294948240673 174634532583287471211180505)
        ·
          refine ⟨130975899437465603408385379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174634532583287471211180505 130975899437465603408385379)
          ·
            refine ⟨196463849156198405112578069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130975899437465603408385379 196463849156198405112578069)
            ·
              refine ⟨9209242929196800239652097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196463849156198405112578069 9209242929196800239652097)
              ·
                refine ⟨6906932196897600179739073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9209242929196800239652097 6906932196897600179739073)
                ·
                  refine ⟨5180199147673200134804305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6906932196897600179739073 5180199147673200134804305)
                  ·
                    refine ⟨3885149360754900101103229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5180199147673200134804305 3885149360754900101103229)
                    ·
                      refine ⟨1456931010283087537913711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3885149360754900101103229 1456931010283087537913711)
                      ·
                        rfl

theorem cell23_2837363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_2837363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837363 prefixEnd_2837363 := by exact prefixLift 2837363
  have htrace : WordTrace (prefixWord ++ tailWord_2837363) baseStart_2837363 baseEnd_2837363 := by
    simpa [prefixWord, tailWord_2837363, baseEnd_2837363] using wordTrace_append hprefix tailTrace_2837363
  have hstable : (prefixWord ++ tailWord_2837363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837363).length < 2 ^ (prefixWord ++ tailWord_2837363).sum := by decide
  have hdescent : baseEnd_2837363 < baseStart_2837363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837383 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 6]
def baseStart_2837383 : Nat := 118140960795 + 2837383 * 2 ^ 59
def prefixEnd_2837383 : Nat := 4983230072969 + 3 ^ 40 * 2837383 * 2
def baseEnd_2837383 : Nat := 161882364432908606629291

theorem tailTrace_2837383 : CollatzResearch.WordTrace tailWord_2837383 prefixEnd_2837383 161882364432908606629291 := by
  unfold tailWord_2837383
  simp only [CollatzResearch.WordTrace]
  refine ⟨103487859879653452281612803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68991906586435634854408535 103487859879653452281612803)
  ·
    refine ⟨155231789819480178422419205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103487859879653452281612803 155231789819480178422419205)
    ·
      refine ⟨29105960591152533454203601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155231789819480178422419205 29105960591152533454203601)
      ·
        refine ⟨21829470443364400090652701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29105960591152533454203601 21829470443364400090652701)
        ·
          refine ⟨8186051416261650033994763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21829470443364400090652701 8186051416261650033994763)
          ·
            refine ⟨12279077124392475050992145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186051416261650033994763 12279077124392475050992145)
            ·
              refine ⟨9209307843294356288244109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12279077124392475050992145 9209307843294356288244109)
              ·
                refine ⟨3453490441235383608091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9209307843294356288244109 3453490441235383608091541)
                ·
                  refine ⟨161882364432908606629291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3453490441235383608091541 161882364432908606629291)
                  ·
                    rfl

theorem cell23_2837383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 6].length) (baseStart_2837383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837383 prefixEnd_2837383 := by exact prefixLift 2837383
  have htrace : WordTrace (prefixWord ++ tailWord_2837383) baseStart_2837383 baseEnd_2837383 := by
    simpa [prefixWord, tailWord_2837383, baseEnd_2837383] using wordTrace_append hprefix tailTrace_2837383
  have hstable : (prefixWord ++ tailWord_2837383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837383).length < 2 ^ (prefixWord ++ tailWord_2837383).sum := by decide
  have hdescent : baseEnd_2837383 < baseStart_2837383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837394 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2837394 : Nat := 118140960795 + 2837394 * 2 ^ 59
def prefixEnd_2837394 : Nat := 4983230072969 + 3 ^ 40 * 2837394 * 2
def baseEnd_2837394 : Nat := 1456946928183376916626069

theorem tailTrace_2837394 : CollatzResearch.WordTrace tailWord_2837394 prefixEnd_2837394 1456946928183376916626069 := by
  unfold tailWord_2837394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25872065270653400290065809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68992174055075734106842157 25872065270653400290065809)
  ·
    refine ⟨19404048952990050217549357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25872065270653400290065809 19404048952990050217549357)
    ·
      refine ⟨7276518357371268831581009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19404048952990050217549357 7276518357371268831581009)
      ·
        refine ⟨5457388768028451623685757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7276518357371268831581009 5457388768028451623685757)
        ·
          refine ⟨2046520788010669358882159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5457388768028451623685757 2046520788010669358882159)
          ·
            refine ⟨3069781182016004038323239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046520788010669358882159 3069781182016004038323239)
            ·
              refine ⟨4604671773024006057484859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069781182016004038323239 4604671773024006057484859)
              ·
                refine ⟨6907007659536009086227289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604671773024006057484859 6907007659536009086227289)
                ·
                  refine ⟨5180255744652006814670467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6907007659536009086227289 5180255744652006814670467)
                  ·
                    refine ⟨7770383616978010222005701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180255744652006814670467 7770383616978010222005701)
                    ·
                      refine ⟨1456946928183376916626069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7770383616978010222005701 1456946928183376916626069)
                      ·
                        rfl

theorem cell23_2837394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2837394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837394 prefixEnd_2837394 := by exact prefixLift 2837394
  have htrace : WordTrace (prefixWord ++ tailWord_2837394) baseStart_2837394 baseEnd_2837394 := by
    simpa [prefixWord, tailWord_2837394, baseEnd_2837394] using wordTrace_append hprefix tailTrace_2837394
  have hstable : (prefixWord ++ tailWord_2837394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837394).length < 2 ^ (prefixWord ++ tailWord_2837394).sum := by decide
  have hdescent : baseEnd_2837394 < baseStart_2837394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837404 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2837404 : Nat := 118140960795 + 2837404 * 2 ^ 59
def prefixEnd_2837404 : Nat := 4983230072969 + 3 ^ 40 * 2837404 * 2
def baseEnd_2837404 : Nat := 485650687663307292500341

theorem tailTrace_2837404 : CollatzResearch.WordTrace tailWord_2837404 prefixEnd_2837404 485650687663307292500341 := by
  unfold tailWord_2837404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51744312906288686434063633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68992417208384915245418177 51744312906288686434063633)
  ·
    refine ⟨38808234679716514825547725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51744312906288686434063633 38808234679716514825547725)
    ·
      refine ⟨14553088004893693059580397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38808234679716514825547725 14553088004893693059580397)
      ·
        refine ⟨5457408001835134897342649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14553088004893693059580397 5457408001835134897342649)
        ·
          refine ⟨4093056001376351173006987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5457408001835134897342649 4093056001376351173006987)
          ·
            refine ⟨6139584002064526759510481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093056001376351173006987 6139584002064526759510481)
            ·
              refine ⟨4604688001548395069632861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139584002064526759510481 4604688001548395069632861)
              ·
                refine ⟨1726758000580648151112323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4604688001548395069632861 1726758000580648151112323)
                ·
                  refine ⟨2590137000870972226668485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726758000580648151112323 2590137000870972226668485)
                  ·
                    refine ⟨485650687663307292500341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590137000870972226668485 485650687663307292500341)
                    ·
                      rfl

theorem cell23_2837404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2837404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837404 prefixEnd_2837404 := by exact prefixLift 2837404
  have htrace : WordTrace (prefixWord ++ tailWord_2837404) baseStart_2837404 baseEnd_2837404 := by
    simpa [prefixWord, tailWord_2837404, baseEnd_2837404] using wordTrace_append hprefix tailTrace_2837404
  have hstable : (prefixWord ++ tailWord_2837404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837404).length < 2 ^ (prefixWord ++ tailWord_2837404).sum := by decide
  have hdescent : baseEnd_2837404 < baseStart_2837404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837426 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_2837426 : Nat := 118140960795 + 2837426 * 2 ^ 59
def prefixEnd_2837426 : Nat := 4983230072969 + 3 ^ 40 * 2837426 * 2
def baseEnd_2837426 : Nat := 485654453188106930475307

theorem tailTrace_2837426 : CollatzResearch.WordTrace tailWord_2837426 prefixEnd_2837426 485654453188106930475307 := by
  unfold tailWord_2837426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25872357054624417656357033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68992952145665113750285421 25872357054624417656357033)
  ·
    refine ⟨19404267790968313242267775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25872357054624417656357033 19404267790968313242267775)
    ·
      refine ⟨29106401686452469863401663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19404267790968313242267775 29106401686452469863401663)
      ·
        refine ⟨43659602529678704795102495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29106401686452469863401663 43659602529678704795102495)
        ·
          refine ⟨65489403794518057192653743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43659602529678704795102495 65489403794518057192653743)
          ·
            refine ⟨98234105691777085788980615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65489403794518057192653743 98234105691777085788980615)
            ·
              refine ⟨147351158537665628683470923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98234105691777085788980615 147351158537665628683470923)
              ·
                refine ⟨221026737806498443025206385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147351158537665628683470923 221026737806498443025206385)
                ·
                  refine ⟨165770053354873832268904789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221026737806498443025206385 165770053354873832268904789)
                  ·
                    refine ⟨485654453188106930475307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 165770053354873832268904789 485654453188106930475307)
                    ·
                      rfl

theorem cell23_2837426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_2837426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837426 prefixEnd_2837426 := by exact prefixLift 2837426
  have htrace : WordTrace (prefixWord ++ tailWord_2837426) baseStart_2837426 baseEnd_2837426 := by
    simpa [prefixWord, tailWord_2837426, baseEnd_2837426] using wordTrace_append hprefix tailTrace_2837426
  have hstable : (prefixWord ++ tailWord_2837426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837426).length < 2 ^ (prefixWord ++ tailWord_2837426).sum := by decide
  have hdescent : baseEnd_2837426 < baseStart_2837426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837460 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_2837460 : Nat := 118140960795 + 2837460 * 2 ^ 59
def prefixEnd_2837460 : Nat := 4983230072969 + 3 ^ 40 * 2837460 * 2
def baseEnd_2837460 : Nat := 485660272635524552800255

theorem tailTrace_2837460 : CollatzResearch.WordTrace tailWord_2837460 prefixEnd_2837460 485660272635524552800255 := by
  unfold tailWord_2837460
  simp only [CollatzResearch.WordTrace]
  refine ⟨51745334150187247216082917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68993778866916329621443889 51745334150187247216082917)
  ·
    refine ⟨9702250153160108853015547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51745334150187247216082917 9702250153160108853015547)
    ·
      refine ⟨14553375229740163279523321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702250153160108853015547 14553375229740163279523321)
      ·
        refine ⟨10915031422305122459642491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14553375229740163279523321 10915031422305122459642491)
        ·
          refine ⟨16372547133457683689463737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10915031422305122459642491 16372547133457683689463737)
          ·
            refine ⟨12279410350093262767097803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16372547133457683689463737 12279410350093262767097803)
            ·
              refine ⟨18419115525139894150646705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279410350093262767097803 18419115525139894150646705)
              ·
                refine ⟨13814336643854920612985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18419115525139894150646705 13814336643854920612985029)
                ·
                  refine ⟨2590188120722797614934693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13814336643854920612985029 2590188120722797614934693)
                  ·
                    refine ⟨485660272635524552800255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590188120722797614934693 485660272635524552800255)
                    ·
                      rfl

theorem cell23_2837460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_2837460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837460 prefixEnd_2837460 := by exact prefixLift 2837460
  have htrace : WordTrace (prefixWord ++ tailWord_2837460) baseStart_2837460 baseEnd_2837460 := by
    simpa [prefixWord, tailWord_2837460, baseEnd_2837460] using wordTrace_append hprefix tailTrace_2837460
  have hstable : (prefixWord ++ tailWord_2837460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837460).length < 2 ^ (prefixWord ++ tailWord_2837460).sum := by decide
  have hdescent : baseEnd_2837460 < baseStart_2837460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837461 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2837461 : Nat := 118140960795 + 2837461 * 2 ^ 59
def prefixEnd_2837461 : Nat := 4983230072969 + 3 ^ 40 * 2837461 * 2
def baseEnd_2837461 : Nat := 1456981331387228154488261

theorem tailTrace_2837461 : CollatzResearch.WordTrace tailWord_2837461 prefixEnd_2837461 1456981331387228154488261 := by
  unfold tailWord_2837461
  simp only [CollatzResearch.WordTrace]
  refine ⟨103490704773370871602952237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68993803182247247735301491 103490704773370871602952237)
  ·
    refine ⟨38809014290014076851107089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103490704773370871602952237 38809014290014076851107089)
    ·
      refine ⟨29106760717510557638330317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38809014290014076851107089 29106760717510557638330317)
      ·
        refine ⟨10915035269066459114373869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29106760717510557638330317 10915035269066459114373869)
        ·
          refine ⟨4093138225899922167890201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10915035269066459114373869 4093138225899922167890201)
          ·
            refine ⟨3069853669424941625917651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4093138225899922167890201 3069853669424941625917651)
            ·
              refine ⟨4604780504137412438876477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069853669424941625917651 4604780504137412438876477)
              ·
                refine ⟨1726792689051529664578679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4604780504137412438876477 1726792689051529664578679)
                ·
                  refine ⟨2590189033577294496868019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726792689051529664578679 2590189033577294496868019)
                  ·
                    refine ⟨3885283550365941745302029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590189033577294496868019 3885283550365941745302029)
                    ·
                      refine ⟨1456981331387228154488261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3885283550365941745302029 1456981331387228154488261)
                      ·
                        rfl

theorem cell23_2837461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2837461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837461 prefixEnd_2837461 := by exact prefixLift 2837461
  have htrace : WordTrace (prefixWord ++ tailWord_2837461) baseStart_2837461 baseEnd_2837461 := by
    simpa [prefixWord, tailWord_2837461, baseEnd_2837461] using wordTrace_append hprefix tailTrace_2837461
  have hstable : (prefixWord ++ tailWord_2837461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837461).length < 2 ^ (prefixWord ++ tailWord_2837461).sum := by decide
  have hdescent : baseEnd_2837461 < baseStart_2837461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837494 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2837494 : Nat := 118140960795 + 2837494 * 2 ^ 59
def prefixEnd_2837494 : Nat := 4983230072969 + 3 ^ 40 * 2837494 * 2
def baseEnd_2837494 : Nat := 485666092082942175125203

theorem tailTrace_2837494 : CollatzResearch.WordTrace tailWord_2837494 prefixEnd_2837494 485666092082942175125203 := by
  unfold tailWord_2837494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468244273890707389931471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68994605588167545492602357 6468244273890707389931471)
  ·
    refine ⟨9702366410836061084897207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468244273890707389931471 9702366410836061084897207)
    ·
      refine ⟨14553549616254091627345811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702366410836061084897207 14553549616254091627345811)
      ·
        refine ⟨21830324424381137441018717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553549616254091627345811 21830324424381137441018717)
        ·
          refine ⟨8186371659142926540382019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21830324424381137441018717 8186371659142926540382019)
          ·
            refine ⟨12279557488714389810573029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186371659142926540382019 12279557488714389810573029)
            ·
              refine ⟨2302417029133948089482443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12279557488714389810573029 2302417029133948089482443)
              ·
                refine ⟨3453625543700922134223665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302417029133948089482443 3453625543700922134223665)
                ·
                  refine ⟨2590219157775691600667749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453625543700922134223665 2590219157775691600667749)
                  ·
                    refine ⟨485666092082942175125203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590219157775691600667749 485666092082942175125203)
                    ·
                      rfl

theorem cell23_2837494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2837494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837494 prefixEnd_2837494 := by exact prefixLift 2837494
  have htrace : WordTrace (prefixWord ++ tailWord_2837494) baseStart_2837494 baseEnd_2837494 := by
    simpa [prefixWord, tailWord_2837494, baseEnd_2837494] using wordTrace_append hprefix tailTrace_2837494
  have hstable : (prefixWord ++ tailWord_2837494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837494).length < 2 ^ (prefixWord ++ tailWord_2837494).sum := by decide
  have hdescent : baseEnd_2837494 < baseStart_2837494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837540 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2837540 : Nat := 118140960795 + 2837540 * 2 ^ 59
def prefixEnd_2837540 : Nat := 4983230072969 + 3 ^ 40 * 2837540 * 2
def baseEnd_2837540 : Nat := 1457021896358933345400397

theorem tailTrace_2837540 : CollatzResearch.WordTrace tailWord_2837540 prefixEnd_2837540 1457021896358933345400397 := by
  unfold tailWord_2837540
  simp only [CollatzResearch.WordTrace]
  refine ⟨51746793070042334047539037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68995724093389778730052049 51746793070042334047539037)
  ·
    refine ⟨19405047401265875267827139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51746793070042334047539037 19405047401265875267827139)
    ·
      refine ⟨29107571101898812901740709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19405047401265875267827139 29107571101898812901740709)
      ·
        refine ⟨5457669581606027419076383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29107571101898812901740709 5457669581606027419076383)
        ·
          refine ⟨8186504372409041128614575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457669581606027419076383 8186504372409041128614575)
          ·
            refine ⟨12279756558613561692921863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186504372409041128614575 12279756558613561692921863)
            ·
              refine ⟨18419634837920342539382795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279756558613561692921863 18419634837920342539382795)
              ·
                refine ⟨27629452256880513809074193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18419634837920342539382795 27629452256880513809074193)
                ·
                  refine ⟨20722089192660385356805645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27629452256880513809074193 20722089192660385356805645)
                  ·
                    refine ⟨7770783447247644508802117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20722089192660385356805645 7770783447247644508802117)
                    ·
                      refine ⟨1457021896358933345400397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7770783447247644508802117 1457021896358933345400397)
                      ·
                        rfl

theorem cell23_2837540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2837540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837540 prefixEnd_2837540 := by exact prefixLift 2837540
  have htrace : WordTrace (prefixWord ++ tailWord_2837540) baseStart_2837540 baseEnd_2837540 := by
    simpa [prefixWord, tailWord_2837540, baseEnd_2837540] using wordTrace_append hprefix tailTrace_2837540
  have hstable : (prefixWord ++ tailWord_2837540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837540).length < 2 ^ (prefixWord ++ tailWord_2837540).sum := by decide
  have hdescent : baseEnd_2837540 < baseStart_2837540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837550 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2837550 : Nat := 118140960795 + 2837550 * 2 ^ 59
def prefixEnd_2837550 : Nat := 4983230072969 + 3 ^ 40 * 2837550 * 2
def baseEnd_2837550 : Nat := 485675677055159435425117

theorem tailTrace_2837550 : CollatzResearch.WordTrace tailWord_2837550 prefixEnd_2837550 485675677055159435425117 := by
  unfold tailWord_2837550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936743858756054975367763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68995967246698959868628069 12936743858756054975367763)
  ·
    refine ⟨19405115788134082463051645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12936743858756054975367763 19405115788134082463051645)
    ·
      refine ⟨7276918420550280923644367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19405115788134082463051645 7276918420550280923644367)
      ·
        refine ⟨10915377630825421385466551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276918420550280923644367 10915377630825421385466551)
        ·
          refine ⟨16373066446238132078199827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10915377630825421385466551 16373066446238132078199827)
          ·
            refine ⟨24559599669357198117299741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16373066446238132078199827 24559599669357198117299741)
            ·
              refine ⟨9209849876008949293987403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24559599669357198117299741 9209849876008949293987403)
              ·
                refine ⟨13814774814013423940981105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9209849876008949293987403 13814774814013423940981105)
                ·
                  refine ⟨10361081110510067955735829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814774814013423940981105 10361081110510067955735829)
                  ·
                    refine ⟨485675677055159435425117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10361081110510067955735829 485675677055159435425117)
                    ·
                      rfl

theorem cell23_2837550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2837550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837550 prefixEnd_2837550 := by exact prefixLift 2837550
  have htrace : WordTrace (prefixWord ++ tailWord_2837550) baseStart_2837550 baseEnd_2837550 := by
    simpa [prefixWord, tailWord_2837550, baseEnd_2837550] using wordTrace_append hprefix tailTrace_2837550
  have hstable : (prefixWord ++ tailWord_2837550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837550).length < 2 ^ (prefixWord ++ tailWord_2837550).sum := by decide
  have hdescent : baseEnd_2837550 < baseStart_2837550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837557 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_2837557 : Nat := 118140960795 + 2837557 * 2 ^ 59
def prefixEnd_2837557 : Nat := 4983230072969 + 3 ^ 40 * 2837557 * 2
def baseEnd_2837557 : Nat := 1457030625530059778887819

theorem tailTrace_2837557 : CollatzResearch.WordTrace tailWord_2837557 prefixEnd_2837557 1457030625530059778887819 := by
  unfold tailWord_2837557
  simp only [CollatzResearch.WordTrace]
  refine ⟨103494206181023079998446925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68996137454015386665631283 103494206181023079998446925)
  ·
    refine ⟨38810327317883654999417597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103494206181023079998446925 38810327317883654999417597)
    ·
      refine ⟨14553872744206370624781599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38810327317883654999417597 14553872744206370624781599)
      ·
        refine ⟨21830809116309555937172399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553872744206370624781599 21830809116309555937172399)
        ·
          refine ⟨32746213674464333905758599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830809116309555937172399 32746213674464333905758599)
          ·
            refine ⟨49119320511696500858637899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32746213674464333905758599 49119320511696500858637899)
            ·
              refine ⟨73678980767544751287956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49119320511696500858637899 73678980767544751287956849)
              ·
                refine ⟨55259235575658563465967637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73678980767544751287956849 55259235575658563465967637)
                ·
                  refine ⟨2590276667608995162467233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55259235575658563465967637 2590276667608995162467233)
                  ·
                    refine ⟨1942707500706746371850425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2590276667608995162467233 1942707500706746371850425)
                    ·
                      refine ⟨1457030625530059778887819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942707500706746371850425 1457030625530059778887819)
                      ·
                        rfl

theorem cell23_2837557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_2837557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837557 prefixEnd_2837557 := by exact prefixLift 2837557
  have htrace : WordTrace (prefixWord ++ tailWord_2837557) baseStart_2837557 baseEnd_2837557 := by
    simpa [prefixWord, tailWord_2837557, baseEnd_2837557] using wordTrace_append hprefix tailTrace_2837557
  have hstable : (prefixWord ++ tailWord_2837557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837557).length < 2 ^ (prefixWord ++ tailWord_2837557).sum := by decide
  have hdescent : baseEnd_2837557 < baseStart_2837557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837603 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2837603 : Nat := 118140960795 + 2837603 * 2 ^ 59
def prefixEnd_2837603 : Nat := 4983230072969 + 3 ^ 40 * 2837603 * 2
def baseEnd_2837603 : Nat := 1457054245640166598912607

theorem tailTrace_2837603 : CollatzResearch.WordTrace tailWord_2837603 prefixEnd_2837603 1457054245640166598912607 := by
  unfold tailWord_2837603
  simp only [CollatzResearch.WordTrace]
  refine ⟨103495883938856429854621463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68997255959237619903080975 103495883938856429854621463)
  ·
    refine ⟨155243825908284644781932195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103495883938856429854621463 155243825908284644781932195)
    ·
      refine ⟨232865738862426967172898293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155243825908284644781932195 232865738862426967172898293)
      ·
        refine ⟨21831163018352528172459215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232865738862426967172898293 21831163018352528172459215)
        ·
          refine ⟨32746744527528792258688823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21831163018352528172459215 32746744527528792258688823)
          ·
            refine ⟨49120116791293188388033235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32746744527528792258688823 49120116791293188388033235)
            ·
              refine ⟨73680175186939782582049853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49120116791293188388033235 73680175186939782582049853)
              ·
                refine ⟨27630065695102418468268695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73680175186939782582049853 27630065695102418468268695)
                ·
                  refine ⟨41445098542653627702403043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27630065695102418468268695 41445098542653627702403043)
                  ·
                    refine ⟨62167647813980441553604565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41445098542653627702403043 62167647813980441553604565)
                    ·
                      refine ⟨1457054245640166598912607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62167647813980441553604565 1457054245640166598912607)
                      ·
                        rfl

theorem cell23_2837603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2837603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837603 prefixEnd_2837603 := by exact prefixLift 2837603
  have htrace : WordTrace (prefixWord ++ tailWord_2837603) baseStart_2837603 baseEnd_2837603 := by
    simpa [prefixWord, tailWord_2837603, baseEnd_2837603] using wordTrace_append hprefix tailTrace_2837603
  have hstable : (prefixWord ++ tailWord_2837603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837603).length < 2 ^ (prefixWord ++ tailWord_2837603).sum := by decide
  have hdescent : baseEnd_2837603 < baseStart_2837603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837608 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2837608 : Nat := 118140960795 + 2837608 * 2 ^ 59
def prefixEnd_2837608 : Nat := 4983230072969 + 3 ^ 40 * 2837608 * 2
def baseEnd_2837608 : Nat := 1457056813043439079350085

theorem tailTrace_2837608 : CollatzResearch.WordTrace tailWord_2837608 prefixEnd_2837608 1457056813043439079350085 := by
  unfold tailWord_2837608
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748033151919157854276739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68997377535892210472368985 51748033151919157854276739)
  ·
    refine ⟨77622049727878736781415109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51748033151919157854276739 77622049727878736781415109)
    ·
      refine ⟨14554134323977263146515333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77622049727878736781415109 14554134323977263146515333)
      ·
        refine ⟨2728900185745736839971625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14554134323977263146515333 2728900185745736839971625)
        ·
          refine ⟨2046675139309302629978719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728900185745736839971625 2046675139309302629978719)
          ·
            refine ⟨3070012708963953944968079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046675139309302629978719 3070012708963953944968079)
            ·
              refine ⟨4605019063445930917452119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070012708963953944968079 4605019063445930917452119)
              ·
                refine ⟨6907528595168896376178179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605019063445930917452119 6907528595168896376178179)
                ·
                  refine ⟨10361292892753344564267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6907528595168896376178179 10361292892753344564267269)
                  ·
                    refine ⟨1942742417391252105800113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10361292892753344564267269 1942742417391252105800113)
                    ·
                      refine ⟨1457056813043439079350085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942742417391252105800113 1457056813043439079350085)
                      ·
                        rfl

theorem cell23_2837608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2837608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837608 prefixEnd_2837608 := by exact prefixLift 2837608
  have htrace : WordTrace (prefixWord ++ tailWord_2837608) baseStart_2837608 baseEnd_2837608 := by
    simpa [prefixWord, tailWord_2837608, baseEnd_2837608] using wordTrace_append hprefix tailTrace_2837608
  have hstable : (prefixWord ++ tailWord_2837608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837608).length < 2 ^ (prefixWord ++ tailWord_2837608).sum := by decide
  have hdescent : baseEnd_2837608 < baseStart_2837608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837610 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2837610 : Nat := 118140960795 + 2837610 * 2 ^ 59
def prefixEnd_2837610 : Nat := 4983230072969 + 3 ^ 40 * 2837610 * 2
def baseEnd_2837610 : Nat := 485685946668249357175025

theorem tailTrace_2837610 : CollatzResearch.WordTrace tailWord_2837610 prefixEnd_2837610 485685946668249357175025 := by
  unfold tailWord_2837610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874034812457767512531571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68997426166554046700084189 25874034812457767512531571)
  ·
    refine ⟨38811052218686651268797357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874034812457767512531571 38811052218686651268797357)
    ·
      refine ⟨14554144582007494225799009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38811052218686651268797357 14554144582007494225799009)
      ·
        refine ⟨10915608436505620669349257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14554144582007494225799009 10915608436505620669349257)
        ·
          refine ⟨8186706327379215502011943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10915608436505620669349257 8186706327379215502011943)
          ·
            refine ⟨12280059491068823253017915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186706327379215502011943 12280059491068823253017915)
            ·
              refine ⟨18420089236603234879526873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12280059491068823253017915 18420089236603234879526873)
              ·
                refine ⟨13815066927452426159645155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18420089236603234879526873 13815066927452426159645155)
                ·
                  refine ⟨20722600391178639239467733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13815066927452426159645155 20722600391178639239467733)
                  ·
                    refine ⟨485685946668249357175025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20722600391178639239467733 485685946668249357175025)
                    ·
                      rfl

theorem cell23_2837610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2837610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837610 prefixEnd_2837610 := by exact prefixLift 2837610
  have htrace : WordTrace (prefixWord ++ tailWord_2837610) baseStart_2837610 baseEnd_2837610 := by
    simpa [prefixWord, tailWord_2837610, baseEnd_2837610] using wordTrace_append hprefix tailTrace_2837610
  have hstable : (prefixWord ++ tailWord_2837610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837610).length < 2 ^ (prefixWord ++ tailWord_2837610).sum := by decide
  have hdescent : baseEnd_2837610 < baseStart_2837610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837623 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 8]
def baseStart_2837623 : Nat := 118140960795 + 2837623 * 2 ^ 59
def prefixEnd_2837623 : Nat := 4983230072969 + 3 ^ 40 * 2837623 * 2
def baseEnd_2837623 : Nat := 485688171751085506887505

theorem tailTrace_2837623 : CollatzResearch.WordTrace tailWord_2837623 prefixEnd_2837623 485688171751085506887505 := by
  unfold tailWord_2837623
  simp only [CollatzResearch.WordTrace]
  refine ⟨103496613398783973270349523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68997742265855982180233015 103496613398783973270349523)
  ·
    refine ⟨155244920098175959905524285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103496613398783973270349523 155244920098175959905524285)
    ·
      refine ⟨58216845036815984964571607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155244920098175959905524285 58216845036815984964571607)
      ·
        refine ⟨87325267555223977446857411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58216845036815984964571607 87325267555223977446857411)
        ·
          refine ⟨130987901332835966170286117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87325267555223977446857411 130987901332835966170286117)
          ·
            refine ⟨24560231499906743656928647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130987901332835966170286117 24560231499906743656928647)
            ·
              refine ⟨36840347249860115485392971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24560231499906743656928647 36840347249860115485392971)
              ·
                refine ⟨55260520874790173228089457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36840347249860115485392971 55260520874790173228089457)
                ·
                  refine ⟨41445390656092629921067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55260520874790173228089457 41445390656092629921067093)
                  ·
                    refine ⟨485688171751085506887505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41445390656092629921067093 485688171751085506887505)
                    ·
                      rfl

theorem cell23_2837623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_2837623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837623 prefixEnd_2837623 := by exact prefixLift 2837623
  have htrace : WordTrace (prefixWord ++ tailWord_2837623) baseStart_2837623 baseEnd_2837623 := by
    simpa [prefixWord, tailWord_2837623, baseEnd_2837623] using wordTrace_append hprefix tailTrace_2837623
  have hstable : (prefixWord ++ tailWord_2837623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837623).length < 2 ^ (prefixWord ++ tailWord_2837623).sum := by decide
  have hdescent : baseEnd_2837623 < baseStart_2837623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837643 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_2837643 : Nat := 118140960795 + 2837643 * 2 ^ 59
def prefixEnd_2837643 : Nat := 4983230072969 + 3 ^ 40 * 2837643 * 2
def baseEnd_2837643 : Nat := 1457074784866346442412423

theorem tailTrace_2837643 : CollatzResearch.WordTrace tailWord_2837643 prefixEnd_2837643 1457074784866346442412423 := by
  unfold tailWord_2837643
  simp only [CollatzResearch.WordTrace]
  refine ⟨103497342858711516686077583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68998228572474344457385055 103497342858711516686077583)
  ·
    refine ⟨155246014288067275029116375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103497342858711516686077583 155246014288067275029116375)
    ·
      refine ⟨232869021432100912543674563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155246014288067275029116375 232869021432100912543674563)
      ·
        refine ⟨349303532148151368815511845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232869021432100912543674563 349303532148151368815511845)
        ·
          refine ⟨65494412277778381652908471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349303532148151368815511845 65494412277778381652908471)
          ·
            refine ⟨98241618416667572479362707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65494412277778381652908471 98241618416667572479362707)
            ·
              refine ⟨147362427625001358719044061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98241618416667572479362707 147362427625001358719044061)
              ·
                refine ⟨55260910359375509519641523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147362427625001358719044061 55260910359375509519641523)
                ·
                  refine ⟨82891365539063264279462285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55260910359375509519641523 82891365539063264279462285)
                  ·
                    refine ⟨31084262077148724104798357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82891365539063264279462285 31084262077148724104798357)
                    ·
                      refine ⟨1457074784866346442412423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31084262077148724104798357 1457074784866346442412423)
                      ·
                        rfl

theorem cell23_2837643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_2837643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837643 prefixEnd_2837643 := by exact prefixLift 2837643
  have htrace : WordTrace (prefixWord ++ tailWord_2837643) baseStart_2837643 baseEnd_2837643 := by
    simpa [prefixWord, tailWord_2837643, baseEnd_2837643] using wordTrace_append hprefix tailTrace_2837643
  have hstable : (prefixWord ++ tailWord_2837643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837643).length < 2 ^ (prefixWord ++ tailWord_2837643).sum := by decide
  have hdescent : baseEnd_2837643 < baseStart_2837643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837707 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 4, 3, 2]
def baseStart_2837707 : Nat := 118140960795 + 2837707 * 2 ^ 59
def prefixEnd_2837707 : Nat := 4983230072969 + 3 ^ 40 * 2837707 * 2
def baseEnd_2837707 : Nat := 1457107647628234192012129

theorem tailTrace_2837707 : CollatzResearch.WordTrace tailWord_2837707 prefixEnd_2837707 1457107647628234192012129 := by
  unfold tailWord_2837707
  simp only [CollatzResearch.WordTrace]
  refine ⟨103499677130479655616407375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68999784753653103744271583 103499677130479655616407375)
  ·
    refine ⟨155249515695719483424611063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103499677130479655616407375 155249515695719483424611063)
    ·
      refine ⟨232874273543579225136916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155249515695719483424611063 232874273543579225136916595)
      ·
        refine ⟨349311410315368837705374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232874273543579225136916595 349311410315368837705374893)
        ·
          refine ⟨130991778868263314139515585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349311410315368837705374893 130991778868263314139515585)
          ·
            refine ⟨98243834151197485604636689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130991778868263314139515585 98243834151197485604636689)
            ·
              refine ⟨73682875613398114203477517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98243834151197485604636689 73682875613398114203477517)
              ·
                refine ⟨27631078355024292826304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73682875613398114203477517 27631078355024292826304069)
                ·
                  refine ⟨5180827191567054904932013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27631078355024292826304069 5180827191567054904932013)
                  ·
                    refine ⟨1942810196837645589349505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5180827191567054904932013 1942810196837645589349505)
                    ·
                      refine ⟨1457107647628234192012129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942810196837645589349505 1457107647628234192012129)
                      ·
                        rfl

theorem cell23_2837707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3, 2].length) (baseStart_2837707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837707 prefixEnd_2837707 := by exact prefixLift 2837707
  have htrace : WordTrace (prefixWord ++ tailWord_2837707) baseStart_2837707 baseEnd_2837707 := by
    simpa [prefixWord, tailWord_2837707, baseEnd_2837707] using wordTrace_append hprefix tailTrace_2837707
  have hstable : (prefixWord ++ tailWord_2837707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837707).length < 2 ^ (prefixWord ++ tailWord_2837707).sum := by decide
  have hdescent : baseEnd_2837707 < baseStart_2837707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837714 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2837714 : Nat := 118140960795 + 2837714 * 2 ^ 59
def prefixEnd_2837714 : Nat := 4983230072969 + 3 ^ 40 * 2837714 * 2
def baseEnd_2837714 : Nat := 1457111241992815664624597

theorem tailTrace_2837714 : CollatzResearch.WordTrace tailWord_2837714 prefixEnd_2837714 1457111241992815664624597 := by
  unfold tailWord_2837714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874983110363573952978049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68999954960969530541274797 25874983110363573952978049)
  ·
    refine ⟨19406237332772680464733537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25874983110363573952978049 19406237332772680464733537)
    ·
      refine ⟨14554677999579510348550153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19406237332772680464733537 14554677999579510348550153)
      ·
        refine ⟨10916008499684632761412615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14554677999579510348550153 10916008499684632761412615)
        ·
          refine ⟨16374012749526949142118923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10916008499684632761412615 16374012749526949142118923)
          ·
            refine ⟨24561019124290423713178385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16374012749526949142118923 24561019124290423713178385)
            ·
              refine ⟨18420764343217817784883789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24561019124290423713178385 18420764343217817784883789)
              ·
                refine ⟨6907786628706681669331421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18420764343217817784883789 6907786628706681669331421)
                ·
                  refine ⟨2590419985765005625999283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6907786628706681669331421 2590419985765005625999283)
                  ·
                    refine ⟨3885629978647508438998925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590419985765005625999283 3885629978647508438998925)
                    ·
                      refine ⟨1457111241992815664624597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3885629978647508438998925 1457111241992815664624597)
                      ·
                        rfl

theorem cell23_2837714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2837714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837714 prefixEnd_2837714 := by exact prefixLift 2837714
  have htrace : WordTrace (prefixWord ++ tailWord_2837714) baseStart_2837714 baseEnd_2837714 := by
    simpa [prefixWord, tailWord_2837714, baseEnd_2837714] using wordTrace_append hprefix tailTrace_2837714
  have hstable : (prefixWord ++ tailWord_2837714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837714).length < 2 ^ (prefixWord ++ tailWord_2837714).sum := by decide
  have hdescent : baseEnd_2837714 < baseStart_2837714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837717 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2837717 : Nat := 118140960795 + 2837717 * 2 ^ 59
def prefixEnd_2837717 : Nat := 4983230072969 + 3 ^ 40 * 2837717 * 2
def baseEnd_2837717 : Nat := 485704260811593050962361

theorem tailTrace_2837717 : CollatzResearch.WordTrace tailWord_2837717 prefixEnd_2837717 485704260811593050962361 := by
  unfold tailWord_2837717
  simp only [CollatzResearch.WordTrace]
  refine ⟨103500041860443427324271405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69000027906962284882847603 103500041860443427324271405)
  ·
    refine ⟨38812515697666285246601777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103500041860443427324271405 38812515697666285246601777)
    ·
      refine ⟨29109386773249713934951333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38812515697666285246601777 29109386773249713934951333)
      ·
        refine ⟨5458010019984321362803375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29109386773249713934951333 5458010019984321362803375)
        ·
          refine ⟨8187015029976482044205063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458010019984321362803375 8187015029976482044205063)
          ·
            refine ⟨12280522544964723066307595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187015029976482044205063 12280522544964723066307595)
            ·
              refine ⟨18420783817447084599461393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12280522544964723066307595 18420783817447084599461393)
              ·
                refine ⟨13815587863085313449596045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18420783817447084599461393 13815587863085313449596045)
                ·
                  refine ⟨5180845448656992543598517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13815587863085313449596045 5180845448656992543598517)
                  ·
                    refine ⟨485704260811593050962361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5180845448656992543598517 485704260811593050962361)
                    ·
                      rfl

theorem cell23_2837717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2837717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837717 prefixEnd_2837717 := by exact prefixLift 2837717
  have htrace : WordTrace (prefixWord ++ tailWord_2837717) baseStart_2837717 baseEnd_2837717 := by
    simpa [prefixWord, tailWord_2837717, baseEnd_2837717] using wordTrace_append hprefix tailTrace_2837717
  have hstable : (prefixWord ++ tailWord_2837717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837717).length < 2 ^ (prefixWord ++ tailWord_2837717).sum := by decide
  have hdescent : baseEnd_2837717 < baseStart_2837717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837741 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2837741 : Nat := 118140960795 + 2837741 * 2 ^ 59
def prefixEnd_2837741 : Nat := 4983230072969 + 3 ^ 40 * 2837741 * 2
def baseEnd_2837741 : Nat := 1457125105970487058986973

theorem tailTrace_2837741 : CollatzResearch.WordTrace tailWord_2837741 prefixEnd_2837741 1457125105970487058986973 := by
  unfold tailWord_2837741
  simp only [CollatzResearch.WordTrace]
  refine ⟨103500917212356479423145077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69000611474904319615430051 103500917212356479423145077)
  ·
    refine ⟨9703210988658419945919851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103500917212356479423145077 9703210988658419945919851)
    ·
      refine ⟨14554816482987629918879777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9703210988658419945919851 14554816482987629918879777)
      ·
        refine ⟨10916112362240722439159833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14554816482987629918879777 10916112362240722439159833)
        ·
          refine ⟨8187084271680541829369875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10916112362240722439159833 8187084271680541829369875)
          ·
            refine ⟨12280626407520812744054813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187084271680541829369875 12280626407520812744054813)
            ·
              refine ⟨4605234902820304779020555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12280626407520812744054813 4605234902820304779020555)
              ·
                refine ⟨6907852354230457168530833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605234902820304779020555 6907852354230457168530833)
                ·
                  refine ⟨5180889265672842876398125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6907852354230457168530833 5180889265672842876398125)
                  ·
                    refine ⟨1942833474627316078649297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5180889265672842876398125 1942833474627316078649297)
                    ·
                      refine ⟨1457125105970487058986973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942833474627316078649297 1457125105970487058986973)
                      ·
                        rfl

theorem cell23_2837741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2837741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837741 prefixEnd_2837741 := by exact prefixLift 2837741
  have htrace : WordTrace (prefixWord ++ tailWord_2837741) baseStart_2837741 baseEnd_2837741 := by
    simpa [prefixWord, tailWord_2837741, baseEnd_2837741] using wordTrace_append hprefix tailTrace_2837741
  have hstable : (prefixWord ++ tailWord_2837741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837741).length < 2 ^ (prefixWord ++ tailWord_2837741).sum := by decide
  have hdescent : baseEnd_2837741 < baseStart_2837741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837754 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_2837754 : Nat := 118140960795 + 2837754 * 2 ^ 59
def prefixEnd_2837754 : Nat := 4983230072969 + 3 ^ 40 * 2837754 * 2
def baseEnd_2837754 : Nat := 1457131781218995508124413

theorem tailTrace_2837754 : CollatzResearch.WordTrace tailWord_2837754 prefixEnd_2837754 1457131781218995508124413 := by
  unfold tailWord_2837754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25875347840327345660842079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69000927574206255095578877 25875347840327345660842079)
  ·
    refine ⟨38813021760491018491263119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25875347840327345660842079 38813021760491018491263119)
    ·
      refine ⟨58219532640736527736894679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38813021760491018491263119 58219532640736527736894679)
      ·
        refine ⟨87329298961104791605342019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58219532640736527736894679 87329298961104791605342019)
        ·
          refine ⟨130993948441657187408013029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87329298961104791605342019 130993948441657187408013029)
          ·
            refine ⟨24561365332810722639002443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130993948441657187408013029 24561365332810722639002443)
            ·
              refine ⟨36842047999216083958503665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24561365332810722639002443 36842047999216083958503665)
              ·
                refine ⟨27631535999412062968877749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36842047999216083958503665 27631535999412062968877749)
                ·
                  refine ⟨2590456499944880903332289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27631535999412062968877749 2590456499944880903332289)
                  ·
                    refine ⟨1942842374958660677499217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2590456499944880903332289 1942842374958660677499217)
                    ·
                      refine ⟨1457131781218995508124413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942842374958660677499217 1457131781218995508124413)
                      ·
                        rfl

theorem cell23_2837754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_2837754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837754 prefixEnd_2837754 := by exact prefixLift 2837754
  have htrace : WordTrace (prefixWord ++ tailWord_2837754) baseStart_2837754 baseEnd_2837754 := by
    simpa [prefixWord, tailWord_2837754, baseEnd_2837754] using wordTrace_append hprefix tailTrace_2837754
  have hstable : (prefixWord ++ tailWord_2837754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837754).length < 2 ^ (prefixWord ++ tailWord_2837754).sum := by decide
  have hdescent : baseEnd_2837754 < baseStart_2837754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837764 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2837764 : Nat := 118140960795 + 2837764 * 2 ^ 59
def prefixEnd_2837764 : Nat := 4983230072969 + 3 ^ 40 * 2837764 * 2
def baseEnd_2837764 : Nat := 485712305341846822999789

theorem tailTrace_2837764 : CollatzResearch.WordTrace tailWord_2837764 prefixEnd_2837764 485712305341846822999789 := by
  unfold tailWord_2837764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51750878045636577175616173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69001170727515436234154897 51750878045636577175616173)
  ·
    refine ⟨19406579267113716440856065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51750878045636577175616173 19406579267113716440856065)
    ·
      refine ⟨14554934450335287330642049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19406579267113716440856065 14554934450335287330642049)
      ·
        refine ⟨10916200837751465497981537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14554934450335287330642049 10916200837751465497981537)
        ·
          refine ⟨8187150628313599123486153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10916200837751465497981537 8187150628313599123486153)
          ·
            refine ⟨6140362971235199342614615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8187150628313599123486153 6140362971235199342614615)
            ·
              refine ⟨9210544456852799013921923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140362971235199342614615 9210544456852799013921923)
              ·
                refine ⟨13815816685279198520882885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210544456852799013921923 13815816685279198520882885)
                ·
                  refine ⟨2590465628489849722665541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13815816685279198520882885 2590465628489849722665541)
                  ·
                    refine ⟨485712305341846822999789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590465628489849722665541 485712305341846822999789)
                    ·
                      rfl

theorem cell23_2837764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2837764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837764 prefixEnd_2837764 := by exact prefixLift 2837764
  have htrace : WordTrace (prefixWord ++ tailWord_2837764) baseStart_2837764 baseEnd_2837764 := by
    simpa [prefixWord, tailWord_2837764, baseEnd_2837764] using wordTrace_append hprefix tailTrace_2837764
  have hstable : (prefixWord ++ tailWord_2837764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837764).length < 2 ^ (prefixWord ++ tailWord_2837764).sum := by decide
  have hdescent : baseEnd_2837764 < baseStart_2837764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2837770 : Nat := 118140960795 + 2837770 * 2 ^ 59
def prefixEnd_2837770 : Nat := 4983230072969 + 3 ^ 40 * 2837770 * 2
def baseEnd_2837770 : Nat := 1457139996909467445524339

theorem tailTrace_2837770 : CollatzResearch.WordTrace tailWord_2837770 prefixEnd_2837770 1457139996909467445524339 := by
  unfold tailWord_2837770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25875493732312854343987691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69001316619500944917300509 25875493732312854343987691)
  ·
    refine ⟨38813240598469281515981537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25875493732312854343987691 38813240598469281515981537)
    ·
      refine ⟨29109930448851961136986153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38813240598469281515981537 29109930448851961136986153)
      ·
        refine ⟨21832447836638970852739615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29109930448851961136986153 21832447836638970852739615)
        ·
          refine ⟨32748671754958456279109423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21832447836638970852739615 32748671754958456279109423)
          ·
            refine ⟨49123007632437684418664135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32748671754958456279109423 49123007632437684418664135)
            ·
              refine ⟨73684511448656526627996203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49123007632437684418664135 73684511448656526627996203)
              ·
                refine ⟨110526767172984789941994305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73684511448656526627996203 110526767172984789941994305)
                ·
                  refine ⟨82895075379738592456495729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110526767172984789941994305 82895075379738592456495729)
                  ·
                    refine ⟨62171306534803944342371797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82895075379738592456495729 62171306534803944342371797)
                    ·
                      refine ⟨1457139996909467445524339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62171306534803944342371797 1457139996909467445524339)
                      ·
                        rfl

theorem cell23_2837770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2837770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837770 prefixEnd_2837770 := by exact prefixLift 2837770
  have htrace : WordTrace (prefixWord ++ tailWord_2837770) baseStart_2837770 baseEnd_2837770 := by
    simpa [prefixWord, tailWord_2837770, baseEnd_2837770] using wordTrace_append hprefix tailTrace_2837770
  have hstable : (prefixWord ++ tailWord_2837770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837770).length < 2 ^ (prefixWord ++ tailWord_2837770).sum := by decide
  have hdescent : baseEnd_2837770 < baseStart_2837770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837771 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 3, 2, 2]
def baseStart_2837771 : Nat := 118140960795 + 2837771 * 2 ^ 59
def prefixEnd_2837771 : Nat := 4983230072969 + 3 ^ 40 * 2837771 * 2
def baseEnd_2837771 : Nat := 1457140510390121941611835

theorem tailTrace_2837771 : CollatzResearch.WordTrace tailWord_2837771 prefixEnd_2837771 1457140510390121941611835 := by
  unfold tailWord_2837771
  simp only [CollatzResearch.WordTrace]
  refine ⟨103502011402247794546737167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69001340934831863031158111 103502011402247794546737167)
  ·
    refine ⟨155253017103371691820105751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103502011402247794546737167 155253017103371691820105751)
    ·
      refine ⟨232879525655057537730158627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155253017103371691820105751 232879525655057537730158627)
      ·
        refine ⟨349319288482586306595237941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232879525655057537730158627 349319288482586306595237941)
        ·
          refine ⟨32748683295242466243303557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349319288482586306595237941 32748683295242466243303557)
          ·
            refine ⟨6140378117857962420619417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32748683295242466243303557 6140378117857962420619417)
            ·
              refine ⟨4605283588393471815464563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6140378117857962420619417 4605283588393471815464563)
              ·
                refine ⟨6907925382590207723196845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605283588393471815464563 6907925382590207723196845)
                ·
                  refine ⟨2590472018471327896198817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6907925382590207723196845 2590472018471327896198817)
                  ·
                    refine ⟨1942854013853495922149113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2590472018471327896198817 1942854013853495922149113)
                    ·
                      refine ⟨1457140510390121941611835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1942854013853495922149113 1457140510390121941611835)
                      ·
                        rfl

theorem cell23_2837771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2, 2].length) (baseStart_2837771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837771 prefixEnd_2837771 := by exact prefixLift 2837771
  have htrace : WordTrace (prefixWord ++ tailWord_2837771) baseStart_2837771 baseEnd_2837771 := by
    simpa [prefixWord, tailWord_2837771, baseEnd_2837771] using wordTrace_append hprefix tailTrace_2837771
  have hstable : (prefixWord ++ tailWord_2837771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837771).length < 2 ^ (prefixWord ++ tailWord_2837771).sum := by decide
  have hdescent : baseEnd_2837771 < baseStart_2837771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837784 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2837784 : Nat := 118140960795 + 2837784 * 2 ^ 59
def prefixEnd_2837784 : Nat := 4983230072969 + 3 ^ 40 * 2837784 * 2
def baseEnd_2837784 : Nat := 1457147185638630390749275

theorem tailTrace_2837784 : CollatzResearch.WordTrace tailWord_2837784 prefixEnd_2837784 1457147185638630390749275 := by
  unfold tailWord_2837784
  simp only [CollatzResearch.WordTrace]
  refine ⟨51751242775600348883480203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69001657034133798511306937 51751242775600348883480203)
  ·
    refine ⟨77626864163400523325220305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51751242775600348883480203 77626864163400523325220305)
    ·
      refine ⟨58220148122550392493915229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77626864163400523325220305 58220148122550392493915229)
      ·
        refine ⟨21832555545956397185218211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58220148122550392493915229 21832555545956397185218211)
        ·
          refine ⟨32748833318934595777827317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21832555545956397185218211 32748833318934595777827317)
          ·
            refine ⟨3070203123650118354171311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32748833318934595777827317 3070203123650118354171311)
            ·
              refine ⟨4605304685475177531256967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070203123650118354171311 4605304685475177531256967)
              ·
                refine ⟨6907957028212766296885451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605304685475177531256967 6907957028212766296885451)
                ·
                  refine ⟨10361935542319149445328177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6907957028212766296885451 10361935542319149445328177)
                  ·
                    refine ⟨7771451656739362083996133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10361935542319149445328177 7771451656739362083996133)
                    ·
                      refine ⟨1457147185638630390749275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7771451656739362083996133 1457147185638630390749275)
                      ·
                        rfl

theorem cell23_2837784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2837784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837784 prefixEnd_2837784 := by exact prefixLift 2837784
  have htrace : WordTrace (prefixWord ++ tailWord_2837784) baseStart_2837784 baseEnd_2837784 := by
    simpa [prefixWord, tailWord_2837784, baseEnd_2837784] using wordTrace_append hprefix tailTrace_2837784
  have hstable : (prefixWord ++ tailWord_2837784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837784).length < 2 ^ (prefixWord ++ tailWord_2837784).sum := by decide
  have hdescent : baseEnd_2837784 < baseStart_2837784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837791 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_2837791 : Nat := 118140960795 + 2837791 * 2 ^ 59
def prefixEnd_2837791 : Nat := 4983230072969 + 3 ^ 40 * 2837791 * 2
def baseEnd_2837791 : Nat := 1457150780003211863361743

theorem tailTrace_2837791 : CollatzResearch.WordTrace tailWord_2837791 prefixEnd_2837791 1457150780003211863361743 := by
  unfold tailWord_2837791
  simp only [CollatzResearch.WordTrace]
  refine ⟨103502740862175337962465227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69001827241450225308310151 103502740862175337962465227)
  ·
    refine ⟨155254111293263006943697841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103502740862175337962465227 155254111293263006943697841)
    ·
      refine ⟨116440583469947255207773381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155254111293263006943697841 116440583469947255207773381)
      ·
        refine ⟨21832609400615110351457509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116440583469947255207773381 21832609400615110351457509)
        ·
          refine ⟨4093614262615333190898283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21832609400615110351457509 4093614262615333190898283)
          ·
            refine ⟨6140421393922999786347425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093614262615333190898283 6140421393922999786347425)
            ·
              refine ⟨4605316045442249839760569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6140421393922999786347425 4605316045442249839760569)
              ·
                refine ⟨3453987034081687379820427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605316045442249839760569 3453987034081687379820427)
                ·
                  refine ⟨5180980551122531069730641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453987034081687379820427 5180980551122531069730641)
                  ·
                    refine ⟨3885735413341898302297981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5180980551122531069730641 3885735413341898302297981)
                    ·
                      refine ⟨1457150780003211863361743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3885735413341898302297981 1457150780003211863361743)
                      ·
                        rfl

theorem cell23_2837791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_2837791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837791 prefixEnd_2837791 := by exact prefixLift 2837791
  have htrace : WordTrace (prefixWord ++ tailWord_2837791) baseStart_2837791 baseEnd_2837791 := by
    simpa [prefixWord, tailWord_2837791, baseEnd_2837791] using wordTrace_append hprefix tailTrace_2837791
  have hstable : (prefixWord ++ tailWord_2837791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837791).length < 2 ^ (prefixWord ++ tailWord_2837791).sum := by decide
  have hdescent : baseEnd_2837791 < baseStart_2837791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837847 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2837847 : Nat := 118140960795 + 2837847 * 2 ^ 59
def prefixEnd_2837847 : Nat := 4983230072969 + 3 ^ 40 * 2837847 * 2
def baseEnd_2837847 : Nat := 1457179534919863644261485

theorem tailTrace_2837847 : CollatzResearch.WordTrace tailWord_2837847 prefixEnd_2837847 1457179534919863644261485 := by
  unfold tailWord_2837847
  simp only [CollatzResearch.WordTrace]
  refine ⟨103504783349972459526503795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69003188899981639684335863 103504783349972459526503795)
  ·
    refine ⟨155257175024958689289755693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103504783349972459526503795 155257175024958689289755693)
    ·
      refine ⟨58221440634359508483658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155257175024958689289755693 58221440634359508483658385)
      ·
        refine ⟨43666080475769631362743789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58221440634359508483658385 43666080475769631362743789)
        ·
          refine ⟨16374780178413611761028921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43666080475769631362743789 16374780178413611761028921)
          ·
            refine ⟨12281085133810208820771691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16374780178413611761028921 12281085133810208820771691)
            ·
              refine ⟨18421627700715313231157537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281085133810208820771691 18421627700715313231157537)
              ·
                refine ⟨13816220775536484923368153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18421627700715313231157537 13816220775536484923368153)
                ·
                  refine ⟨10362165581652363692526115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13816220775536484923368153 10362165581652363692526115)
                  ·
                    refine ⟨15543248372478545538789173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10362165581652363692526115 15543248372478545538789173)
                    ·
                      refine ⟨1457179534919863644261485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15543248372478545538789173 1457179534919863644261485)
                      ·
                        rfl

theorem cell23_2837847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2837847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837847 prefixEnd_2837847 := by exact prefixLift 2837847
  have htrace : WordTrace (prefixWord ++ tailWord_2837847) baseStart_2837847 baseEnd_2837847 := by
    simpa [prefixWord, tailWord_2837847, baseEnd_2837847] using wordTrace_append hprefix tailTrace_2837847
  have hstable : (prefixWord ++ tailWord_2837847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837847).length < 2 ^ (prefixWord ++ tailWord_2837847).sum := by decide
  have hdescent : baseEnd_2837847 < baseStart_2837847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837884 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 5]
def baseStart_2837884 : Nat := 118140960795 + 2837884 * 2 ^ 59
def prefixEnd_2837884 : Nat := 4983230072969 + 3 ^ 40 * 2837884 * 2
def baseEnd_2837884 : Nat := 161910948189342222166535

theorem tailTrace_2837884 : CollatzResearch.WordTrace tailWord_2837884 prefixEnd_2837884 161910948189342222166535 := by
  unfold tailWord_2837884
  simp only [CollatzResearch.WordTrace]
  refine ⟨51753066425419207422800353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69004088567225609897067137 51753066425419207422800353)
  ·
    refine ⟨38814799819064405567100265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51753066425419207422800353 38814799819064405567100265)
    ·
      refine ⟨29111099864298304175325199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38814799819064405567100265 29111099864298304175325199)
      ·
        refine ⟨43666649796447456262987799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29111099864298304175325199 43666649796447456262987799)
        ·
          refine ⟨65499974694671184394481699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43666649796447456262987799 65499974694671184394481699)
          ·
            refine ⟨98249962042006776591722549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65499974694671184394481699 98249962042006776591722549)
            ·
              refine ⟨9210933941438135305473989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98249962042006776591722549 9210933941438135305473989)
              ·
                refine ⟨1727050114019650369776373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9210933941438135305473989 1727050114019650369776373)
                ·
                  refine ⟨161910948189342222166535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727050114019650369776373 161910948189342222166535)
                  ·
                    rfl

theorem cell23_2837884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_2837884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837884 prefixEnd_2837884 := by exact prefixLift 2837884
  have htrace : WordTrace (prefixWord ++ tailWord_2837884) baseStart_2837884 baseEnd_2837884 := by
    simpa [prefixWord, tailWord_2837884, baseEnd_2837884] using wordTrace_append hprefix tailTrace_2837884
  have hstable : (prefixWord ++ tailWord_2837884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837884).length < 2 ^ (prefixWord ++ tailWord_2837884).sum := by decide
  have hdescent : baseEnd_2837884 < baseStart_2837884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837944 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_2837944 : Nat := 118140960795 + 2837944 * 2 ^ 59
def prefixEnd_2837944 : Nat := 4983230072969 + 3 ^ 40 * 2837944 * 2
def baseEnd_2837944 : Nat := 485743114181116588249513

theorem tailTrace_2837944 : CollatzResearch.WordTrace tailWord_2837944 prefixEnd_2837944 485743114181116588249513 := by
  unfold tailWord_2837944
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754160615310522546392443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69005547487080696728523257 51754160615310522546392443)
  ·
    refine ⟨77631240922965783819588665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51754160615310522546392443 77631240922965783819588665)
    ·
      refine ⟨58223430692224337864691499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77631240922965783819588665 58223430692224337864691499)
      ·
        refine ⟨87335146038336506797037249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58223430692224337864691499 87335146038336506797037249)
        ·
          refine ⟨65501359528752380097777937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87335146038336506797037249 65501359528752380097777937)
          ·
            refine ⟨49126019646564285073333453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65501359528752380097777937 49126019646564285073333453)
            ·
              refine ⟨18422257367461606902500045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49126019646564285073333453 18422257367461606902500045)
              ·
                refine ⟨6908346512798102588437517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18422257367461606902500045 6908346512798102588437517)
                ·
                  refine ⟨2590629942299288470664069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6908346512798102588437517 2590629942299288470664069)
                  ·
                    refine ⟨485743114181116588249513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590629942299288470664069 485743114181116588249513)
                    ·
                      rfl

theorem cell23_2837944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_2837944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837944 prefixEnd_2837944 := by exact prefixLift 2837944
  have htrace : WordTrace (prefixWord ++ tailWord_2837944) baseStart_2837944 baseEnd_2837944 := by
    simpa [prefixWord, tailWord_2837944, baseEnd_2837944] using wordTrace_append hprefix tailTrace_2837944
  have hstable : (prefixWord ++ tailWord_2837944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837944).length < 2 ^ (prefixWord ++ tailWord_2837944).sum := by decide
  have hdescent : baseEnd_2837944 < baseStart_2837944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837978 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_2837978 : Nat := 118140960795 + 2837978 * 2 ^ 59
def prefixEnd_2837978 : Nat := 4983230072969 + 3 ^ 40 * 2837978 * 2
def baseEnd_2837978 : Nat := 485748933628534210574461

theorem tailTrace_2837978 : CollatzResearch.WordTrace tailWord_2837978 prefixEnd_2837978 485748933628534210574461 := by
  unfold tailWord_2837978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877390328124467224880647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69006374208331912599681725 25877390328124467224880647)
  ·
    refine ⟨38816085492186700837320971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25877390328124467224880647 38816085492186700837320971)
    ·
      refine ⟨58224128238280051255981457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38816085492186700837320971 58224128238280051255981457)
      ·
        refine ⟨43668096178710038441986093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58224128238280051255981457 43668096178710038441986093)
        ·
          refine ⟨16375536067016264415744785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43668096178710038441986093 16375536067016264415744785)
          ·
            refine ⟨12281652050262198311808589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16375536067016264415744785 12281652050262198311808589)
            ·
              refine ⟨4605619518848324366928221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12281652050262198311808589 4605619518848324366928221)
              ·
                refine ⟨1727107319568121637598083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605619518848324366928221 1727107319568121637598083)
                ·
                  refine ⟨2590660979352182456397125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727107319568121637598083 2590660979352182456397125)
                  ·
                    refine ⟨485748933628534210574461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590660979352182456397125 485748933628534210574461)
                    ·
                      rfl

theorem cell23_2837978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_2837978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2837978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2837978 prefixEnd_2837978 := by exact prefixLift 2837978
  have htrace : WordTrace (prefixWord ++ tailWord_2837978) baseStart_2837978 baseEnd_2837978 := by
    simpa [prefixWord, tailWord_2837978, baseEnd_2837978] using wordTrace_append hprefix tailTrace_2837978
  have hstable : (prefixWord ++ tailWord_2837978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837978).length < 2 ^ (prefixWord ++ tailWord_2837978).sum := by decide
  have hdescent : baseEnd_2837978 < baseStart_2837978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838071 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_2838071 : Nat := 118140960795 + 2838071 * 2 ^ 59
def prefixEnd_2838071 : Nat := 4983230072969 + 3 ^ 40 * 2838071 * 2
def baseEnd_2838071 : Nat := 1457294554586470767860455

theorem tailTrace_2838071 : CollatzResearch.WordTrace tailWord_2838071 prefixEnd_2838071 1457294554586470767860455 := by
  unfold tailWord_2838071
  simp only [CollatzResearch.WordTrace]
  refine ⟨103512953301160945782658067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69008635534107297188438711 103512953301160945782658067)
  ·
    refine ⟨155269429951741418673987101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103512953301160945782658067 155269429951741418673987101)
    ·
      refine ⟨58226036231903032002745163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155269429951741418673987101 58226036231903032002745163)
      ·
        refine ⟨87339054347854548004117745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58226036231903032002745163 87339054347854548004117745)
        ·
          refine ⟨65504290760890911003088309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87339054347854548004117745 65504290760890911003088309)
          ·
            refine ⟨6141027258833522906539529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65504290760890911003088309 6141027258833522906539529)
            ·
              refine ⟨4605770444125142179904647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141027258833522906539529 4605770444125142179904647)
              ·
                refine ⟨6908655666187713269856971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605770444125142179904647 6908655666187713269856971)
                ·
                  refine ⟨10362983499281569904785457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908655666187713269856971 10362983499281569904785457)
                  ·
                    refine ⟨7772237624461177428589093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10362983499281569904785457 7772237624461177428589093)
                    ·
                      refine ⟨1457294554586470767860455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7772237624461177428589093 1457294554586470767860455)
                      ·
                        rfl

theorem cell23_2838071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_2838071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838071 prefixEnd_2838071 := by exact prefixLift 2838071
  have htrace : WordTrace (prefixWord ++ tailWord_2838071) baseStart_2838071 baseEnd_2838071 := by
    simpa [prefixWord, tailWord_2838071, baseEnd_2838071] using wordTrace_append hprefix tailTrace_2838071
  have hstable : (prefixWord ++ tailWord_2838071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838071).length < 2 ^ (prefixWord ++ tailWord_2838071).sum := by decide
  have hdescent : baseEnd_2838071 < baseStart_2838071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838081 : List Nat := [1, 2, 5, 1, 1, 1, 5, 7]
def baseStart_2838081 : Nat := 118140960795 + 2838081 * 2 ^ 59
def prefixEnd_2838081 : Nat := 4983230072969 + 3 ^ 40 * 2838081 * 2
def baseEnd_2838081 : Nat := 53974062570111693656867

theorem tailTrace_2838081 : CollatzResearch.WordTrace tailWord_2838081 prefixEnd_2838081 53974062570111693656867 := by
  unfold tailWord_2838081
  simp only [CollatzResearch.WordTrace]
  refine ⟨103513318031124717490522097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69008878687416478327014731 103513318031124717490522097)
  ·
    refine ⟨77634988523343538117891573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103513318031124717490522097 77634988523343538117891573)
    ·
      refine ⟨7278280174063456698552335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77634988523343538117891573 7278280174063456698552335)
      ·
        refine ⟨10917420261095185047828503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7278280174063456698552335 10917420261095185047828503)
        ·
          refine ⟨16376130391642777571742755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917420261095185047828503 16376130391642777571742755)
          ·
            refine ⟨24564195587464166357614133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16376130391642777571742755 24564195587464166357614133)
            ·
              refine ⟨2302893336324765596026325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24564195587464166357614133 2302893336324765596026325)
              ·
                refine ⟨53974062570111693656867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2302893336324765596026325 53974062570111693656867)
                ·
                  rfl

theorem cell23_2838081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 7].length) (baseStart_2838081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838081 prefixEnd_2838081 := by exact prefixLift 2838081
  have htrace : WordTrace (prefixWord ++ tailWord_2838081) baseStart_2838081 baseEnd_2838081 := by
    simpa [prefixWord, tailWord_2838081, baseEnd_2838081] using wordTrace_append hprefix tailTrace_2838081
  have hstable : (prefixWord ++ tailWord_2838081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838081).length < 2 ^ (prefixWord ++ tailWord_2838081).sum := by decide
  have hdescent : baseEnd_2838081 < baseStart_2838081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838091 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 3]
def baseStart_2838091 : Nat := 118140960795 + 2838091 * 2 ^ 59
def prefixEnd_2838091 : Nat := 4983230072969 + 3 ^ 40 * 2838091 * 2
def baseEnd_2838091 : Nat := 1457304824199560689610363

theorem tailTrace_2838091 : CollatzResearch.WordTrace tailWord_2838091 prefixEnd_2838091 1457304824199560689610363 := by
  unfold tailWord_2838091
  simp only [CollatzResearch.WordTrace]
  refine ⟨103513682761088489198386127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69009121840725659465590751 103513682761088489198386127)
  ·
    refine ⟨155270524141632733797579191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103513682761088489198386127 155270524141632733797579191)
    ·
      refine ⟨232905786212449100696368787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155270524141632733797579191 232905786212449100696368787)
      ·
        refine ⟨349358679318673651044553181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232905786212449100696368787 349358679318673651044553181)
        ·
          refine ⟨131009504744502619141707443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349358679318673651044553181 131009504744502619141707443)
          ·
            refine ⟨196514257116753928712561165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131009504744502619141707443 196514257116753928712561165)
            ·
              refine ⟨73692846418782723267210437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196514257116753928712561165 73692846418782723267210437)
              ·
                refine ⟨13817408703521760612601957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73692846418782723267210437 13817408703521760612601957)
                ·
                  refine ⟨2590764131910330114862867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13817408703521760612601957 2590764131910330114862867)
                  ·
                    refine ⟨3886146197865495172294301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590764131910330114862867 3886146197865495172294301)
                    ·
                      refine ⟨1457304824199560689610363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886146197865495172294301 1457304824199560689610363)
                      ·
                        rfl

theorem cell23_2838091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 3].length) (baseStart_2838091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838091 prefixEnd_2838091 := by exact prefixLift 2838091
  have htrace : WordTrace (prefixWord ++ tailWord_2838091) baseStart_2838091 baseEnd_2838091 := by
    simpa [prefixWord, tailWord_2838091, baseEnd_2838091] using wordTrace_append hprefix tailTrace_2838091
  have hstable : (prefixWord ++ tailWord_2838091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838091).length < 2 ^ (prefixWord ++ tailWord_2838091).sum := by decide
  have hdescent : baseEnd_2838091 < baseStart_2838091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838092 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_2838092 : Nat := 118140960795 + 2838092 * 2 ^ 59
def prefixEnd_2838092 : Nat := 4983230072969 + 3 ^ 40 * 2838092 * 2
def baseEnd_2838092 : Nat := 1457305337680215185697859

theorem tailTrace_2838092 : CollatzResearch.WordTrace tailWord_2838092 prefixEnd_2838092 1457305337680215185697859 := by
  unfold tailWord_2838092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51756859617042433184586265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69009146156056577579448353 51756859617042433184586265)
  ·
    refine ⟨38817644712781824888439699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51756859617042433184586265 38817644712781824888439699)
    ·
      refine ⟨58226467069172737332659549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38817644712781824888439699 58226467069172737332659549)
      ·
        refine ⟨21834925150939776499747331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58226467069172737332659549 21834925150939776499747331)
        ·
          refine ⟨32752387726409664749620997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21834925150939776499747331 32752387726409664749620997)
          ·
            refine ⟨6141072698701812140553937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32752387726409664749620997 6141072698701812140553937)
            ·
              refine ⟨4605804524026359105415453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141072698701812140553937 4605804524026359105415453)
              ·
                refine ⟨1727176696509884664530795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605804524026359105415453 1727176696509884664530795)
                ·
                  refine ⟨2590765044764826996796193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727176696509884664530795 2590765044764826996796193)
                  ·
                    refine ⟨1943073783573620247597145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2590765044764826996796193 1943073783573620247597145)
                    ·
                      refine ⟨1457305337680215185697859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943073783573620247597145 1457305337680215185697859)
                      ·
                        rfl

theorem cell23_2838092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_2838092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838092 prefixEnd_2838092 := by exact prefixLift 2838092
  have htrace : WordTrace (prefixWord ++ tailWord_2838092) baseStart_2838092 baseEnd_2838092 := by
    simpa [prefixWord, tailWord_2838092, baseEnd_2838092] using wordTrace_append hprefix tailTrace_2838092
  have hstable : (prefixWord ++ tailWord_2838092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838092).length < 2 ^ (prefixWord ++ tailWord_2838092).sum := by decide
  have hdescent : baseEnd_2838092 < baseStart_2838092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838102 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2838102 : Nat := 118140960795 + 2838102 * 2 ^ 59
def prefixEnd_2838102 : Nat := 4983230072969 + 3 ^ 40 * 2838102 * 2
def baseEnd_2838102 : Nat := 485770157495586715524271

theorem tailTrace_2838102 : CollatzResearch.WordTrace tailWord_2838102 prefixEnd_2838102 485770157495586715524271 := by
  unfold tailWord_2838102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469630247753039879814785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69009389309365758718024373 6469630247753039879814785)
  ·
    refine ⟨4852222685814779909861089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6469630247753039879814785 4852222685814779909861089)
    ·
      refine ⟨3639167014361084932395817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4852222685814779909861089 3639167014361084932395817)
      ·
        refine ⟨2729375260770813699296863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639167014361084932395817 2729375260770813699296863)
        ·
          refine ⟨4094062891156220548945295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729375260770813699296863 4094062891156220548945295)
          ·
            refine ⟨6141094336734330823417943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094062891156220548945295 6141094336734330823417943)
            ·
              refine ⟨9211641505101496235126915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141094336734330823417943 9211641505101496235126915)
              ·
                refine ⟨13817462257652244352690373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211641505101496235126915 13817462257652244352690373)
                ·
                  refine ⟨2590774173309795816129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13817462257652244352690373 2590774173309795816129445)
                  ·
                    refine ⟨485770157495586715524271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590774173309795816129445 485770157495586715524271)
                    ·
                      rfl

theorem cell23_2838102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2838102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838102 prefixEnd_2838102 := by exact prefixLift 2838102
  have htrace : WordTrace (prefixWord ++ tailWord_2838102) baseStart_2838102 baseEnd_2838102 := by
    simpa [prefixWord, tailWord_2838102, baseEnd_2838102] using wordTrace_append hprefix tailTrace_2838102
  have hstable : (prefixWord ++ tailWord_2838102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838102).length < 2 ^ (prefixWord ++ tailWord_2838102).sum := by decide
  have hdescent : baseEnd_2838102 < baseStart_2838102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838109 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2838109 : Nat := 118140960795 + 2838109 * 2 ^ 59
def prefixEnd_2838109 : Nat := 4983230072969 + 3 ^ 40 * 2838109 * 2
def baseEnd_2838109 : Nat := 1457314066851341619185281

theorem tailTrace_2838109 : CollatzResearch.WordTrace tailWord_2838109 prefixEnd_2838109 1457314066851341619185281 := by
  unfold tailWord_2838109
  simp only [CollatzResearch.WordTrace]
  refine ⟨103514339275023278272541381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69009559516682185515027587 103514339275023278272541381)
  ·
    refine ⟨19408938614066864676101509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103514339275023278272541381 19408938614066864676101509)
    ·
      refine ⟨3639175990137537126769033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19408938614066864676101509 3639175990137537126769033)
      ·
        refine ⟨2729381992603152845076775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639175990137537126769033 2729381992603152845076775)
        ·
          refine ⟨4094072988904729267615163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729381992603152845076775 4094072988904729267615163)
          ·
            refine ⟨6141109483357093901422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094072988904729267615163 6141109483357093901422745)
            ·
              refine ⟨4605832112517820426067059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141109483357093901422745 4605832112517820426067059)
              ·
                refine ⟨6908748168776730639100589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605832112517820426067059 6908748168776730639100589)
                ·
                  refine ⟨2590780563291273989662721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6908748168776730639100589 2590780563291273989662721)
                  ·
                    refine ⟨1943085422468455492247041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2590780563291273989662721 1943085422468455492247041)
                    ·
                      refine ⟨1457314066851341619185281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943085422468455492247041 1457314066851341619185281)
                      ·
                        rfl

theorem cell23_2838109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2838109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838109 prefixEnd_2838109 := by exact prefixLift 2838109
  have htrace : WordTrace (prefixWord ++ tailWord_2838109) baseStart_2838109 baseEnd_2838109 := by
    simpa [prefixWord, tailWord_2838109, baseEnd_2838109] using wordTrace_append hprefix tailTrace_2838109
  have hstable : (prefixWord ++ tailWord_2838109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838109).length < 2 ^ (prefixWord ++ tailWord_2838109).sum := by decide
  have hdescent : baseEnd_2838109 < baseStart_2838109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838125 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2838125 : Nat := 118140960795 + 2838125 * 2 ^ 59
def prefixEnd_2838125 : Nat := 4983230072969 + 3 ^ 40 * 2838125 * 2
def baseEnd_2838125 : Nat := 1457322282541813556585207

theorem tailTrace_2838125 : CollatzResearch.WordTrace tailWord_2838125 prefixEnd_2838125 1457322282541813556585207 := by
  unfold tailWord_2838125
  simp only [CollatzResearch.WordTrace]
  refine ⟨103514922842965313005123829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69009948561976875336749219 103514922842965313005123829)
  ·
    refine ⟨9704524016527998094230359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103514922842965313005123829 9704524016527998094230359)
    ·
      refine ⟨14556786024791997141345539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9704524016527998094230359 14556786024791997141345539)
      ·
        refine ⟨21835179037187995712018309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14556786024791997141345539 21835179037187995712018309)
        ·
          refine ⟨4094096069472749196003433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21835179037187995712018309 4094096069472749196003433)
          ·
            refine ⟨3070572052104561897002575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4094096069472749196003433 3070572052104561897002575)
            ·
              refine ⟨4605858078156842845503863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070572052104561897002575 4605858078156842845503863)
              ·
                refine ⟨6908787117235264268255795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605858078156842845503863 6908787117235264268255795)
                ·
                  refine ⟨10363180675852896402383693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908787117235264268255795 10363180675852896402383693)
                  ·
                    refine ⟨3886192753444836150893885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10363180675852896402383693 3886192753444836150893885)
                    ·
                      refine ⟨1457322282541813556585207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886192753444836150893885 1457322282541813556585207)
                      ·
                        rfl

theorem cell23_2838125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2838125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838125 prefixEnd_2838125 := by exact prefixLift 2838125
  have htrace : WordTrace (prefixWord ++ tailWord_2838125) baseStart_2838125 baseEnd_2838125 := by
    simpa [prefixWord, tailWord_2838125, baseEnd_2838125] using wordTrace_append hprefix tailTrace_2838125
  have hstable : (prefixWord ++ tailWord_2838125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838125).length < 2 ^ (prefixWord ++ tailWord_2838125).sum := by decide
  have hdescent : baseEnd_2838125 < baseStart_2838125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838151 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2838151 : Nat := 118140960795 + 2838151 * 2 ^ 59
def prefixEnd_2838151 : Nat := 4983230072969 + 3 ^ 40 * 2838151 * 2
def baseEnd_2838151 : Nat := 1457335633038830454860087

theorem tailTrace_2838151 : CollatzResearch.WordTrace tailWord_2838151 prefixEnd_2838151 1457335633038830454860087 := by
  unfold tailWord_2838151
  simp only [CollatzResearch.WordTrace]
  refine ⟨103515871140871119445570307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69010580760580746297046871 103515871140871119445570307)
  ·
    refine ⟨155273806711306679168355461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103515871140871119445570307 155273806711306679168355461)
    ·
      refine ⟨29113838758370002344066649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155273806711306679168355461 29113838758370002344066649)
      ·
        refine ⟨21835379068777501758049987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29113838758370002344066649 21835379068777501758049987)
        ·
          refine ⟨32753068603166252637074981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21835379068777501758049987 32753068603166252637074981)
          ·
            refine ⟨6141200363093672369451559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32753068603166252637074981 6141200363093672369451559)
            ·
              refine ⟨9211800544640508554177339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141200363093672369451559 9211800544640508554177339)
              ·
                refine ⟨13817700816960762831266009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211800544640508554177339 13817700816960762831266009)
                ·
                  refine ⟨10363275612720572123449507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13817700816960762831266009 10363275612720572123449507)
                  ·
                    refine ⟨15544913419080858185174261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10363275612720572123449507 15544913419080858185174261)
                    ·
                      refine ⟨1457335633038830454860087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15544913419080858185174261 1457335633038830454860087)
                      ·
                        rfl

theorem cell23_2838151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2838151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838151 prefixEnd_2838151 := by exact prefixLift 2838151
  have htrace : WordTrace (prefixWord ++ tailWord_2838151) baseStart_2838151 baseEnd_2838151 := by
    simpa [prefixWord, tailWord_2838151, baseEnd_2838151] using wordTrace_append hprefix tailTrace_2838151
  have hstable : (prefixWord ++ tailWord_2838151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838151).length < 2 ^ (prefixWord ++ tailWord_2838151).sum := by decide
  have hdescent : baseEnd_2838151 < baseStart_2838151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838181 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_2838181 : Nat := 118140960795 + 2838181 * 2 ^ 59
def prefixEnd_2838181 : Nat := 4983230072969 + 3 ^ 40 * 2838181 * 2
def baseEnd_2838181 : Nat := 1457351037458465337484949

theorem tailTrace_2838181 : CollatzResearch.WordTrace tailWord_2838181 prefixEnd_2838181 1457351037458465337484949 := by
  unfold tailWord_2838181
  simp only [CollatzResearch.WordTrace]
  refine ⟨103516965330762434569162397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69011310220508289712774931 103516965330762434569162397)
  ·
    refine ⟨38818861999035912963435899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103516965330762434569162397 38818861999035912963435899)
    ·
      refine ⟨58228292998553869445153849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38818861999035912963435899 58228292998553869445153849)
      ·
        refine ⟨43671219748915402083865387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58228292998553869445153849 43671219748915402083865387)
        ·
          refine ⟨65506829623373103125798081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43671219748915402083865387 65506829623373103125798081)
          ·
            refine ⟨49130122217529827344348561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65506829623373103125798081 49130122217529827344348561)
            ·
              refine ⟨36847591663147370508261421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49130122217529827344348561 36847591663147370508261421)
              ·
                refine ⟨13817846873680263940598033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36847591663147370508261421 13817846873680263940598033)
                ·
                  refine ⟨10363385155260197955448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13817846873680263940598033 10363385155260197955448525)
                  ·
                    refine ⟨3886269433222574233293197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10363385155260197955448525 3886269433222574233293197)
                    ·
                      refine ⟨1457351037458465337484949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886269433222574233293197 1457351037458465337484949)
                      ·
                        rfl

theorem cell23_2838181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_2838181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838181 prefixEnd_2838181 := by exact prefixLift 2838181
  have htrace : WordTrace (prefixWord ++ tailWord_2838181) baseStart_2838181 baseEnd_2838181 := by
    simpa [prefixWord, tailWord_2838181, baseEnd_2838181] using wordTrace_append hprefix tailTrace_2838181
  have hstable : (prefixWord ++ tailWord_2838181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838181).length < 2 ^ (prefixWord ++ tailWord_2838181).sum := by decide
  have hdescent : baseEnd_2838181 < baseStart_2838181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838201 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_2838201 : Nat := 118140960795 + 2838201 * 2 ^ 59
def prefixEnd_2838201 : Nat := 4983230072969 + 3 ^ 40 * 2838201 * 2
def baseEnd_2838201 : Nat := 485787102357185086411619

theorem tailTrace_2838201 : CollatzResearch.WordTrace tailWord_2838201 prefixEnd_2838201 485787102357185086411619 := by
  unfold tailWord_2838201
  simp only [CollatzResearch.WordTrace]
  refine ⟨103517694790689977984890457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69011796527126651989926971 103517694790689977984890457)
  ·
    refine ⟨77638271093017483488667843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103517694790689977984890457 77638271093017483488667843)
    ·
      refine ⟨116457406639526225233001765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77638271093017483488667843 116457406639526225233001765)
      ·
        refine ⟨21835763744911167231187831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116457406639526225233001765 21835763744911167231187831)
        ·
          refine ⟨32753645617366750846781747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21835763744911167231187831 32753645617366750846781747)
          ·
            refine ⟨49130468426050126270172621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32753645617366750846781747 49130468426050126270172621)
            ·
              refine ⟨18423925659768797351314733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49130468426050126270172621 18423925659768797351314733)
              ·
                refine ⟨6908972122413299006743025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18423925659768797351314733 6908972122413299006743025)
                ·
                  refine ⟨5181729091809974255057269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6908972122413299006743025 5181729091809974255057269)
                  ·
                    refine ⟨485787102357185086411619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5181729091809974255057269 485787102357185086411619)
                    ·
                      rfl

theorem cell23_2838201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_2838201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838201 prefixEnd_2838201 := by exact prefixLift 2838201
  have htrace : WordTrace (prefixWord ++ tailWord_2838201) baseStart_2838201 baseEnd_2838201 := by
    simpa [prefixWord, tailWord_2838201, baseEnd_2838201] using wordTrace_append hprefix tailTrace_2838201
  have hstable : (prefixWord ++ tailWord_2838201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838201).length < 2 ^ (prefixWord ++ tailWord_2838201).sum := by decide
  have hdescent : baseEnd_2838201 < baseStart_2838201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838228 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2838228 : Nat := 118140960795 + 2838228 * 2 ^ 59
def prefixEnd_2838228 : Nat := 4983230072969 + 3 ^ 40 * 2838228 * 2
def baseEnd_2838228 : Nat := 1457375171049226653597233

theorem tailTrace_2838228 : CollatzResearch.WordTrace tailWord_2838228 prefixEnd_2838228 1457375171049226653597233 := by
  unfold tailWord_2838228
  simp only [CollatzResearch.WordTrace]
  refine ⟨51759339780796080798061669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69012453041061441064082225 51759339780796080798061669)
  ·
    refine ⟨9704876208899265149636563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51759339780796080798061669 9704876208899265149636563)
    ·
      refine ⟨14557314313348897724454845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9704876208899265149636563 14557314313348897724454845)
      ·
        refine ⟨5458992867505836646670567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14557314313348897724454845 5458992867505836646670567)
        ·
          refine ⟨8188489301258754970005851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458992867505836646670567 8188489301258754970005851)
          ·
            refine ⟨12282733951888132455008777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188489301258754970005851 12282733951888132455008777)
            ·
              refine ⟨9212050463916099341256583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12282733951888132455008777 9212050463916099341256583)
              ·
                refine ⟨13818075695874149011884875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212050463916099341256583 13818075695874149011884875)
                ·
                  refine ⟨20727113543811223517827313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13818075695874149011884875 20727113543811223517827313)
                  ·
                    refine ⟨15545335157858417638370485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20727113543811223517827313 15545335157858417638370485)
                    ·
                      refine ⟨1457375171049226653597233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15545335157858417638370485 1457375171049226653597233)
                      ·
                        rfl

theorem cell23_2838228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2838228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838228 prefixEnd_2838228 := by exact prefixLift 2838228
  have htrace : WordTrace (prefixWord ++ tailWord_2838228) baseStart_2838228 baseEnd_2838228 := by
    simpa [prefixWord, tailWord_2838228, baseEnd_2838228] using wordTrace_append hprefix tailTrace_2838228
  have hstable : (prefixWord ++ tailWord_2838228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838228).length < 2 ^ (prefixWord ++ tailWord_2838228).sum := by decide
  have hdescent : baseEnd_2838228 < baseStart_2838228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838248 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2838248 : Nat := 118140960795 + 2838248 * 2 ^ 59
def prefixEnd_2838248 : Nat := 4983230072969 + 3 ^ 40 * 2838248 * 2
def baseEnd_2838248 : Nat := 485795146887438858449047

theorem tailTrace_2838248 : CollatzResearch.WordTrace tailWord_2838248 prefixEnd_2838248 485795146887438858449047 := by
  unfold tailWord_2838248
  simp only [CollatzResearch.WordTrace]
  refine ⟨51759704510759852505925699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69012939347679803341234265 51759704510759852505925699)
  ·
    refine ⟨77639556766139778758888549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51759704510759852505925699 77639556766139778758888549)
    ·
      refine ⟨14557416893651208517291603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77639556766139778758888549 14557416893651208517291603)
      ·
        refine ⟨21836125340476812775937405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14557416893651208517291603 21836125340476812775937405)
        ·
          refine ⟨8188547002678804790976527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21836125340476812775937405 8188547002678804790976527)
          ·
            refine ⟨12282820504018207186464791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188547002678804790976527 12282820504018207186464791)
            ·
              refine ⟨18424230756027310779697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12282820504018207186464791 18424230756027310779697187)
              ·
                refine ⟨27636346134040966169545781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18424230756027310779697187 27636346134040966169545781)
                ·
                  refine ⟨2590907450066340578394917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27636346134040966169545781 2590907450066340578394917)
                  ·
                    refine ⟨485795146887438858449047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590907450066340578394917 485795146887438858449047)
                    ·
                      rfl

theorem cell23_2838248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2838248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838248 prefixEnd_2838248 := by exact prefixLift 2838248
  have htrace : WordTrace (prefixWord ++ tailWord_2838248) baseStart_2838248 baseEnd_2838248 := by
    simpa [prefixWord, tailWord_2838248, baseEnd_2838248] using wordTrace_append hprefix tailTrace_2838248
  have hstable : (prefixWord ++ tailWord_2838248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838248).length < 2 ^ (prefixWord ++ tailWord_2838248).sum := by decide
  have hdescent : baseEnd_2838248 < baseStart_2838248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838258 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2838258 : Nat := 118140960795 + 2838258 * 2 ^ 59
def prefixEnd_2838258 : Nat := 4983230072969 + 3 ^ 40 * 2838258 * 2
def baseEnd_2838258 : Nat := 1457390575468861536222095

theorem tailTrace_2838258 : CollatzResearch.WordTrace tailWord_2838258 prefixEnd_2838258 1457390575468861536222095 := by
  unfold tailWord_2838258
  simp only [CollatzResearch.WordTrace]
  refine ⟨25879943437870869179928857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69013182500988984479810285 25879943437870869179928857)
  ·
    refine ⟨19409957578403151884946643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25879943437870869179928857 19409957578403151884946643)
    ·
      refine ⟨29114936367604727827419965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19409957578403151884946643 29114936367604727827419965)
      ·
        refine ⟨10918101137851772935282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29114936367604727827419965 10918101137851772935282487)
        ·
          refine ⟨16377151706777659402923731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10918101137851772935282487 16377151706777659402923731)
          ·
            refine ⟨24565727560166489104385597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16377151706777659402923731 24565727560166489104385597)
            ·
              refine ⟨9212147835062433414144599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24565727560166489104385597 9212147835062433414144599)
              ·
                refine ⟨13818221752593650121216899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212147835062433414144599 13818221752593650121216899)
                ·
                  refine ⟨20727332628890475181825349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13818221752593650121216899 20727332628890475181825349)
                  ·
                    refine ⟨3886374867916964096592253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20727332628890475181825349 3886374867916964096592253)
                    ·
                      refine ⟨1457390575468861536222095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886374867916964096592253 1457390575468861536222095)
                      ·
                        rfl

theorem cell23_2838258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2838258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838258 prefixEnd_2838258 := by exact prefixLift 2838258
  have htrace : WordTrace (prefixWord ++ tailWord_2838258) baseStart_2838258 baseEnd_2838258 := by
    simpa [prefixWord, tailWord_2838258, baseEnd_2838258] using wordTrace_append hprefix tailTrace_2838258
  have hstable : (prefixWord ++ tailWord_2838258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838258).length < 2 ^ (prefixWord ++ tailWord_2838258).sum := by decide
  have hdescent : baseEnd_2838258 < baseStart_2838258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838291 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 3, 5]
def baseStart_2838291 : Nat := 118140960795 + 2838291 * 2 ^ 59
def prefixEnd_2838291 : Nat := 4983230072969 + 3 ^ 40 * 2838291 * 2
def baseEnd_2838291 : Nat := 485802506776819969036481

theorem tailTrace_2838291 : CollatzResearch.WordTrace tailWord_2838291 prefixEnd_2838291 485802506776819969036481 := by
  unfold tailWord_2838291
  simp only [CollatzResearch.WordTrace]
  refine ⟨103520977360363923355666727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69013984906909282237111151 103520977360363923355666727)
  ·
    refine ⟨155281466040545885033500091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103520977360363923355666727 155281466040545885033500091)
    ·
      refine ⟨232922199060818827550250137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155281466040545885033500091 232922199060818827550250137)
      ·
        refine ⟨174691649295614120662687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232922199060818827550250137 174691649295614120662687603)
        ·
          refine ⟨262037473943421180994031405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174691649295614120662687603 262037473943421180994031405)
          ·
            refine ⟨98264052728782942872761777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262037473943421180994031405 98264052728782942872761777)
            ·
              refine ⟨73698039546587207154571333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98264052728782942872761777 73698039546587207154571333)
              ·
                refine ⟨13818382414985101341482125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73698039546587207154571333 13818382414985101341482125)
                ·
                  refine ⟨5181893405619413003055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13818382414985101341482125 5181893405619413003055797)
                  ·
                    refine ⟨485802506776819969036481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5181893405619413003055797 485802506776819969036481)
                    ·
                      rfl

theorem cell23_2838291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].length) (baseStart_2838291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838291 prefixEnd_2838291 := by exact prefixLift 2838291
  have htrace : WordTrace (prefixWord ++ tailWord_2838291) baseStart_2838291 baseEnd_2838291 := by
    simpa [prefixWord, tailWord_2838291, baseEnd_2838291] using wordTrace_append hprefix tailTrace_2838291
  have hstable : (prefixWord ++ tailWord_2838291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838291).length < 2 ^ (prefixWord ++ tailWord_2838291).sum := by decide
  have hdescent : baseEnd_2838291 < baseStart_2838291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838295 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 6]
def baseStart_2838295 : Nat := 118140960795 + 2838295 * 2 ^ 59
def prefixEnd_2838295 : Nat := 4983230072969 + 3 ^ 40 * 2838295 * 2
def baseEnd_2838295 : Nat := 161934397139230876828825

theorem tailTrace_2838295 : CollatzResearch.WordTrace tailWord_2838295 prefixEnd_2838295 161934397139230876828825 := by
  unfold tailWord_2838295
  simp only [CollatzResearch.WordTrace]
  refine ⟨103521123252349432038812339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69014082168232954692541559 103521123252349432038812339)
  ·
    refine ⟨155281684878524148058218509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103521123252349432038812339 155281684878524148058218509)
    ·
      refine ⟨58230631829446555521831941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155281684878524148058218509 58230631829446555521831941)
      ·
        refine ⟨10918243468021229160343489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58230631829446555521831941 10918243468021229160343489)
        ·
          refine ⟨8188682601015921870257617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10918243468021229160343489 8188682601015921870257617)
          ·
            refine ⟨6141511950761941402693213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8188682601015921870257617 6141511950761941402693213)
            ·
              refine ⟨2303066981535728026009955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6141511950761941402693213 2303066981535728026009955)
              ·
                refine ⟨3454600472303592039014933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303066981535728026009955 3454600472303592039014933)
                ·
                  refine ⟨161934397139230876828825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3454600472303592039014933 161934397139230876828825)
                  ·
                    rfl

theorem cell23_2838295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 6].length) (baseStart_2838295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838295 prefixEnd_2838295 := by exact prefixLift 2838295
  have htrace : WordTrace (prefixWord ++ tailWord_2838295) baseStart_2838295 baseEnd_2838295 := by
    simpa [prefixWord, tailWord_2838295, baseEnd_2838295] using wordTrace_append hprefix tailTrace_2838295
  have hstable : (prefixWord ++ tailWord_2838295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838295).length < 2 ^ (prefixWord ++ tailWord_2838295).sum := by decide
  have hdescent : baseEnd_2838295 < baseStart_2838295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838305 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2838305 : Nat := 118140960795 + 2838305 * 2 ^ 59
def prefixEnd_2838305 : Nat := 4983230072969 + 3 ^ 40 * 2838305 * 2
def baseEnd_2838305 : Nat := 1457414709059622852334379

theorem tailTrace_2838305 : CollatzResearch.WordTrace tailWord_2838305 prefixEnd_2838305 1457414709059622852334379 := by
  unfold tailWord_2838305
  simp only [CollatzResearch.WordTrace]
  refine ⟨103521487982313203746676369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69014325321542135831117579 103521487982313203746676369)
  ·
    refine ⟨77641115986734902810007277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103521487982313203746676369 77641115986734902810007277)
    ·
      refine ⟨29115418495025588553752729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77641115986734902810007277 29115418495025588553752729)
      ·
        refine ⟨21836563871269191415314547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29115418495025588553752729 21836563871269191415314547)
        ·
          refine ⟨32754845806903787122971821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21836563871269191415314547 32754845806903787122971821)
          ·
            refine ⟨12283067177588920171114433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32754845806903787122971821 12283067177588920171114433)
            ·
              refine ⟨9212300383191690128335825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12283067177588920171114433 9212300383191690128335825)
              ·
                refine ⟨6909225287393767596251869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9212300383191690128335825 6909225287393767596251869)
                ·
                  refine ⟨2590959482772662848594451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6909225287393767596251869 2590959482772662848594451)
                  ·
                    refine ⟨3886439224158994272891677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590959482772662848594451 3886439224158994272891677)
                    ·
                      refine ⟨1457414709059622852334379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886439224158994272891677 1457414709059622852334379)
                      ·
                        rfl

theorem cell23_2838305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2838305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838305 prefixEnd_2838305 := by exact prefixLift 2838305
  have htrace : WordTrace (prefixWord ++ tailWord_2838305) baseStart_2838305 baseEnd_2838305 := by
    simpa [prefixWord, tailWord_2838305, baseEnd_2838305] using wordTrace_append hprefix tailTrace_2838305
  have hstable : (prefixWord ++ tailWord_2838305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838305).length < 2 ^ (prefixWord ++ tailWord_2838305).sum := by decide
  have hdescent : baseEnd_2838305 < baseStart_2838305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838339 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 1, 1, 3]
def baseStart_2838339 : Nat := 118140960795 + 2838339 * 2 ^ 59
def prefixEnd_2838339 : Nat := 4983230072969 + 3 ^ 40 * 2838339 * 2
def baseEnd_2838339 : Nat := 1457432167401875719309223

theorem tailTrace_2838339 : CollatzResearch.WordTrace tailWord_2838339 prefixEnd_2838339 1457432167401875719309223 := by
  unfold tailWord_2838339
  simp only [CollatzResearch.WordTrace]
  refine ⟨103522728064190027553414071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69015152042793351702276047 103522728064190027553414071)
  ·
    refine ⟨155284092096285041330121107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103522728064190027553414071 155284092096285041330121107)
    ·
      refine ⟨232926138144427561995181661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155284092096285041330121107 232926138144427561995181661)
      ·
        refine ⟨87347301804160335748193123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232926138144427561995181661 87347301804160335748193123)
        ·
          refine ⟨131020952706240503622289685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87347301804160335748193123 131020952706240503622289685)
          ·
            refine ⟨6141607158105023607294829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131020952706240503622289685 6141607158105023607294829)
            ·
              refine ⟨2303102684289383852735561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6141607158105023607294829 2303102684289383852735561)
              ·
                refine ⟨1727327013217037889551671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303102684289383852735561 1727327013217037889551671)
                ·
                  refine ⟨2590990519825556834327507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727327013217037889551671 2590990519825556834327507)
                  ·
                    refine ⟨3886485779738335251491261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590990519825556834327507 3886485779738335251491261)
                    ·
                      refine ⟨1457432167401875719309223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886485779738335251491261 1457432167401875719309223)
                      ·
                        rfl

theorem cell23_2838339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_2838339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838339 prefixEnd_2838339 := by exact prefixLift 2838339
  have htrace : WordTrace (prefixWord ++ tailWord_2838339) baseStart_2838339 baseEnd_2838339 := by
    simpa [prefixWord, tailWord_2838339, baseEnd_2838339] using wordTrace_append hprefix tailTrace_2838339
  have hstable : (prefixWord ++ tailWord_2838339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838339).length < 2 ^ (prefixWord ++ tailWord_2838339).sum := by decide
  have hdescent : baseEnd_2838339 < baseStart_2838339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838341 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2838341 : Nat := 118140960795 + 2838341 * 2 ^ 59
def prefixEnd_2838341 : Nat := 4983230072969 + 3 ^ 40 * 2838341 * 2
def baseEnd_2838341 : Nat := 1457433194363184711484213

theorem tailTrace_2838341 : CollatzResearch.WordTrace tailWord_2838341 prefixEnd_2838341 1457433194363184711484213 := by
  unfold tailWord_2838341
  simp only [CollatzResearch.WordTrace]
  refine ⟨103522801010182781894986877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69015200673455187929991251 103522801010182781894986877)
  ·
    refine ⟨38821050378818543210620079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103522801010182781894986877 38821050378818543210620079)
    ·
      refine ⟨58231575568227814815930119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38821050378818543210620079 58231575568227814815930119)
      ·
        refine ⟨87347363352341722223895179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58231575568227814815930119 87347363352341722223895179)
        ·
          refine ⟨131021045028512583335842769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87347363352341722223895179 131021045028512583335842769)
          ·
            refine ⟨98265783771384437501882077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131021045028512583335842769 98265783771384437501882077)
            ·
              refine ⟨36849668914269164063205779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98265783771384437501882077 36849668914269164063205779)
              ·
                refine ⟨55274503371403746094808669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36849668914269164063205779 55274503371403746094808669)
                ·
                  refine ⟨20727938764276404785553251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55274503371403746094808669 20727938764276404785553251)
                  ·
                    refine ⟨31091908146414607178329877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20727938764276404785553251 31091908146414607178329877)
                    ·
                      refine ⟨1457433194363184711484213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31091908146414607178329877 1457433194363184711484213)
                      ·
                        rfl

theorem cell23_2838341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2838341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838341 prefixEnd_2838341 := by exact prefixLift 2838341
  have htrace : WordTrace (prefixWord ++ tailWord_2838341) baseStart_2838341 baseEnd_2838341 := by
    simpa [prefixWord, tailWord_2838341, baseEnd_2838341] using wordTrace_append hprefix tailTrace_2838341
  have hstable : (prefixWord ++ tailWord_2838341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838341).length < 2 ^ (prefixWord ++ tailWord_2838341).sum := by decide
  have hdescent : baseEnd_2838341 < baseStart_2838341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838382 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2838382 : Nat := 118140960795 + 2838382 * 2 ^ 59
def prefixEnd_2838382 : Nat := 4983230072969 + 3 ^ 40 * 2838382 * 2
def baseEnd_2838382 : Nat := 1457454247070019051071525

theorem tailTrace_2838382 : CollatzResearch.WordTrace tailWord_2838382 prefixEnd_2838382 1457454247070019051071525 := by
  unfold tailWord_2838382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940537050379280737153675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69016197602022830598152933 12940537050379280737153675)
  ·
    refine ⟨19410805575568921105730513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12940537050379280737153675 19410805575568921105730513)
    ·
      refine ⟨14558104181676690829297885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19410805575568921105730513 14558104181676690829297885)
      ·
        refine ⟨5459289068128759060986707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14558104181676690829297885 5459289068128759060986707)
        ·
          refine ⟨8188933602193138591480061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459289068128759060986707 8188933602193138591480061)
          ·
            refine ⟨3070850100822426971805023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8188933602193138591480061 3070850100822426971805023)
            ·
              refine ⟨4606275151233640457707535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070850100822426971805023 4606275151233640457707535)
              ·
                refine ⟨6909412726850460686561303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606275151233640457707535 6909412726850460686561303)
                ·
                  refine ⟨10364119090275691029841955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6909412726850460686561303 10364119090275691029841955)
                  ·
                    refine ⟨15546178635413536544762933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10364119090275691029841955 15546178635413536544762933)
                    ·
                      refine ⟨1457454247070019051071525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15546178635413536544762933 1457454247070019051071525)
                      ·
                        rfl

theorem cell23_2838382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2838382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838382 prefixEnd_2838382 := by exact prefixLift 2838382
  have htrace : WordTrace (prefixWord ++ tailWord_2838382) baseStart_2838382 baseEnd_2838382 := by
    simpa [prefixWord, tailWord_2838382, baseEnd_2838382] using wordTrace_append hprefix tailTrace_2838382
  have hstable : (prefixWord ++ tailWord_2838382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838382).length < 2 ^ (prefixWord ++ tailWord_2838382).sum := by decide
  have hdescent : baseEnd_2838382 < baseStart_2838382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838390 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2838390 : Nat := 118140960795 + 2838390 * 2 ^ 59
def prefixEnd_2838390 : Nat := 4983230072969 + 3 ^ 40 * 2838390 * 2
def baseEnd_2838390 : Nat := 1457458354915255019771489

theorem tailTrace_2838390 : CollatzResearch.WordTrace tailWord_2838390 prefixEnd_2838390 1457458354915255019771489 := by
  unfold tailWord_2838390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470286761687828953970039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69016392124670175509013749 6470286761687828953970039)
  ·
    refine ⟨9705430142531743430955059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6470286761687828953970039 9705430142531743430955059)
    ·
      refine ⟨14558145213797615146432589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9705430142531743430955059 14558145213797615146432589)
      ·
        refine ⟨5459304455174105679912221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14558145213797615146432589 5459304455174105679912221)
        ·
          refine ⟨2047239170690289629967083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5459304455174105679912221 2047239170690289629967083)
          ·
            refine ⟨3070858756035434444950625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047239170690289629967083 3070858756035434444950625)
            ·
              refine ⟨2303144067026575833712969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070858756035434444950625 2303144067026575833712969)
              ·
                refine ⟨1727358050269931875284727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303144067026575833712969 1727358050269931875284727)
                ·
                  refine ⟨2591037075404897812927091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727358050269931875284727 2591037075404897812927091)
                  ·
                    refine ⟨3886555613107346719390637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591037075404897812927091 3886555613107346719390637)
                    ·
                      refine ⟨1457458354915255019771489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886555613107346719390637 1457458354915255019771489)
                      ·
                        rfl

theorem cell23_2838390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2838390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838390 prefixEnd_2838390 := by exact prefixLift 2838390
  have htrace : WordTrace (prefixWord ++ tailWord_2838390) baseStart_2838390 baseEnd_2838390 := by
    simpa [prefixWord, tailWord_2838390, baseEnd_2838390] using wordTrace_append hprefix tailTrace_2838390
  have hstable : (prefixWord ++ tailWord_2838390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838390).length < 2 ^ (prefixWord ++ tailWord_2838390).sum := by decide
  have hdescent : baseEnd_2838390 < baseStart_2838390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838391 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2838391 : Nat := 118140960795 + 2838391 * 2 ^ 59
def prefixEnd_2838391 : Nat := 4983230072969 + 3 ^ 40 * 2838391 * 2
def baseEnd_2838391 : Nat := 1457458868395909515858983

theorem tailTrace_2838391 : CollatzResearch.WordTrace tailWord_2838391 prefixEnd_2838391 1457458868395909515858983 := by
  unfold tailWord_2838391
  simp only [CollatzResearch.WordTrace]
  refine ⟨103524624660001640434307027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69016416440001093622871351 103524624660001640434307027)
  ·
    refine ⟨155286936990002460651460541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103524624660001640434307027 155286936990002460651460541)
    ·
      refine ⟨58232601371250922744297703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155286936990002460651460541 58232601371250922744297703)
      ·
        refine ⟨87348902056876384116446555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58232601371250922744297703 87348902056876384116446555)
        ·
          refine ⟨131023353085314576174669833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87348902056876384116446555 131023353085314576174669833)
          ·
            refine ⟨98267514813985932131002375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131023353085314576174669833 98267514813985932131002375)
            ·
              refine ⟨147401272220978898196503563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98267514813985932131002375 147401272220978898196503563)
              ·
                refine ⟨221101908331468347294755345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147401272220978898196503563 221101908331468347294755345)
                ·
                  refine ⟨165826431248601260471066509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221101908331468347294755345 165826431248601260471066509)
                  ·
                    refine ⟨62184911718225472676649941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165826431248601260471066509 62184911718225472676649941)
                    ·
                      refine ⟨1457458868395909515858983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62184911718225472676649941 1457458868395909515858983)
                      ·
                        rfl

theorem cell23_2838391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2838391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838391 prefixEnd_2838391 := by exact prefixLift 2838391
  have htrace : WordTrace (prefixWord ++ tailWord_2838391) baseStart_2838391 baseEnd_2838391 := by
    simpa [prefixWord, tailWord_2838391, baseEnd_2838391] using wordTrace_append hprefix tailTrace_2838391
  have hstable : (prefixWord ++ tailWord_2838391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838391).length < 2 ^ (prefixWord ++ tailWord_2838391).sum := by decide
  have hdescent : baseEnd_2838391 < baseStart_2838391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838405 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_2838405 : Nat := 118140960795 + 2838405 * 2 ^ 59
def prefixEnd_2838405 : Nat := 4983230072969 + 3 ^ 40 * 2838405 * 2
def baseEnd_2838405 : Nat := 1457466057125072461083919

theorem tailTrace_2838405 : CollatzResearch.WordTrace tailWord_2838405 prefixEnd_2838405 1457466057125072461083919 := by
  unfold tailWord_2838405
  simp only [CollatzResearch.WordTrace]
  refine ⟨103525135281950920825316669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69016756854633947216877779 103525135281950920825316669)
  ·
    refine ⟨38821925730731595309493751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103525135281950920825316669 38821925730731595309493751)
    ·
      refine ⟨58232888596097392964240627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38821925730731595309493751 58232888596097392964240627)
      ·
        refine ⟨87349332894146089446360941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58232888596097392964240627 87349332894146089446360941)
        ·
          refine ⟨32755999835304783542385353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87349332894146089446360941 32755999835304783542385353)
          ·
            refine ⟨24566999876478587656789015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32755999835304783542385353 24566999876478587656789015)
            ·
              refine ⟨36850499814717881485183523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24566999876478587656789015 36850499814717881485183523)
              ·
                refine ⟨55275749722076822227775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36850499814717881485183523 55275749722076822227775285)
                ·
                  refine ⟨5182101536444702083853933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55275749722076822227775285 5182101536444702083853933)
                  ·
                    refine ⟨1943288076166763281445225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5182101536444702083853933 1943288076166763281445225)
                    ·
                      refine ⟨1457466057125072461083919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943288076166763281445225 1457466057125072461083919)
                      ·
                        rfl

theorem cell23_2838405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_2838405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838405 prefixEnd_2838405 := by exact prefixLift 2838405
  have htrace : WordTrace (prefixWord ++ tailWord_2838405) baseStart_2838405 baseEnd_2838405 := by
    simpa [prefixWord, tailWord_2838405, baseEnd_2838405] using wordTrace_append hprefix tailTrace_2838405
  have hstable : (prefixWord ++ tailWord_2838405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838405).length < 2 ^ (prefixWord ++ tailWord_2838405).sum := by decide
  have hdescent : baseEnd_2838405 < baseStart_2838405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838430 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2838430 : Nat := 118140960795 + 2838430 * 2 ^ 59
def prefixEnd_2838430 : Nat := 4983230072969 + 3 ^ 40 * 2838430 * 2
def baseEnd_2838430 : Nat := 1457478894141434863271305

theorem tailTrace_2838430 : CollatzResearch.WordTrace tailWord_2838430 prefixEnd_2838430 1457478894141434863271305 := by
  unfold tailWord_2838430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940755888357543761872093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69017364737906900063317829 12940755888357543761872093)
  ·
    refine ⟨4852783458134078910702035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12940755888357543761872093 4852783458134078910702035)
    ·
      refine ⟨7279175187201118366053053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852783458134078910702035 7279175187201118366053053)
      ·
        refine ⟨2729690695200419387269895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7279175187201118366053053 2729690695200419387269895)
        ·
          refine ⟨4094536042800629080904843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729690695200419387269895 4094536042800629080904843)
          ·
            refine ⟨6141804064200943621357265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094536042800629080904843 6141804064200943621357265)
            ·
              refine ⟨4606353048150707716017949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141804064200943621357265 4606353048150707716017949)
              ·
                refine ⟨1727382393056515393506731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4606353048150707716017949 1727382393056515393506731)
                ·
                  refine ⟨2591073589584773090260097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727382393056515393506731 2591073589584773090260097)
                  ·
                    refine ⟨1943305192188579817695073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2591073589584773090260097 1943305192188579817695073)
                    ·
                      refine ⟨1457478894141434863271305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943305192188579817695073 1457478894141434863271305)
                      ·
                        rfl

theorem cell23_2838430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2838430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838430 prefixEnd_2838430 := by exact prefixLift 2838430
  have htrace : WordTrace (prefixWord ++ tailWord_2838430) baseStart_2838430 baseEnd_2838430 := by
    simpa [prefixWord, tailWord_2838430, baseEnd_2838430] using wordTrace_append hprefix tailTrace_2838430
  have hstable : (prefixWord ++ tailWord_2838430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838430).length < 2 ^ (prefixWord ++ tailWord_2838430).sum := by decide
  have hdescent : baseEnd_2838430 < baseStart_2838430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838439 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2838439 : Nat := 118140960795 + 2838439 * 2 ^ 59
def prefixEnd_2838439 : Nat := 4983230072969 + 3 ^ 40 * 2838439 * 2
def baseEnd_2838439 : Nat := 1457483515467325328058763

theorem tailTrace_2838439 : CollatzResearch.WordTrace tailWord_2838439 prefixEnd_2838439 1457483515467325328058763 := by
  unfold tailWord_2838439
  simp only [CollatzResearch.WordTrace]
  refine ⟨103526375363827744632054371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69017583575885163088036247 103526375363827744632054371)
  ·
    refine ⟨155289563045741616948081557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103526375363827744632054371 155289563045741616948081557)
    ·
      refine ⟨7279198267769138294441323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155289563045741616948081557 7279198267769138294441323)
      ·
        refine ⟨10918797401653707441661985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279198267769138294441323 10918797401653707441661985)
        ·
          refine ⟨8189098051240280581246489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10918797401653707441661985 8189098051240280581246489)
          ·
            refine ⟨6141823538430210435934867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8189098051240280581246489 6141823538430210435934867)
            ·
              refine ⟨9212735307645315653902301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141823538430210435934867 9212735307645315653902301)
              ·
                refine ⟨3454775740366993370213363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9212735307645315653902301 3454775740366993370213363)
                ·
                  refine ⟨5182163610550490055320045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454775740366993370213363 5182163610550490055320045)
                  ·
                    refine ⟨1943311353956433770745017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5182163610550490055320045 1943311353956433770745017)
                    ·
                      refine ⟨1457483515467325328058763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943311353956433770745017 1457483515467325328058763)
                      ·
                        rfl

theorem cell23_2838439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2838439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838439 prefixEnd_2838439 := by exact prefixLift 2838439
  have htrace : WordTrace (prefixWord ++ tailWord_2838439) baseStart_2838439 baseEnd_2838439 := by
    simpa [prefixWord, tailWord_2838439, baseEnd_2838439] using wordTrace_append hprefix tailTrace_2838439
  have hstable : (prefixWord ++ tailWord_2838439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838439).length < 2 ^ (prefixWord ++ tailWord_2838439).sum := by decide
  have hdescent : baseEnd_2838439 < baseStart_2838439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838488 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_2838488 : Nat := 118140960795 + 2838488 * 2 ^ 59
def prefixEnd_2838488 : Nat := 4983230072969 + 3 ^ 40 * 2838488 * 2
def baseEnd_2838488 : Nat := 485836225339798545448679

theorem tailTrace_2838488 : CollatzResearch.WordTrace tailWord_2838488 prefixEnd_2838488 485836225339798545448679 := by
  unfold tailWord_2838488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51764081270325113000294059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69018775027100150667058745 51764081270325113000294059)
  ·
    refine ⟨77646121905487669500441089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51764081270325113000294059 77646121905487669500441089)
    ·
      refine ⟨58234591429115752125330817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77646121905487669500441089 58234591429115752125330817)
      ·
        refine ⟨43675943571836814093998113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58234591429115752125330817 43675943571836814093998113)
        ·
          refine ⟨32756957678877610570498585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43675943571836814093998113 32756957678877610570498585)
          ·
            refine ⟨24567718259158207927873939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32756957678877610570498585 24567718259158207927873939)
            ·
              refine ⟨36851577388737311891810909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24567718259158207927873939 36851577388737311891810909)
              ·
                refine ⟨13819341520776491959429091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36851577388737311891810909 13819341520776491959429091)
                ·
                  refine ⟨20729012281164737939143637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13819341520776491959429091 20729012281164737939143637)
                  ·
                    refine ⟨485836225339798545448679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20729012281164737939143637 485836225339798545448679)
                    ·
                      rfl

theorem cell23_2838488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_2838488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838488 prefixEnd_2838488 := by exact prefixLift 2838488
  have htrace : WordTrace (prefixWord ++ tailWord_2838488) baseStart_2838488 baseEnd_2838488 := by
    simpa [prefixWord, tailWord_2838488, baseEnd_2838488] using wordTrace_append hprefix tailTrace_2838488
  have hstable : (prefixWord ++ tailWord_2838488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838488).length < 2 ^ (prefixWord ++ tailWord_2838488).sum := by decide
  have hdescent : baseEnd_2838488 < baseStart_2838488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838509 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 7]
def baseStart_2838509 : Nat := 118140960795 + 2838509 * 2 ^ 59
def prefixEnd_2838509 : Nat := 4983230072969 + 3 ^ 40 * 2838509 * 2
def baseEnd_2838509 : Nat := 161946606568126672687049

theorem tailTrace_2838509 : CollatzResearch.WordTrace tailWord_2838509 prefixEnd_2838509 161946606568126672687049 := by
  unfold tailWord_2838509
  simp only [CollatzResearch.WordTrace]
  refine ⟨103528928473574146587102581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69019285649049431058068387 103528928473574146587102581)
  ·
    refine ⟨9705837044397576242540867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103528928473574146587102581 9705837044397576242540867)
    ·
      refine ⟨14558755566596364363811301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9705837044397576242540867 14558755566596364363811301)
      ·
        refine ⟨2729766668736818318214619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14558755566596364363811301 2729766668736818318214619)
        ·
          refine ⟨4094650003105227477321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729766668736818318214619 4094650003105227477321929)
          ·
            refine ⟨3070987502328920607991447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4094650003105227477321929 3070987502328920607991447)
            ·
              refine ⟨4606481253493380911987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070987502328920607991447 4606481253493380911987171)
              ·
                refine ⟨6909721880240071367980757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606481253493380911987171 6909721880240071367980757)
                ·
                  refine ⟨161946606568126672687049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6909721880240071367980757 161946606568126672687049)
                  ·
                    rfl

theorem cell23_2838509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_2838509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838509 prefixEnd_2838509 := by exact prefixLift 2838509
  have htrace : WordTrace (prefixWord ++ tailWord_2838509) baseStart_2838509 baseEnd_2838509 := by
    simpa [prefixWord, tailWord_2838509, baseEnd_2838509] using wordTrace_append hprefix tailTrace_2838509
  have hstable : (prefixWord ++ tailWord_2838509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838509).length < 2 ^ (prefixWord ++ tailWord_2838509).sum := by decide
  have hdescent : baseEnd_2838509 < baseStart_2838509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838542 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2838542 : Nat := 118140960795 + 2838542 * 2 ^ 59
def prefixEnd_2838542 : Nat := 4983230072969 + 3 ^ 40 * 2838542 * 2
def baseEnd_2838542 : Nat := 1457536403974738425070789

theorem tailTrace_2838542 : CollatzResearch.WordTrace tailWord_2838542 prefixEnd_2838542 1457536403974738425070789 := by
  unfold tailWord_2838542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941266510306824152881735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69020088054969728815369253 12941266510306824152881735)
  ·
    refine ⟨19411899765460236229322603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12941266510306824152881735 19411899765460236229322603)
    ·
      refine ⟨29117849648190354343983905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19411899765460236229322603 29117849648190354343983905)
      ·
        refine ⟨21838387236142765757987929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29117849648190354343983905 21838387236142765757987929)
        ·
          refine ⟨16378790427107074318490947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21838387236142765757987929 16378790427107074318490947)
          ·
            refine ⟨24568185640660611477736421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16378790427107074318490947 24568185640660611477736421)
            ·
              refine ⟨4606534807623864652075579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24568185640660611477736421 4606534807623864652075579)
              ·
                refine ⟨6909802211435796978113369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606534807623864652075579 6909802211435796978113369)
                ·
                  refine ⟨5182351658576847733585027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909802211435796978113369 5182351658576847733585027)
                  ·
                    refine ⟨7773527487865271600377541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182351658576847733585027 7773527487865271600377541)
                    ·
                      refine ⟨1457536403974738425070789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7773527487865271600377541 1457536403974738425070789)
                      ·
                        rfl

theorem cell23_2838542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2838542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838542 prefixEnd_2838542 := by exact prefixLift 2838542
  have htrace : WordTrace (prefixWord ++ tailWord_2838542) baseStart_2838542 baseEnd_2838542 := by
    simpa [prefixWord, tailWord_2838542, baseEnd_2838542] using wordTrace_append hprefix tailTrace_2838542
  have hstable : (prefixWord ++ tailWord_2838542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838542).length < 2 ^ (prefixWord ++ tailWord_2838542).sum := by decide
  have hdescent : baseEnd_2838542 < baseStart_2838542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838562 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2838562 : Nat := 118140960795 + 2838562 * 2 ^ 59
def prefixEnd_2838562 : Nat := 4983230072969 + 3 ^ 40 * 2838562 * 2
def baseEnd_2838562 : Nat := 1457546673587828346820697

theorem tailTrace_2838562 : CollatzResearch.WordTrace tailWord_2838562 prefixEnd_2838562 1457546673587828346820697 := by
  unfold tailWord_2838562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25882715385595534159695485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69020574361588091092521293 25882715385595534159695485)
  ·
    refine ⟨9706018269598325309885807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25882715385595534159695485 9706018269598325309885807)
    ·
      refine ⟨14559027404397487964828711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706018269598325309885807 14559027404397487964828711)
      ·
        refine ⟨21838541106596231947243067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14559027404397487964828711 21838541106596231947243067)
        ·
          refine ⟨32757811659894347920864601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21838541106596231947243067 32757811659894347920864601)
          ·
            refine ⟨24568358744920760940648451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32757811659894347920864601 24568358744920760940648451)
            ·
              refine ⟨36852538117381141410972677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24568358744920760940648451 36852538117381141410972677)
              ·
                refine ⟨6909850897008964014557377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36852538117381141410972677 6909850897008964014557377)
                ·
                  refine ⟨5182388172756723010918033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909850897008964014557377 5182388172756723010918033)
                  ·
                    refine ⟨3886791129567542258188525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5182388172756723010918033 3886791129567542258188525)
                    ·
                      refine ⟨1457546673587828346820697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886791129567542258188525 1457546673587828346820697)
                      ·
                        rfl

theorem cell23_2838562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2838562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838562 prefixEnd_2838562 := by exact prefixLift 2838562
  have htrace : WordTrace (prefixWord ++ tailWord_2838562) baseStart_2838562 baseEnd_2838562 := by
    simpa [prefixWord, tailWord_2838562, baseEnd_2838562] using wordTrace_append hprefix tailTrace_2838562
  have hstable : (prefixWord ++ tailWord_2838562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838562).length < 2 ^ (prefixWord ++ tailWord_2838562).sum := by decide
  have hdescent : baseEnd_2838562 < baseStart_2838562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838565 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 6]
def baseStart_2838565 : Nat := 118140960795 + 2838565 * 2 ^ 59
def prefixEnd_2838565 : Nat := 4983230072969 + 3 ^ 40 * 2838565 * 2
def baseEnd_2838565 : Nat := 161949801558865759453687

theorem tailTrace_2838565 : CollatzResearch.WordTrace tailWord_2838565 prefixEnd_2838565 161949801558865759453687 := by
  unfold tailWord_2838565
  simp only [CollatzResearch.WordTrace]
  refine ⟨103530970961371268151141149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69020647307580845434094099 103530970961371268151141149)
  ·
    refine ⟨38824114110514225556677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103530970961371268151141149 38824114110514225556677931)
    ·
      refine ⟨58236171165771338335016897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38824114110514225556677931 58236171165771338335016897)
      ·
        refine ⟨43677128374328503751262673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58236171165771338335016897 43677128374328503751262673)
        ·
          refine ⟨32757846280746377813447005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43677128374328503751262673 32757846280746377813447005)
          ·
            refine ⟨12284192355279891680042627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32757846280746377813447005 12284192355279891680042627)
            ·
              refine ⟨18426288532919837520063941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12284192355279891680042627 18426288532919837520063941)
              ·
                refine ⟨3454929099922469535011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18426288532919837520063941 3454929099922469535011989)
                ·
                  refine ⟨161949801558865759453687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3454929099922469535011989 161949801558865759453687)
                  ·
                    rfl

theorem cell23_2838565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_2838565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838565 prefixEnd_2838565 := by exact prefixLift 2838565
  have htrace : WordTrace (prefixWord ++ tailWord_2838565) baseStart_2838565 baseEnd_2838565 := by
    simpa [prefixWord, tailWord_2838565, baseEnd_2838565] using wordTrace_append hprefix tailTrace_2838565
  have hstable : (prefixWord ++ tailWord_2838565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838565).length < 2 ^ (prefixWord ++ tailWord_2838565).sum := by decide
  have hdescent : baseEnd_2838565 < baseStart_2838565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838582 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2838582 : Nat := 118140960795 + 2838582 * 2 ^ 59
def prefixEnd_2838582 : Nat := 4983230072969 + 3 ^ 40 * 2838582 * 2
def baseEnd_2838582 : Nat := 161950771466768696507845

theorem tailTrace_2838582 : CollatzResearch.WordTrace tailWord_2838582 prefixEnd_2838582 161950771466768696507845 := by
  unfold tailWord_2838582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470724437644355003406875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69021060668206453369673333 6470724437644355003406875)
  ·
    refine ⟨9706086656466532505110313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6470724437644355003406875 9706086656466532505110313)
    ·
      refine ⟨7279564992349899378832735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9706086656466532505110313 7279564992349899378832735)
      ·
        refine ⟨10919347488524849068249103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279564992349899378832735 10919347488524849068249103)
        ·
          refine ⟨16379021232787273602373655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10919347488524849068249103 16379021232787273602373655)
          ·
            refine ⟨24568531849180910403560483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16379021232787273602373655 24568531849180910403560483)
            ·
              refine ⟨36852797773771365605340725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24568531849180910403560483 36852797773771365605340725)
              ·
                refine ⟨3454949791291065525500693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36852797773771365605340725 3454949791291065525500693)
                ·
                  refine ⟨161950771466768696507845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3454949791291065525500693 161950771466768696507845)
                  ·
                    rfl

theorem cell23_2838582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2838582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838582 prefixEnd_2838582 := by exact prefixLift 2838582
  have htrace : WordTrace (prefixWord ++ tailWord_2838582) baseStart_2838582 baseEnd_2838582 := by
    simpa [prefixWord, tailWord_2838582, baseEnd_2838582] using wordTrace_append hprefix tailTrace_2838582
  have hstable : (prefixWord ++ tailWord_2838582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838582).length < 2 ^ (prefixWord ++ tailWord_2838582).sum := by decide
  have hdescent : baseEnd_2838582 < baseStart_2838582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838592 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_2838592 : Nat := 118140960795 + 2838592 * 2 ^ 59
def prefixEnd_2838592 : Nat := 4983230072969 + 3 ^ 40 * 2838592 * 2
def baseEnd_2838592 : Nat := 1457562078007463229445559

theorem tailTrace_2838592 : CollatzResearch.WordTrace tailWord_2838592 prefixEnd_2838592 1457562078007463229445559 := by
  unfold tailWord_2838592
  simp only [CollatzResearch.WordTrace]
  refine ⟨51765977866136725881187015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69021303821515634508249353 51765977866136725881187015)
  ·
    refine ⟨77648966799205088821780523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51765977866136725881187015 77648966799205088821780523)
    ·
      refine ⟨116473450198807633232670785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77648966799205088821780523 116473450198807633232670785)
      ·
        refine ⟨87355087649105724924503089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116473450198807633232670785 87355087649105724924503089)
        ·
          refine ⟨65516315736829293693377317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87355087649105724924503089 65516315736829293693377317)
          ·
            refine ⟨12284309200655492567508247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65516315736829293693377317 12284309200655492567508247)
            ·
              refine ⟨18426463800983238851262371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12284309200655492567508247 18426463800983238851262371)
              ·
                refine ⟨27639695701474858276893557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18426463800983238851262371 27639695701474858276893557)
                ·
                  refine ⟨2591221472013267963458771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27639695701474858276893557 2591221472013267963458771)
                  ·
                    refine ⟨3886832208019901945188157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591221472013267963458771 3886832208019901945188157)
                    ·
                      refine ⟨1457562078007463229445559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3886832208019901945188157 1457562078007463229445559)
                      ·
                        rfl

theorem cell23_2838592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_2838592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838592 prefixEnd_2838592 := by exact prefixLift 2838592
  have htrace : WordTrace (prefixWord ++ tailWord_2838592) baseStart_2838592 baseEnd_2838592 := by
    simpa [prefixWord, tailWord_2838592, baseEnd_2838592] using wordTrace_append hprefix tailTrace_2838592
  have hstable : (prefixWord ++ tailWord_2838592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838592).length < 2 ^ (prefixWord ++ tailWord_2838592).sum := by decide
  have hdescent : baseEnd_2838592 < baseStart_2838592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838642 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_2838642 : Nat := 118140960795 + 2838642 * 2 ^ 59
def prefixEnd_2838642 : Nat := 4983230072969 + 3 ^ 40 * 2838642 * 2
def baseEnd_2838642 : Nat := 485862584013396011273443

theorem tailTrace_2838642 : CollatzResearch.WordTrace tailWord_2838642 prefixEnd_2838642 485862584013396011273443 := by
  unfold tailWord_2838642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25883444845523077575423545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69022519588061540201129453 25883444845523077575423545)
  ·
    refine ⟨19412583634142308181567659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25883444845523077575423545 19412583634142308181567659)
    ·
      refine ⟨29118875451213462272351489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19412583634142308181567659 29118875451213462272351489)
      ·
        refine ⟨21839156588410096704263617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29118875451213462272351489 21839156588410096704263617)
        ·
          refine ⟨16379367441307572528197713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21839156588410096704263617 16379367441307572528197713)
          ·
            refine ⟨12284525580980679396148285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16379367441307572528197713 12284525580980679396148285)
            ·
              refine ⟨4606697092867754773555607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12284525580980679396148285 4606697092867754773555607)
              ·
                refine ⟨6910045639301632160333411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606697092867754773555607 6910045639301632160333411)
                ·
                  refine ⟨10365068458952448240500117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910045639301632160333411 10365068458952448240500117)
                  ·
                    refine ⟨485862584013396011273443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10365068458952448240500117 485862584013396011273443)
                    ·
                      rfl

theorem cell23_2838642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_2838642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838642 prefixEnd_2838642 := by exact prefixLift 2838642
  have htrace : WordTrace (prefixWord ++ tailWord_2838642) baseStart_2838642 baseEnd_2838642 := by
    simpa [prefixWord, tailWord_2838642, baseEnd_2838642] using wordTrace_append hprefix tailTrace_2838642
  have hstable : (prefixWord ++ tailWord_2838642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838642).length < 2 ^ (prefixWord ++ tailWord_2838642).sum := by decide
  have hdescent : baseEnd_2838642 < baseStart_2838642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838649 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2838649 : Nat := 118140960795 + 2838649 * 2 ^ 59
def prefixEnd_2838649 : Nat := 4983230072969 + 3 ^ 40 * 2838649 * 2
def baseEnd_2838649 : Nat := 1457591346404769506432797

theorem tailTrace_2838649 : CollatzResearch.WordTrace tailWord_2838649 prefixEnd_2838649 1457591346404769506432797 := by
  unfold tailWord_2838649
  simp only [CollatzResearch.WordTrace]
  refine ⟨103534034693066950497199001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69022689795377966998132667 103534034693066950497199001)
  ·
    refine ⟨77650526019800212872899251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103534034693066950497199001 77650526019800212872899251)
    ·
      refine ⟨116475789029700319309348877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77650526019800212872899251 116475789029700319309348877)
      ·
        refine ⟨43678420886137619741005829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116475789029700319309348877 43678420886137619741005829)
        ·
          refine ⟨8189703916150803701438593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43678420886137619741005829 8189703916150803701438593)
          ·
            refine ⟨6142277937113102776078945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8189703916150803701438593 6142277937113102776078945)
            ·
              refine ⟨4606708452834827082059209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6142277937113102776078945 4606708452834827082059209)
              ·
                refine ⟨3455031339626120311544407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4606708452834827082059209 3455031339626120311544407)
                ·
                  refine ⟨5182547009439180467316611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455031339626120311544407 5182547009439180467316611)
                  ·
                    refine ⟨7773820514158770700974917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182547009439180467316611 7773820514158770700974917)
                    ·
                      refine ⟨1457591346404769506432797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7773820514158770700974917 1457591346404769506432797)
                      ·
                        rfl

theorem cell23_2838649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2838649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838649 prefixEnd_2838649 := by exact prefixLift 2838649
  have htrace : WordTrace (prefixWord ++ tailWord_2838649) baseStart_2838649 baseEnd_2838649 := by
    simpa [prefixWord, tailWord_2838649, baseEnd_2838649] using wordTrace_append hprefix tailTrace_2838649
  have hstable : (prefixWord ++ tailWord_2838649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838649).length < 2 ^ (prefixWord ++ tailWord_2838649).sum := by decide
  have hdescent : baseEnd_2838649 < baseStart_2838649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838749 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2838749 : Nat := 118140960795 + 2838749 * 2 ^ 59
def prefixEnd_2838749 : Nat := 4983230072969 + 3 ^ 40 * 2838749 * 2
def baseEnd_2838749 : Nat := 485880898156739705060779

theorem tailTrace_2838749 : CollatzResearch.WordTrace tailWord_2838749 prefixEnd_2838749 485880898156739705060779 := by
  unfold tailWord_2838749
  simp only [CollatzResearch.WordTrace]
  refine ⟨103537681992704667575839301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69025121328469778383892867 103537681992704667575839301)
  ·
    refine ⟨19413315373632125170469869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103537681992704667575839301 19413315373632125170469869)
    ·
      refine ⟨7279993265112046938926201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19413315373632125170469869 7279993265112046938926201)
      ·
        refine ⟨5459994948834035204194651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7279993265112046938926201 5459994948834035204194651)
        ·
          refine ⟨8189992423251052806291977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459994948834035204194651 8189992423251052806291977)
          ·
            refine ⟨6142494317438289604718983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8189992423251052806291977 6142494317438289604718983)
            ·
              refine ⟨9213741476157434407078475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142494317438289604718983 9213741476157434407078475)
              ·
                refine ⟨13820612214236151610617713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213741476157434407078475 13820612214236151610617713)
                ·
                  refine ⟨10365459160677113707963285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13820612214236151610617713 10365459160677113707963285)
                  ·
                    refine ⟨485880898156739705060779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10365459160677113707963285 485880898156739705060779)
                    ·
                      rfl

theorem cell23_2838749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2838749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838749 prefixEnd_2838749 := by exact prefixLift 2838749
  have htrace : WordTrace (prefixWord ++ tailWord_2838749) baseStart_2838749 baseEnd_2838749 := by
    simpa [prefixWord, tailWord_2838749, baseEnd_2838749] using wordTrace_append hprefix tailTrace_2838749
  have hstable : (prefixWord ++ tailWord_2838749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838749).length < 2 ^ (prefixWord ++ tailWord_2838749).sum := by decide
  have hdescent : baseEnd_2838749 < baseStart_2838749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838752 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2838752 : Nat := 118140960795 + 2838752 * 2 ^ 59
def prefixEnd_2838752 : Nat := 4983230072969 + 3 ^ 40 * 2838752 * 2
def baseEnd_2838752 : Nat := 1457644234912182603444823

theorem tailTrace_2838752 : CollatzResearch.WordTrace tailWord_2838752 prefixEnd_2838752 1457644234912182603444823 := by
  unfold tailWord_2838752
  simp only [CollatzResearch.WordTrace]
  refine ⟨51768895705846899544099255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69025194274462532725465673 51768895705846899544099255)
  ·
    refine ⟨77653343558770349316148883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51768895705846899544099255 77653343558770349316148883)
    ·
      refine ⟨116480015338155523974223325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77653343558770349316148883 116480015338155523974223325)
      ·
        refine ⟨43680005751808321490333747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116480015338155523974223325 43680005751808321490333747)
        ·
          refine ⟨65520008627712482235500621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43680005751808321490333747 65520008627712482235500621)
          ·
            refine ⟨24570003235392180838312733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65520008627712482235500621 24570003235392180838312733)
            ·
              refine ⟨9213751213272067814367275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24570003235392180838312733 9213751213272067814367275)
              ·
                refine ⟨13820626819908101721550913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213751213272067814367275 13820626819908101721550913)
                ·
                  refine ⟨10365470114931076291163185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13820626819908101721550913 10365470114931076291163185)
                  ·
                    refine ⟨7774102586198307218372389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10365470114931076291163185 7774102586198307218372389)
                    ·
                      refine ⟨1457644234912182603444823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774102586198307218372389 1457644234912182603444823)
                      ·
                        rfl

theorem cell23_2838752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2838752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838752 prefixEnd_2838752 := by exact prefixLift 2838752
  have htrace : WordTrace (prefixWord ++ tailWord_2838752) baseStart_2838752 baseEnd_2838752 := by
    simpa [prefixWord, tailWord_2838752, baseEnd_2838752] using wordTrace_append hprefix tailTrace_2838752
  have hstable : (prefixWord ++ tailWord_2838752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838752).length < 2 ^ (prefixWord ++ tailWord_2838752).sum := by decide
  have hdescent : baseEnd_2838752 < baseStart_2838752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838762 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_2838762 : Nat := 118140960795 + 2838762 * 2 ^ 59
def prefixEnd_2838762 : Nat := 4983230072969 + 3 ^ 40 * 2838762 * 2
def baseEnd_2838762 : Nat := 161961041079858618257753

theorem tailTrace_2838762 : CollatzResearch.WordTrace tailWord_2838762 prefixEnd_2838762 161961041079858618257753 := by
  unfold tailWord_2838762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884539035414392699015635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69025437427771713864041693 25884539035414392699015635)
  ·
    refine ⟨38826808553121589048523453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25884539035414392699015635 38826808553121589048523453)
    ·
      refine ⟨14560053207420595893196295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38826808553121589048523453 14560053207420595893196295)
      ·
        refine ⟨21840079811130893839794443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14560053207420595893196295 21840079811130893839794443)
        ·
          refine ⟨32760119716696340759691665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21840079811130893839794443 32760119716696340759691665)
          ·
            refine ⟨24570089787522255569768749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32760119716696340759691665 24570089787522255569768749)
            ·
              refine ⟨9213783670320845838663281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24570089787522255569768749 9213783670320845838663281)
              ·
                refine ⟨6910337752740634378997461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9213783670320845838663281 6910337752740634378997461)
                ·
                  refine ⟨161961041079858618257753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6910337752740634378997461 161961041079858618257753)
                  ·
                    rfl

theorem cell23_2838762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_2838762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838762 prefixEnd_2838762 := by exact prefixLift 2838762
  have htrace : WordTrace (prefixWord ++ tailWord_2838762) baseStart_2838762 baseEnd_2838762 := by
    simpa [prefixWord, tailWord_2838762, baseEnd_2838762] using wordTrace_append hprefix tailTrace_2838762
  have hstable : (prefixWord ++ tailWord_2838762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838762).length < 2 ^ (prefixWord ++ tailWord_2838762).sum := by decide
  have hdescent : baseEnd_2838762 < baseStart_2838762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838830 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_2838830 : Nat := 118140960795 + 2838830 * 2 ^ 59
def prefixEnd_2838830 : Nat := 4983230072969 + 3 ^ 40 * 2838830 * 2
def baseEnd_2838830 : Nat := 161964920711470366474385

theorem tailTrace_2838830 : CollatzResearch.WordTrace tailWord_2838830 prefixEnd_2838830 161964920711470366474385 := by
  unfold tailWord_2838830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12942579538176402301192243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69027090870274145606358629 12942579538176402301192243)
  ·
    refine ⟨19413869307264603451788365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12942579538176402301192243 19413869307264603451788365)
    ·
      refine ⟨7280200990224226294420637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19413869307264603451788365 7280200990224226294420637)
      ·
        refine ⟨2730075371334084860407739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7280200990224226294420637 2730075371334084860407739)
        ·
          refine ⟨4095113057001127290611609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730075371334084860407739 4095113057001127290611609)
          ·
            refine ⟨3071334792750845467958707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4095113057001127290611609 3071334792750845467958707)
            ·
              refine ⟨4607002189126268201938061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071334792750845467958707 4607002189126268201938061)
              ·
                refine ⟨1727625820922350575726773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4607002189126268201938061 1727625820922350575726773)
                ·
                  refine ⟨161964920711470366474385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727625820922350575726773 161964920711470366474385)
                  ·
                    rfl

theorem cell23_2838830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_2838830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838830 prefixEnd_2838830 := by exact prefixLift 2838830
  have htrace : WordTrace (prefixWord ++ tailWord_2838830) baseStart_2838830 baseEnd_2838830 := by
    simpa [prefixWord, tailWord_2838830, baseEnd_2838830] using wordTrace_append hprefix tailTrace_2838830
  have hstable : (prefixWord ++ tailWord_2838830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838830).length < 2 ^ (prefixWord ++ tailWord_2838830).sum := by decide
  have hdescent : baseEnd_2838830 < baseStart_2838830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838846 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2838846 : Nat := 118140960795 + 2838846 * 2 ^ 59
def prefixEnd_2838846 : Nat := 4983230072969 + 3 ^ 40 * 2838846 * 2
def baseEnd_2838846 : Nat := 1457692502093705235669391

theorem tailTrace_2838846 : CollatzResearch.WordTrace tailWord_2838846 prefixEnd_2838846 1457692502093705235669391 := by
  unfold tailWord_2838846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12942652484169156642765049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69027479915568835428080261 12942652484169156642765049)
  ·
    refine ⟨9706989363126867482073787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12942652484169156642765049 9706989363126867482073787)
    ·
      refine ⟨14560484044690301223110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706989363126867482073787 14560484044690301223110681)
      ·
        refine ⟨10920363033517725917333011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14560484044690301223110681 10920363033517725917333011)
        ·
          refine ⟨16380544550276588875999517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920363033517725917333011 16380544550276588875999517)
          ·
            refine ⟨6142704206353720828499819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16380544550276588875999517 6142704206353720828499819)
            ·
              refine ⟨9214056309530581242749729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142704206353720828499819 9214056309530581242749729)
              ·
                refine ⟨6910542232147935932062297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9214056309530581242749729 6910542232147935932062297)
                ·
                  refine ⟨5182906674110951949046723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910542232147935932062297 5182906674110951949046723)
                  ·
                    refine ⟨7774360011166427923570085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182906674110951949046723 7774360011166427923570085)
                    ·
                      refine ⟨1457692502093705235669391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774360011166427923570085 1457692502093705235669391)
                      ·
                        rfl

theorem cell23_2838846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2838846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838846 prefixEnd_2838846 := by exact prefixLift 2838846
  have htrace : WordTrace (prefixWord ++ tailWord_2838846) baseStart_2838846 baseEnd_2838846 := by
    simpa [prefixWord, tailWord_2838846, baseEnd_2838846] using wordTrace_append hprefix tailTrace_2838846
  have hstable : (prefixWord ++ tailWord_2838846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838846).length < 2 ^ (prefixWord ++ tailWord_2838846).sum := by decide
  have hdescent : baseEnd_2838846 < baseStart_2838846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838856 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 1, 4]
def baseStart_2838856 : Nat := 118140960795 + 2838856 * 2 ^ 59
def prefixEnd_2838856 : Nat := 4983230072969 + 3 ^ 40 * 2838856 * 2
def baseEnd_2838856 : Nat := 485899212300083398848115

theorem tailTrace_2838856 : CollatzResearch.WordTrace tailWord_2838856 prefixEnd_2838856 485899212300083398848115 := by
  unfold tailWord_2838856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51770792301658512424992211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69027723068878016566656281 51770792301658512424992211)
  ·
    refine ⟨77656188452487768637488317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51770792301658512424992211 77656188452487768637488317)
    ·
      refine ⟨29121070669682913239058119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77656188452487768637488317 29121070669682913239058119)
      ·
        refine ⟨43681606004524369858587179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29121070669682913239058119 43681606004524369858587179)
        ·
          refine ⟨65522409006786554787880769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43681606004524369858587179 65522409006786554787880769)
          ·
            refine ⟨49141806755089916090910577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65522409006786554787880769 49141806755089916090910577)
            ·
              refine ⟨36856355066317437068182933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49141806755089916090910577 36856355066317437068182933)
              ·
                refine ⟨1727641643733629862571075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36856355066317437068182933 1727641643733629862571075)
                ·
                  refine ⟨2591462465600444793856613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727641643733629862571075 2591462465600444793856613)
                  ·
                    refine ⟨485899212300083398848115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591462465600444793856613 485899212300083398848115)
                    ·
                      rfl

theorem cell23_2838856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_2838856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838856 prefixEnd_2838856 := by exact prefixLift 2838856
  have htrace : WordTrace (prefixWord ++ tailWord_2838856) baseStart_2838856 baseEnd_2838856 := by
    simpa [prefixWord, tailWord_2838856, baseEnd_2838856] using wordTrace_append hprefix tailTrace_2838856
  have hstable : (prefixWord ++ tailWord_2838856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838856).length < 2 ^ (prefixWord ++ tailWord_2838856).sum := by decide
  have hdescent : baseEnd_2838856 < baseStart_2838856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838919 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2838919 : Nat := 118140960795 + 2838919 * 2 ^ 59
def prefixEnd_2838919 : Nat := 4983230072969 + 3 ^ 40 * 2838919 * 2
def baseEnd_2838919 : Nat := 1457729986181483450056555

theorem tailTrace_2838919 : CollatzResearch.WordTrace tailWord_2838919 prefixEnd_2838919 1457729986181483450056555 := by
  unfold tailWord_2838919
  simp only [CollatzResearch.WordTrace]
  refine ⟨103543882402088786609527811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69029254934725857739685207 103543882402088786609527811)
  ·
    refine ⟨155315823603133179914291717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103543882402088786609527811 155315823603133179914291717)
    ·
      refine ⟨29121716925587471233929697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155315823603133179914291717 29121716925587471233929697)
      ·
        refine ⟨21841287694190603425447273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29121716925587471233929697 21841287694190603425447273)
        ·
          refine ⟨16380965770642952569085455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21841287694190603425447273 16380965770642952569085455)
          ·
            refine ⟨24571448655964428853628183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16380965770642952569085455 24571448655964428853628183)
            ·
              refine ⟨36857172983946643280442275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571448655964428853628183 36857172983946643280442275)
              ·
                refine ⟨55285759475919964920663413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36857172983946643280442275 55285759475919964920663413)
                ·
                  refine ⟨5183039950867496711312195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55285759475919964920663413 5183039950867496711312195)
                  ·
                    refine ⟨7774559926301245066968293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183039950867496711312195 7774559926301245066968293)
                    ·
                      refine ⟨1457729986181483450056555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774559926301245066968293 1457729986181483450056555)
                      ·
                        rfl

theorem cell23_2838919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2838919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838919 prefixEnd_2838919 := by exact prefixLift 2838919
  have htrace : WordTrace (prefixWord ++ tailWord_2838919) baseStart_2838919 baseEnd_2838919 := by
    simpa [prefixWord, tailWord_2838919, baseEnd_2838919] using wordTrace_append hprefix tailTrace_2838919
  have hstable : (prefixWord ++ tailWord_2838919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838919).length < 2 ^ (prefixWord ++ tailWord_2838919).sum := by decide
  have hdescent : baseEnd_2838919 < baseStart_2838919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838934 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2838934 : Nat := 118140960795 + 2838934 * 2 ^ 59
def prefixEnd_2838934 : Nat := 4983230072969 + 3 ^ 40 * 2838934 * 2
def baseEnd_2838934 : Nat := 1457737688391300891368987

theorem tailTrace_2838934 : CollatzResearch.WordTrace tailWord_2838934 prefixEnd_2838934 1457737688391300891368987 := by
  unfold tailWord_2838934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471526843564652760707741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69029619664689629447549237 6471526843564652760707741)
  ·
    refine ⟨2426822566336744785265403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6471526843564652760707741 2426822566336744785265403)
    ·
      refine ⟨3640233849505117177898105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426822566336744785265403 3640233849505117177898105)
      ·
        refine ⟨2730175387128837883423579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3640233849505117177898105 2730175387128837883423579)
        ·
          refine ⟨4095263080693256825135369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730175387128837883423579 4095263080693256825135369)
          ·
            refine ⟨3071447310519942618851527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4095263080693256825135369 3071447310519942618851527)
            ·
              refine ⟨4607170965779913928277291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071447310519942618851527 4607170965779913928277291)
              ·
                refine ⟨6910756448669870892415937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607170965779913928277291 6910756448669870892415937)
                ·
                  refine ⟨5183067336502403169311953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910756448669870892415937 5183067336502403169311953)
                  ·
                    refine ⟨3887300502376802376983965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5183067336502403169311953 3887300502376802376983965)
                    ·
                      refine ⟨1457737688391300891368987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3887300502376802376983965 1457737688391300891368987)
                      ·
                        rfl

theorem cell23_2838934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2838934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838934 prefixEnd_2838934 := by exact prefixLift 2838934
  have htrace : WordTrace (prefixWord ++ tailWord_2838934) baseStart_2838934 baseEnd_2838934 := by
    simpa [prefixWord, tailWord_2838934, baseEnd_2838934] using wordTrace_append hprefix tailTrace_2838934
  have hstable : (prefixWord ++ tailWord_2838934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838934).length < 2 ^ (prefixWord ++ tailWord_2838934).sum := by decide
  have hdescent : baseEnd_2838934 < baseStart_2838934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838936 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2838936 : Nat := 118140960795 + 2838936 * 2 ^ 59
def prefixEnd_2838936 : Nat := 4983230072969 + 3 ^ 40 * 2838936 * 2
def baseEnd_2838936 : Nat := 1457738715352609883543977

theorem tailTrace_2838936 : CollatzResearch.WordTrace tailWord_2838936 prefixEnd_2838936 1457738715352609883543977 := by
  unfold tailWord_2838936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51772251221513599256448331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69029668295351465675264441 51772251221513599256448331)
  ·
    refine ⟨77658376832270398884672497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51772251221513599256448331 77658376832270398884672497)
    ·
      refine ⟨58243782624202799163504373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77658376832270398884672497 58243782624202799163504373)
      ·
        refine ⟨5460354621019012421578535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58243782624202799163504373 5460354621019012421578535)
        ·
          refine ⟨8190531931528518632367803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460354621019012421578535 8190531931528518632367803)
          ·
            refine ⟨12285797897292777948551705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190531931528518632367803 12285797897292777948551705)
            ·
              refine ⟨9214348422969583461413779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12285797897292777948551705 9214348422969583461413779)
              ·
                refine ⟨13821522634454375192120669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214348422969583461413779 13821522634454375192120669)
                ·
                  refine ⟨5183070987920390697045251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13821522634454375192120669 5183070987920390697045251)
                  ·
                    refine ⟨7774606481880586045567877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183070987920390697045251 7774606481880586045567877)
                    ·
                      refine ⟨1457738715352609883543977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774606481880586045567877 1457738715352609883543977)
                      ·
                        rfl

theorem cell23_2838936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2838936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838936 prefixEnd_2838936 := by exact prefixLift 2838936
  have htrace : WordTrace (prefixWord ++ tailWord_2838936) baseStart_2838936 baseEnd_2838936 := by
    simpa [prefixWord, tailWord_2838936, baseEnd_2838936] using wordTrace_append hprefix tailTrace_2838936
  have hstable : (prefixWord ++ tailWord_2838936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838936).length < 2 ^ (prefixWord ++ tailWord_2838936).sum := by decide
  have hdescent : baseEnd_2838936 < baseStart_2838936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838946 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2838946 : Nat := 118140960795 + 2838946 * 2 ^ 59
def prefixEnd_2838946 : Nat := 4983230072969 + 3 ^ 40 * 2838946 * 2
def baseEnd_2838946 : Nat := 485914616719718281472977

theorem tailTrace_2838946 : CollatzResearch.WordTrace tailWord_2838946 prefixEnd_2838946 485914616719718281472977 := by
  unfold tailWord_2838946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25886216793247742555190173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69029911448660646813840461 25886216793247742555190173)
  ·
    refine ⟨9707331297467903458196315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25886216793247742555190173 9707331297467903458196315)
    ·
      refine ⟨14560996946201855187294473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707331297467903458196315 14560996946201855187294473)
      ·
        refine ⟨10920747709651391390470855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14560996946201855187294473 10920747709651391390470855)
        ·
          refine ⟨16381121564477087085706283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920747709651391390470855 16381121564477087085706283)
          ·
            refine ⟨24571682346715630628559425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381121564477087085706283 24571682346715630628559425)
            ·
              refine ⟨18428761760036722971419569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24571682346715630628559425 18428761760036722971419569)
              ·
                refine ⟨13821571320027542228564677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18428761760036722971419569 13821571320027542228564677)
                ·
                  refine ⟨2591544622505164167855877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13821571320027542228564677 2591544622505164167855877)
                  ·
                    refine ⟨485914616719718281472977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591544622505164167855877 485914616719718281472977)
                    ·
                      rfl

theorem cell23_2838946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2838946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838946 prefixEnd_2838946 := by exact prefixLift 2838946
  have htrace : WordTrace (prefixWord ++ tailWord_2838946) baseStart_2838946 baseEnd_2838946 := by
    simpa [prefixWord, tailWord_2838946, baseEnd_2838946] using wordTrace_append hprefix tailTrace_2838946
  have hstable : (prefixWord ++ tailWord_2838946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838946).length < 2 ^ (prefixWord ++ tailWord_2838946).sum := by decide
  have hdescent : baseEnd_2838946 < baseStart_2838946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838949 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2838949 : Nat := 118140960795 + 2838949 * 2 ^ 59
def prefixEnd_2838949 : Nat := 4983230072969 + 3 ^ 40 * 2838949 * 2
def baseEnd_2838949 : Nat := 1457745390601118332681417

theorem tailTrace_2838949 : CollatzResearch.WordTrace tailWord_2838949 prefixEnd_2838949 1457745390601118332681417 := by
  unfold tailWord_2838949
  simp only [CollatzResearch.WordTrace]
  refine ⟨103544976591980101733119901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69029984394653401155413267 103544976591980101733119901)
  ·
    refine ⟨38829366221992538149919963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103544976591980101733119901 38829366221992538149919963)
    ·
      refine ⟨58244049332988807224879945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38829366221992538149919963 58244049332988807224879945)
      ·
        refine ⟨43683036999741605418659959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58244049332988807224879945 43683036999741605418659959)
        ·
          refine ⟨65524555499612408127989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43683036999741605418659959 65524555499612408127989939)
          ·
            refine ⟨98286833249418612191984909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65524555499612408127989939 98286833249418612191984909)
            ·
              refine ⟨36857562468531979571994341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98286833249418612191984909 36857562468531979571994341)
              ·
                refine ⟨6910792962849746169748939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36857562468531979571994341 6910792962849746169748939)
                ·
                  refine ⟨10366189444274619254623409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910792962849746169748939 10366189444274619254623409)
                  ·
                    refine ⟨7774642083205964440967557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10366189444274619254623409 7774642083205964440967557)
                    ·
                      refine ⟨1457745390601118332681417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774642083205964440967557 1457745390601118332681417)
                      ·
                        rfl

theorem cell23_2838949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2838949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838949 prefixEnd_2838949 := by exact prefixLift 2838949
  have htrace : WordTrace (prefixWord ++ tailWord_2838949) baseStart_2838949 baseEnd_2838949 := by
    simpa [prefixWord, tailWord_2838949, baseEnd_2838949] using wordTrace_append hprefix tailTrace_2838949
  have hstable : (prefixWord ++ tailWord_2838949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838949).length < 2 ^ (prefixWord ++ tailWord_2838949).sum := by decide
  have hdescent : baseEnd_2838949 < baseStart_2838949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838980 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2838980 : Nat := 118140960795 + 2838980 * 2 ^ 59
def prefixEnd_2838980 : Nat := 4983230072969 + 3 ^ 40 * 2838980 * 2
def baseEnd_2838980 : Nat := 485920436167135903797925

theorem tailTrace_2838980 : CollatzResearch.WordTrace tailWord_2838980 prefixEnd_2838980 485920436167135903797925 := by
  unfold tailWord_2838980
  simp only [CollatzResearch.WordTrace]
  refine ⟨51773053627433897013749197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69030738169911862684998929 51773053627433897013749197)
  ·
    refine ⟨19414895110287711380155949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51773053627433897013749197 19414895110287711380155949)
    ·
      refine ⟨7280585666357891767558481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19414895110287711380155949 7280585666357891767558481)
      ·
        refine ⟨5460439249768418825668861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7280585666357891767558481 5460439249768418825668861)
        ·
          refine ⟨2047664718663157059625823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5460439249768418825668861 2047664718663157059625823)
          ·
            refine ⟨3071497077994735589438735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047664718663157059625823 3071497077994735589438735)
            ·
              refine ⟨4607245616992103384158103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071497077994735589438735 4607245616992103384158103)
              ·
                refine ⟨6910868425488155076237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607245616992103384158103 6910868425488155076237155)
                ·
                  refine ⟨10366302638232232614355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910868425488155076237155 10366302638232232614355733)
                  ·
                    refine ⟨485920436167135903797925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10366302638232232614355733 485920436167135903797925)
                    ·
                      rfl

theorem cell23_2838980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2838980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2838980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2838980 prefixEnd_2838980 := by exact prefixLift 2838980
  have htrace : WordTrace (prefixWord ++ tailWord_2838980) baseStart_2838980 baseEnd_2838980 := by
    simpa [prefixWord, tailWord_2838980, baseEnd_2838980] using wordTrace_append hprefix tailTrace_2838980
  have hstable : (prefixWord ++ tailWord_2838980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838980).length < 2 ^ (prefixWord ++ tailWord_2838980).sum := by decide
  have hdescent : baseEnd_2838980 < baseStart_2838980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839010 : List Nat := [3, 3, 3, 2, 2, 1, 9]
def baseStart_2839010 : Nat := 118140960795 + 2839010 * 2 ^ 59
def prefixEnd_2839010 : Nat := 4983230072969 + 3 ^ 40 * 2839010 * 2
def baseEnd_2839010 : Nat := 17997243369395587580477

theorem tailTrace_2839010 : CollatzResearch.WordTrace tailWord_2839010 prefixEnd_2839010 17997243369395587580477 := by
  unfold tailWord_2839010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25886800361189777287772621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69031467629839406100726989 25886800361189777287772621)
  ·
    refine ⟨9707550135446166482914733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25886800361189777287772621 9707550135446166482914733)
    ·
      refine ⟨3640331300792312431093025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9707550135446166482914733 3640331300792312431093025)
      ·
        refine ⟨2730248475594234323319769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3640331300792312431093025 2730248475594234323319769)
        ·
          refine ⟨2047686356695675742489827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730248475594234323319769 2047686356695675742489827)
          ·
            refine ⟨3071529535043513613734741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047686356695675742489827 3071529535043513613734741)
            ·
              refine ⟨17997243369395587580477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3071529535043513613734741 17997243369395587580477)
              ·
                rfl

theorem cell23_2839010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 9].length) (baseStart_2839010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839010 prefixEnd_2839010 := by exact prefixLift 2839010
  have htrace : WordTrace (prefixWord ++ tailWord_2839010) baseStart_2839010 baseEnd_2839010 := by
    simpa [prefixWord, tailWord_2839010, baseEnd_2839010] using wordTrace_append hprefix tailTrace_2839010
  have hstable : (prefixWord ++ tailWord_2839010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839010).length < 2 ^ (prefixWord ++ tailWord_2839010).sum := by decide
  have hdescent : baseEnd_2839010 < baseStart_2839010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839039 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_2839039 : Nat := 118140960795 + 2839039 * 2 ^ 59
def prefixEnd_2839039 : Nat := 4983230072969 + 3 ^ 40 * 2839039 * 2
def baseEnd_2839039 : Nat := 1457791603860022980556003

theorem tailTrace_2839039 : CollatzResearch.WordTrace tailWord_2839039 prefixEnd_2839039 1457791603860022980556003 := by
  unfold tailWord_2839039
  simp only [CollatzResearch.WordTrace]
  refine ⟨103548259161654047103896171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69032172774436031402597447 103548259161654047103896171)
  ·
    refine ⟨155322388742481070655844257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103548259161654047103896171 155322388742481070655844257)
    ·
      refine ⟨116491791556860802991883193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155322388742481070655844257 116491791556860802991883193)
      ·
        refine ⟨87368843667645602243912395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116491791556860802991883193 87368843667645602243912395)
        ·
          refine ⟨131053265501468403365868593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87368843667645602243912395 131053265501468403365868593)
          ·
            refine ⟨98289949126101302524401445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131053265501468403365868593 98289949126101302524401445)
            ·
              refine ⟨18429365461143994223325271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98289949126101302524401445 18429365461143994223325271)
              ·
                refine ⟨27644048191715991334987907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18429365461143994223325271 27644048191715991334987907)
                ·
                  refine ⟨41466072287573987002481861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27644048191715991334987907 41466072287573987002481861)
                  ·
                    refine ⟨7774888553920122562965349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41466072287573987002481861 7774888553920122562965349)
                    ·
                      refine ⟨1457791603860022980556003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7774888553920122562965349 1457791603860022980556003)
                      ·
                        rfl

theorem cell23_2839039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_2839039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839039 prefixEnd_2839039 := by exact prefixLift 2839039
  have htrace : WordTrace (prefixWord ++ tailWord_2839039) baseStart_2839039 baseEnd_2839039 := by
    simpa [prefixWord, tailWord_2839039, baseEnd_2839039] using wordTrace_append hprefix tailTrace_2839039
  have hstable : (prefixWord ++ tailWord_2839039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839039).length < 2 ^ (prefixWord ++ tailWord_2839039).sum := by decide
  have hdescent : baseEnd_2839039 < baseStart_2839039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839047 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2839047 : Nat := 118140960795 + 2839047 * 2 ^ 59
def prefixEnd_2839047 : Nat := 4983230072969 + 3 ^ 40 * 2839047 * 2
def baseEnd_2839047 : Nat := 1457795711705258949255967

theorem tailTrace_2839047 : CollatzResearch.WordTrace tailWord_2839047 prefixEnd_2839047 1457795711705258949255967 := by
  unfold tailWord_2839047
  simp only [CollatzResearch.WordTrace]
  refine ⟨103548550945625064470187395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69032367297083376313458263 103548550945625064470187395)
  ·
    refine ⟨155322826418437596705281093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103548550945625064470187395 155322826418437596705281093)
    ·
      refine ⟨29123029953457049382240205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155322826418437596705281093 29123029953457049382240205)
      ·
        refine ⟨10921136232546393518340077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29123029953457049382240205 10921136232546393518340077)
        ·
          refine ⟨4095426087204897569377529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10921136232546393518340077 4095426087204897569377529)
          ·
            refine ⟨3071569565403673177033147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4095426087204897569377529 3071569565403673177033147)
            ·
              refine ⟨4607354348105509765549721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071569565403673177033147 4607354348105509765549721)
              ·
                refine ⟨3455515761079132324162291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4607354348105509765549721 3455515761079132324162291)
                ·
                  refine ⟨5183273641618698486243437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455515761079132324162291 5183273641618698486243437)
                  ·
                    refine ⟨1943727615607011932341289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5183273641618698486243437 1943727615607011932341289)
                    ·
                      refine ⟨1457795711705258949255967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943727615607011932341289 1457795711705258949255967)
                      ·
                        rfl

theorem cell23_2839047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2839047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839047 prefixEnd_2839047 := by exact prefixLift 2839047
  have htrace : WordTrace (prefixWord ++ tailWord_2839047) baseStart_2839047 baseEnd_2839047 := by
    simpa [prefixWord, tailWord_2839047, baseEnd_2839047] using wordTrace_append hprefix tailTrace_2839047
  have hstable : (prefixWord ++ tailWord_2839047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839047).length < 2 ^ (prefixWord ++ tailWord_2839047).sum := by decide
  have hdescent : baseEnd_2839047 < baseStart_2839047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839060 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2839060 : Nat := 118140960795 + 2839060 * 2 ^ 59
def prefixEnd_2839060 : Nat := 4983230072969 + 3 ^ 40 * 2839060 * 2
def baseEnd_2839060 : Nat := 1457802386953767398393407

theorem tailTrace_2839060 : CollatzResearch.WordTrace tailWord_2839060 prefixEnd_2839060 1457802386953767398393407 := by
  unfold tailWord_2839060
  simp only [CollatzResearch.WordTrace]
  refine ⟨51774512547288983845205317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69032683396385311793607089 51774512547288983845205317)
  ·
    refine ⟨9707721102616684470975997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51774512547288983845205317 9707721102616684470975997)
    ·
      refine ⟨3640395413481256676615999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9707721102616684470975997 3640395413481256676615999)
      ·
        refine ⟨5460593120221885014923999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640395413481256676615999 5460593120221885014923999)
        ·
          refine ⟨8190889680332827522385999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460593120221885014923999 8190889680332827522385999)
          ·
            refine ⟨12286334520499241283578999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190889680332827522385999 12286334520499241283578999)
            ·
              refine ⟨18429501780748861925368499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286334520499241283578999 18429501780748861925368499)
              ·
                refine ⟨27644252671123292888052749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18429501780748861925368499 27644252671123292888052749)
                ·
                  refine ⟨10366594751671234833019781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27644252671123292888052749 10366594751671234833019781)
                  ·
                    refine ⟨1943736515938356531191209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10366594751671234833019781 1943736515938356531191209)
                    ·
                      refine ⟨1457802386953767398393407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943736515938356531191209 1457802386953767398393407)
                      ·
                        rfl

theorem cell23_2839060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2839060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839060 prefixEnd_2839060 := by exact prefixLift 2839060
  have htrace : WordTrace (prefixWord ++ tailWord_2839060) baseStart_2839060 baseEnd_2839060 := by
    simpa [prefixWord, tailWord_2839060, baseEnd_2839060] using wordTrace_append hprefix tailTrace_2839060
  have hstable : (prefixWord ++ tailWord_2839060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839060).length < 2 ^ (prefixWord ++ tailWord_2839060).sum := by decide
  have hdescent : baseEnd_2839060 < baseStart_2839060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
