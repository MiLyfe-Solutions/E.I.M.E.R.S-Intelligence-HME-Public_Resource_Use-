import V185TrunkScan23Chunk1209

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7168663 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_7168663 : Nat := 118140960795 + 7168663 * 2 ^ 59
def prefixEnd_7168663 : Nat := 4983230072969 + 3 ^ 40 * 7168663 * 2
def baseEnd_7168663 : Nat := 3680969769101991306744425

theorem tailTrace_7168663 : CollatzResearch.WordTrace tailWord_7168663 prefixEnd_7168663 3680969769101991306744425 := by
  unfold tailWord_7168663
  simp only [CollatzResearch.WordTrace]
  refine ⟨261462619628165736013198643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174308413085443824008799095 261462619628165736013198643)
  ·
    refine ⟨392193929442248604019797965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261462619628165736013198643 392193929442248604019797965)
    ·
      refine ⟨147072723540843226507424237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392193929442248604019797965 147072723540843226507424237)
      ·
        refine ⟨55152271327816209940284089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147072723540843226507424237 55152271327816209940284089)
        ·
          refine ⟨41364203495862157455213067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55152271327816209940284089 41364203495862157455213067)
          ·
            refine ⟨62046305243793236182819601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41364203495862157455213067 62046305243793236182819601)
            ·
              refine ⟨46534728932844927137114701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62046305243793236182819601 46534728932844927137114701)
              ·
                refine ⟨17450523349816847676418013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46534728932844927137114701 17450523349816847676418013)
                ·
                  refine ⟨6543946256181317878656755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17450523349816847676418013 6543946256181317878656755)
                  ·
                    refine ⟨9815919384271976817985133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543946256181317878656755 9815919384271976817985133)
                    ·
                      refine ⟨3680969769101991306744425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815919384271976817985133 3680969769101991306744425)
                      ·
                        rfl

theorem cell23_7168663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_7168663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168663 prefixEnd_7168663 := by exact prefixLift 7168663
  have htrace : WordTrace (prefixWord ++ tailWord_7168663) baseStart_7168663 baseEnd_7168663 := by
    simpa [prefixWord, tailWord_7168663, baseEnd_7168663] using wordTrace_append hprefix tailTrace_7168663
  have hstable : (prefixWord ++ tailWord_7168663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168663).length < 2 ^ (prefixWord ++ tailWord_7168663).sum := by decide
  have hdescent : baseEnd_7168663 < baseStart_7168663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168699 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_7168699 : Nat := 118140960795 + 7168699 * 2 ^ 59
def prefixEnd_7168699 : Nat := 4983230072969 + 3 ^ 40 * 7168699 * 2
def baseEnd_7168699 : Nat := 3680988254405553165894259

theorem tailTrace_7168699 : CollatzResearch.WordTrace tailWord_7168699 prefixEnd_7168699 3680988254405553165894259 := by
  unfold tailWord_7168699
  simp only [CollatzResearch.WordTrace]
  refine ⟨261463932656035314161509151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174309288437356876107672767 261463932656035314161509151)
  ·
    refine ⟨392195898984052971242263727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261463932656035314161509151 392195898984052971242263727)
    ·
      refine ⟨588293848476079456863395591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392195898984052971242263727 588293848476079456863395591)
      ·
        refine ⟨882440772714119185295093387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588293848476079456863395591 882440772714119185295093387)
        ·
          refine ⟨1323661159071178777942640081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882440772714119185295093387 1323661159071178777942640081)
          ·
            refine ⟨992745869303384083456980061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323661159071178777942640081 992745869303384083456980061)
            ·
              refine ⟨372279700988769031296367523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992745869303384083456980061 372279700988769031296367523)
              ·
                refine ⟨558419551483153546944551285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372279700988769031296367523 558419551483153546944551285)
                ·
                  refine ⟨52351832951545645026051683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558419551483153546944551285 52351832951545645026051683)
                  ·
                    refine ⟨78527749427318467539077525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52351832951545645026051683 78527749427318467539077525)
                    ·
                      refine ⟨3680988254405553165894259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78527749427318467539077525 3680988254405553165894259)
                      ·
                        rfl

theorem cell23_7168699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_7168699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168699 prefixEnd_7168699 := by exact prefixLift 7168699
  have htrace : WordTrace (prefixWord ++ tailWord_7168699) baseStart_7168699 baseEnd_7168699 := by
    simpa [prefixWord, tailWord_7168699, baseEnd_7168699] using wordTrace_append hprefix tailTrace_7168699
  have hstable : (prefixWord ++ tailWord_7168699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168699).length < 2 ^ (prefixWord ++ tailWord_7168699).sum := by decide
  have hdescent : baseEnd_7168699 < baseStart_7168699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168703 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_7168703 : Nat := 118140960795 + 7168703 * 2 ^ 59
def prefixEnd_7168703 : Nat := 4983230072969 + 3 ^ 40 * 7168703 * 2
def baseEnd_7168703 : Nat := 3680990308328171150244241

theorem tailTrace_7168703 : CollatzResearch.WordTrace tailWord_7168703 prefixEnd_7168703 3680990308328171150244241 := by
  unfold tailWord_7168703
  simp only [CollatzResearch.WordTrace]
  refine ⟨261464078548020822844654763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174309385698680548563103175 261464078548020822844654763)
  ·
    refine ⟨392196117822031234266982145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261464078548020822844654763 392196117822031234266982145)
    ·
      refine ⟨294147088366523425700236609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392196117822031234266982145 294147088366523425700236609)
      ·
        refine ⟨220610316274892569275177457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294147088366523425700236609 220610316274892569275177457)
        ·
          refine ⟨165457737206169426956383093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220610316274892569275177457 165457737206169426956383093)
          ·
            refine ⟨15511662863078383777160915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165457737206169426956383093 15511662863078383777160915)
            ·
              refine ⟨23267494294617575665741373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15511662863078383777160915 23267494294617575665741373)
              ·
                refine ⟨8725310360481590874653015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23267494294617575665741373 8725310360481590874653015)
                ·
                  refine ⟨13087965540722386311979523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725310360481590874653015 13087965540722386311979523)
                  ·
                    refine ⟨19631948311083579467969285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13087965540722386311979523 19631948311083579467969285)
                    ·
                      refine ⟨3680990308328171150244241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19631948311083579467969285 3680990308328171150244241)
                      ·
                        rfl

theorem cell23_7168703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_7168703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168703 prefixEnd_7168703 := by exact prefixLift 7168703
  have htrace : WordTrace (prefixWord ++ tailWord_7168703) baseStart_7168703 baseEnd_7168703 := by
    simpa [prefixWord, tailWord_7168703, baseEnd_7168703] using wordTrace_append hprefix tailTrace_7168703
  have hstable : (prefixWord ++ tailWord_7168703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168703).length < 2 ^ (prefixWord ++ tailWord_7168703).sum := by decide
  have hdescent : baseEnd_7168703 < baseStart_7168703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168719 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_7168719 : Nat := 118140960795 + 7168719 * 2 ^ 59
def prefixEnd_7168719 : Nat := 4983230072969 + 3 ^ 40 * 7168719 * 2
def baseEnd_7168719 : Nat := 3680998524018643087644167

theorem tailTrace_7168719 : CollatzResearch.WordTrace tailWord_7168719 prefixEnd_7168719 3680998524018643087644167 := by
  unfold tailWord_7168719
  simp only [CollatzResearch.WordTrace]
  refine ⟨261464662115962857577237211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174309774743975238384824807 261464662115962857577237211)
  ·
    refine ⟨392196993173944286365855817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261464662115962857577237211 392196993173944286365855817)
    ·
      refine ⟨294147744880458214774391863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392196993173944286365855817 294147744880458214774391863)
      ·
        refine ⟨441221617320687322161587795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294147744880458214774391863 441221617320687322161587795)
        ·
          refine ⟨661832425981030983242381693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441221617320687322161587795 661832425981030983242381693)
          ·
            refine ⟨248187159742886618715893135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661832425981030983242381693 248187159742886618715893135)
            ·
              refine ⟨372280739614329928073839703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248187159742886618715893135 372280739614329928073839703)
              ·
                refine ⟨558421109421494892110759555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372280739614329928073839703 558421109421494892110759555)
                ·
                  refine ⟨837631664132242338166139333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558421109421494892110759555 837631664132242338166139333)
                  ·
                    refine ⟨157055937024795438406151125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837631664132242338166139333 157055937024795438406151125)
                    ·
                      refine ⟨3680998524018643087644167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157055937024795438406151125 3680998524018643087644167)
                      ·
                        rfl

theorem cell23_7168719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_7168719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168719 prefixEnd_7168719 := by exact prefixLift 7168719
  have htrace : WordTrace (prefixWord ++ tailWord_7168719) baseStart_7168719 baseEnd_7168719 := by
    simpa [prefixWord, tailWord_7168719, baseEnd_7168719] using wordTrace_append hprefix tailTrace_7168719
  have hstable : (prefixWord ++ tailWord_7168719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168719).length < 2 ^ (prefixWord ++ tailWord_7168719).sum := by decide
  have hdescent : baseEnd_7168719 < baseStart_7168719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168730 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_7168730 : Nat := 118140960795 + 7168730 * 2 ^ 59
def prefixEnd_7168730 : Nat := 4983230072969 + 3 ^ 40 * 7168730 * 2
def baseEnd_7168730 : Nat := 1227001390768614181535539

theorem tailTrace_7168730 : CollatzResearch.WordTrace tailWord_7168730 prefixEnd_7168730 1227001390768614181535539 := by
  unfold tailWord_7168730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65366265829730751613971911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174310042212615337637258429 65366265829730751613971911)
  ·
    refine ⟨98049398744596127420957867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65366265829730751613971911 98049398744596127420957867)
    ·
      refine ⟨147074098116894191131436801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98049398744596127420957867 147074098116894191131436801)
      ·
        refine ⟨110305573587670643348577601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147074098116894191131436801 110305573587670643348577601)
        ·
          refine ⟨82729180190752982511433201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110305573587670643348577601 82729180190752982511433201)
          ·
            refine ⟨62046885143064736883574901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82729180190752982511433201 62046885143064736883574901)
            ·
              refine ⟨5816895482162319082835147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62046885143064736883574901 5816895482162319082835147)
              ·
                refine ⟨8725343223243478624252721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816895482162319082835147 8725343223243478624252721)
                ·
                  refine ⟨6544007417432608968189541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725343223243478624252721 6544007417432608968189541)
                  ·
                    refine ⟨1227001390768614181535539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544007417432608968189541 1227001390768614181535539)
                    ·
                      rfl

theorem cell23_7168730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_7168730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168730 prefixEnd_7168730 := by exact prefixLift 7168730
  have htrace : WordTrace (prefixWord ++ tailWord_7168730) baseStart_7168730 baseEnd_7168730 := by
    simpa [prefixWord, tailWord_7168730, baseEnd_7168730] using wordTrace_append hprefix tailTrace_7168730
  have hstable : (prefixWord ++ tailWord_7168730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168730).length < 2 ^ (prefixWord ++ tailWord_7168730).sum := by decide
  have hdescent : baseEnd_7168730 < baseStart_7168730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168740 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_7168740 : Nat := 118140960795 + 7168740 * 2 ^ 59
def prefixEnd_7168740 : Nat := 4983230072969 + 3 ^ 40 * 7168740 * 2
def baseEnd_7168740 : Nat := 3681009307112387505481571

theorem tailTrace_7168740 : CollatzResearch.WordTrace tailWord_7168740 prefixEnd_7168740 3681009307112387505481571 := by
  unfold tailWord_7168740
  simp only [CollatzResearch.WordTrace]
  refine ⟨130732714024443389081875837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174310285365924518775834449 130732714024443389081875837)
  ·
    refine ⟨49024767759166270905703439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130732714024443389081875837 49024767759166270905703439)
    ·
      refine ⟨73537151638749406358555159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49024767759166270905703439 73537151638749406358555159)
      ·
        refine ⟨110305727458124109537832739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73537151638749406358555159 110305727458124109537832739)
        ·
          refine ⟨165458591187186164306749109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110305727458124109537832739 165458591187186164306749109)
          ·
            refine ⟨15511742923798702903757729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165458591187186164306749109 15511742923798702903757729)
            ·
              refine ⟨11633807192849027177818297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511742923798702903757729 11633807192849027177818297)
              ·
                refine ⟨8725355394636770383363723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11633807192849027177818297 8725355394636770383363723)
                ·
                  refine ⟨13088033091955155575045585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725355394636770383363723 13088033091955155575045585)
                  ·
                    refine ⟨9816024818966366681284189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13088033091955155575045585 9816024818966366681284189)
                    ·
                      refine ⟨3681009307112387505481571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816024818966366681284189 3681009307112387505481571)
                      ·
                        rfl

theorem cell23_7168740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_7168740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168740 prefixEnd_7168740 := by exact prefixLift 7168740
  have htrace : WordTrace (prefixWord ++ tailWord_7168740) baseStart_7168740 baseEnd_7168740 := by
    simpa [prefixWord, tailWord_7168740, baseEnd_7168740] using wordTrace_append hprefix tailTrace_7168740
  have hstable : (prefixWord ++ tailWord_7168740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168740).length < 2 ^ (prefixWord ++ tailWord_7168740).sum := by decide
  have hdescent : baseEnd_7168740 < baseStart_7168740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168753 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_7168753 : Nat := 118140960795 + 7168753 * 2 ^ 59
def prefixEnd_7168753 : Nat := 4983230072969 + 3 ^ 40 * 7168753 * 2
def baseEnd_7168753 : Nat := 3681015982360895954619011

theorem tailTrace_7168753 : CollatzResearch.WordTrace tailWord_7168753 prefixEnd_7168753 3681015982360895954619011 := by
  unfold tailWord_7168753
  simp only [CollatzResearch.WordTrace]
  refine ⟨261465902197839681383974913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174310601465226454255983275 261465902197839681383974913)
  ·
    refine ⟨196099426648379761037981185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261465902197839681383974913 196099426648379761037981185)
    ·
      refine ⟨147074569986284820778485889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196099426648379761037981185 147074569986284820778485889)
      ·
        refine ⟨110305927489713615583864417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147074569986284820778485889 110305927489713615583864417)
        ·
          refine ⟨82729445617285211687898313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110305927489713615583864417 82729445617285211687898313)
          ·
            refine ⟨62047084212963908765923735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82729445617285211687898313 62047084212963908765923735)
            ·
              refine ⟨93070626319445863148885603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62047084212963908765923735 93070626319445863148885603)
              ·
                refine ⟨139605939479168794723328405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93070626319445863148885603 139605939479168794723328405)
                ·
                  refine ⟨6544028413086037252656019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139605939479168794723328405 6544028413086037252656019)
                  ·
                    refine ⟨9816042619629055878984029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6544028413086037252656019 9816042619629055878984029)
                    ·
                      refine ⟨3681015982360895954619011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816042619629055878984029 3681015982360895954619011)
                      ·
                        rfl

theorem cell23_7168753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_7168753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168753 prefixEnd_7168753 := by exact prefixLift 7168753
  have htrace : WordTrace (prefixWord ++ tailWord_7168753) baseStart_7168753 baseEnd_7168753 := by
    simpa [prefixWord, tailWord_7168753, baseEnd_7168753] using wordTrace_append hprefix tailTrace_7168753
  have hstable : (prefixWord ++ tailWord_7168753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168753).length < 2 ^ (prefixWord ++ tailWord_7168753).sum := by decide
  have hdescent : baseEnd_7168753 < baseStart_7168753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168754 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7168754 : Nat := 118140960795 + 7168754 * 2 ^ 59
def prefixEnd_7168754 : Nat := 4983230072969 + 3 ^ 40 * 7168754 * 2
def baseEnd_7168754 : Nat := 3681016495841550450706507

theorem tailTrace_7168754 : CollatzResearch.WordTrace tailWord_7168754 prefixEnd_7168754 3681016495841550450706507 := by
  unfold tailWord_7168754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65366484667709014638690329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174310625780557372369840877 65366484667709014638690329)
  ·
    refine ⟨49024863500781760979017747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65366484667709014638690329 49024863500781760979017747)
    ·
      refine ⟨73537295251172641468526621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49024863500781760979017747 73537295251172641468526621)
      ·
        refine ⟨27576485719189740550697483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73537295251172641468526621 27576485719189740550697483)
        ·
          refine ⟨41364728578784610826046225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27576485719189740550697483 41364728578784610826046225)
          ·
            refine ⟨31023546434088458119534669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41364728578784610826046225 31023546434088458119534669)
            ·
              refine ⟨11633829912783171794825501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31023546434088458119534669 11633829912783171794825501)
              ·
                refine ⟨4362686217293689423059563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633829912783171794825501 4362686217293689423059563)
                ·
                  refine ⟨6544029325940534134589345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362686217293689423059563 6544029325940534134589345)
                  ·
                    refine ⟨4908021994455400600942009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544029325940534134589345 4908021994455400600942009)
                    ·
                      refine ⟨3681016495841550450706507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908021994455400600942009 3681016495841550450706507)
                      ·
                        rfl

theorem cell23_7168754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7168754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168754 prefixEnd_7168754 := by exact prefixLift 7168754
  have htrace : WordTrace (prefixWord ++ tailWord_7168754) baseStart_7168754 baseEnd_7168754 := by
    simpa [prefixWord, tailWord_7168754, baseEnd_7168754] using wordTrace_append hprefix tailTrace_7168754
  have hstable : (prefixWord ++ tailWord_7168754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168754).length < 2 ^ (prefixWord ++ tailWord_7168754).sum := by decide
  have hdescent : baseEnd_7168754 < baseStart_7168754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168856 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7168856 : Nat := 118140960795 + 7168856 * 2 ^ 59
def prefixEnd_7168856 : Nat := 4983230072969 + 3 ^ 40 * 7168856 * 2
def baseEnd_7168856 : Nat := 3681068870868309051631037

theorem tailTrace_7168856 : CollatzResearch.WordTrace tailWord_7168856 prefixEnd_7168856 3681068870868309051631037 := by
  unfold tailWord_7168856
  simp only [CollatzResearch.WordTrace]
  refine ⟨130734829458233264987487211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174313105944311019983316281 130734829458233264987487211)
  ·
    refine ⟨196102244187349897481230817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130734829458233264987487211 196102244187349897481230817)
    ·
      refine ⟨147076683140512423110923113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196102244187349897481230817 147076683140512423110923113)
      ·
        refine ⟨110307512355384317333192335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147076683140512423110923113 110307512355384317333192335)
        ·
          refine ⟨165461268533076475999788503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110307512355384317333192335 165461268533076475999788503)
          ·
            refine ⟨248191902799614713999682755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165461268533076475999788503 248191902799614713999682755)
            ·
              refine ⟨372287854199422070999524133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248191902799614713999682755 372287854199422070999524133)
              ·
                refine ⟨69803972662391638312410775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372287854199422070999524133 69803972662391638312410775)
                ·
                  refine ⟨104705958993587457468616163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69803972662391638312410775 104705958993587457468616163)
                  ·
                    refine ⟨157058938490381186202924245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104705958993587457468616163 157058938490381186202924245)
                    ·
                      refine ⟨3681068870868309051631037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157058938490381186202924245 3681068870868309051631037)
                      ·
                        rfl

theorem cell23_7168856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7168856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168856 prefixEnd_7168856 := by exact prefixLift 7168856
  have htrace : WordTrace (prefixWord ++ tailWord_7168856) baseStart_7168856 baseEnd_7168856 := by
    simpa [prefixWord, tailWord_7168856, baseEnd_7168856] using wordTrace_append hprefix tailTrace_7168856
  have hstable : (prefixWord ++ tailWord_7168856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168856).length < 2 ^ (prefixWord ++ tailWord_7168856).sum := by decide
  have hdescent : baseEnd_7168856 < baseStart_7168856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168878 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7168878 : Nat := 118140960795 + 7168878 * 2 ^ 59
def prefixEnd_7168878 : Nat := 4983230072969 + 3 ^ 40 * 7168878 * 2
def baseEnd_7168878 : Nat := 3681080167442707965555937

theorem tailTrace_7168878 : CollatzResearch.WordTrace tailWord_7168878 prefixEnd_7168878 3681080167442707965555937 := by
  unfold tailWord_7168878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683807665298353466534411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174313640881591218488183525 32683807665298353466534411)
  ·
    refine ⟨49025711497947530199801617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32683807665298353466534411 49025711497947530199801617)
    ·
      refine ⟨36769283623460647649851213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49025711497947530199801617 36769283623460647649851213)
      ·
        refine ⟨13788481358797742868694205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36769283623460647649851213 13788481358797742868694205)
        ·
          refine ⟨5170680509549153575760327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13788481358797742868694205 5170680509549153575760327)
          ·
            refine ⟨7756020764323730363640491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170680509549153575760327 7756020764323730363640491)
            ·
              refine ⟨11634031146485595545460737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756020764323730363640491 11634031146485595545460737)
              ·
                refine ⟨8725523359864196659095553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11634031146485595545460737 8725523359864196659095553)
                ·
                  refine ⟨6544142519898147494321665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725523359864196659095553 6544142519898147494321665)
                  ·
                    refine ⟨4908106889923610620741249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544142519898147494321665 4908106889923610620741249)
                    ·
                      refine ⟨3681080167442707965555937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908106889923610620741249 3681080167442707965555937)
                      ·
                        rfl

theorem cell23_7168878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7168878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168878 prefixEnd_7168878 := by exact prefixLift 7168878
  have htrace : WordTrace (prefixWord ++ tailWord_7168878) baseStart_7168878 baseEnd_7168878 := by
    simpa [prefixWord, tailWord_7168878, baseEnd_7168878] using wordTrace_append hprefix tailTrace_7168878
  have hstable : (prefixWord ++ tailWord_7168878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168878).length < 2 ^ (prefixWord ++ tailWord_7168878).sum := by decide
  have hdescent : baseEnd_7168878 < baseStart_7168878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168883 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4]
def baseStart_7168883 : Nat := 118140960795 + 7168883 * 2 ^ 59
def prefixEnd_7168883 : Nat := 4983230072969 + 3 ^ 40 * 7168883 * 2
def baseEnd_7168883 : Nat := 3681082734845980445993413

theorem tailTrace_7168883 : CollatzResearch.WordTrace tailWord_7168883 prefixEnd_7168883 3681082734845980445993413 := by
  unfold tailWord_7168883
  simp only [CollatzResearch.WordTrace]
  refine ⟨261470643687368713586207303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174313762458245809057471535 261470643687368713586207303)
  ·
    refine ⟨392205965531053070379310955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261470643687368713586207303 392205965531053070379310955)
    ·
      refine ⟨588308948296579605568966433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392205965531053070379310955 588308948296579605568966433)
      ·
        refine ⟨441231711222434704176724825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588308948296579605568966433 441231711222434704176724825)
        ·
          refine ⟨330923783416826028132543619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441231711222434704176724825 330923783416826028132543619)
          ·
            refine ⟨496385675125239042198815429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330923783416826028132543619 496385675125239042198815429)
            ·
              refine ⟨93072314085982320412277893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 496385675125239042198815429 93072314085982320412277893)
              ·
                refine ⟨17451058891121685077302105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93072314085982320412277893 17451058891121685077302105)
                ·
                  refine ⟨13088294168341263807976579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17451058891121685077302105 13088294168341263807976579)
                  ·
                    refine ⟨19632441252511895711964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13088294168341263807976579 19632441252511895711964869)
                    ·
                      refine ⟨3681082734845980445993413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19632441252511895711964869 3681082734845980445993413)
                      ·
                        rfl

theorem cell23_7168883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_7168883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168883 prefixEnd_7168883 := by exact prefixLift 7168883
  have htrace : WordTrace (prefixWord ++ tailWord_7168883) baseStart_7168883 baseEnd_7168883 := by
    simpa [prefixWord, tailWord_7168883, baseEnd_7168883] using wordTrace_append hprefix tailTrace_7168883
  have hstable : (prefixWord ++ tailWord_7168883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168883).length < 2 ^ (prefixWord ++ tailWord_7168883).sum := by decide
  have hdescent : baseEnd_7168883 < baseStart_7168883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168977 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_7168977 : Nat := 118140960795 + 7168977 * 2 ^ 59
def prefixEnd_7168977 : Nat := 4983230072969 + 3 ^ 40 * 7168977 * 2
def baseEnd_7168977 : Nat := 3681131002027503078217981

theorem tailTrace_7168977 : CollatzResearch.WordTrace tailWord_7168977 prefixEnd_7168977 3681131002027503078217981 := by
  unfold tailWord_7168977
  simp only [CollatzResearch.WordTrace]
  refine ⟨261474072149028167640129185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174316048099352111760086123 261474072149028167640129185)
  ·
    refine ⟨196105554111771125730096889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261474072149028167640129185 196105554111771125730096889)
    ·
      refine ⟨147079165583828344297572667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196105554111771125730096889 147079165583828344297572667)
      ·
        refine ⟨220618748375742516446359001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147079165583828344297572667 220618748375742516446359001)
        ·
          refine ⟨165464061281806887334769251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220618748375742516446359001 165464061281806887334769251)
          ·
            refine ⟨248196091922710331002153877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165464061281806887334769251 248196091922710331002153877)
            ·
              refine ⟨11634191808877046765725963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248196091922710331002153877 11634191808877046765725963)
              ·
                refine ⟨17451287713315570148588945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11634191808877046765725963 17451287713315570148588945)
                ·
                  refine ⟨13088465784986677611441709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17451287713315570148588945 13088465784986677611441709)
                  ·
                    refine ⟨4908174669370004104290641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13088465784986677611441709 4908174669370004104290641)
                    ·
                      refine ⟨3681131002027503078217981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908174669370004104290641 3681131002027503078217981)
                      ·
                        rfl

theorem cell23_7168977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_7168977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168977 prefixEnd_7168977 := by exact prefixLift 7168977
  have htrace : WordTrace (prefixWord ++ tailWord_7168977) baseStart_7168977 baseEnd_7168977 := by
    simpa [prefixWord, tailWord_7168977, baseEnd_7168977] using wordTrace_append hprefix tailTrace_7168977
  have hstable : (prefixWord ++ tailWord_7168977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168977).length < 2 ^ (prefixWord ++ tailWord_7168977).sum := by decide
  have hdescent : baseEnd_7168977 < baseStart_7168977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169000 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7169000 : Nat := 118140960795 + 7169000 * 2 ^ 59
def prefixEnd_7169000 : Nat := 4983230072969 + 3 ^ 40 * 7169000 * 2
def baseEnd_7169000 : Nat := 1227047604027518829410125

theorem tailTrace_7169000 : CollatzResearch.WordTrace tailWord_7169000 prefixEnd_7169000 1227047604027518829410125 := by
  unfold tailWord_7169000
  simp only [CollatzResearch.WordTrace]
  refine ⟨130737455513972421284108227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174316607351963228378810969 130737455513972421284108227)
  ·
    refine ⟨196106183270958631926162341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130737455513972421284108227 196106183270958631926162341)
    ·
      refine ⟨36769909363304743486155439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196106183270958631926162341 36769909363304743486155439)
      ·
        refine ⟨55154864044957115229233159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36769909363304743486155439 55154864044957115229233159)
        ·
          refine ⟨82732296067435672843849739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55154864044957115229233159 82732296067435672843849739)
          ·
            refine ⟨124098444101153509265774609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82732296067435672843849739 124098444101153509265774609)
            ·
              refine ⟨93073833075865131949330957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124098444101153509265774609 93073833075865131949330957)
              ·
                refine ⟨34902687403449424480999109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93073833075865131949330957 34902687403449424480999109)
                ·
                  refine ⟨6544253888146767090187333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34902687403449424480999109 6544253888146767090187333)
                  ·
                    refine ⟨1227047604027518829410125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544253888146767090187333 1227047604027518829410125)
                    ·
                      rfl

theorem cell23_7169000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7169000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169000 prefixEnd_7169000 := by exact prefixLift 7169000
  have htrace : WordTrace (prefixWord ++ tailWord_7169000) baseStart_7169000 baseEnd_7169000 := by
    simpa [prefixWord, tailWord_7169000, baseEnd_7169000] using wordTrace_append hprefix tailTrace_7169000
  have hstable : (prefixWord ++ tailWord_7169000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169000).length < 2 ^ (prefixWord ++ tailWord_7169000).sum := by decide
  have hdescent : baseEnd_7169000 < baseStart_7169000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169020 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_7169020 : Nat := 118140960795 + 7169020 * 2 ^ 59
def prefixEnd_7169020 : Nat := 4983230072969 + 3 ^ 40 * 7169020 * 2
def baseEnd_7169020 : Nat := 3681153081695646409980283

theorem tailTrace_7169020 : CollatzResearch.WordTrace tailWord_7169020 prefixEnd_7169020 3681153081695646409980283 := by
  unfold tailWord_7169020
  simp only [CollatzResearch.WordTrace]
  refine ⟨130737820243936192991972257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174317093658581590655963009 130737820243936192991972257)
  ·
    refine ⟨98053365182952144743979193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130737820243936192991972257 98053365182952144743979193)
    ·
      refine ⟨73540023887214108557984395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98053365182952144743979193 73540023887214108557984395)
      ·
        refine ⟨110310035830821162836976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73540023887214108557984395 110310035830821162836976593)
        ·
          refine ⟨82732526873115872127732445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110310035830821162836976593 82732526873115872127732445)
          ·
            refine ⟨31024697577418452047899667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82732526873115872127732445 31024697577418452047899667)
            ·
              refine ⟨46537046366127678071849501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31024697577418452047899667 46537046366127678071849501)
              ·
                refine ⟨17451392387297879276943563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46537046366127678071849501 17451392387297879276943563)
                ·
                  refine ⟨26177088580946818915415345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17451392387297879276943563 26177088580946818915415345)
                  ·
                    refine ⟨19632816435710114186561509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26177088580946818915415345 19632816435710114186561509)
                    ·
                      refine ⟨3681153081695646409980283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19632816435710114186561509 3681153081695646409980283)
                      ·
                        rfl

theorem cell23_7169020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_7169020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169020 prefixEnd_7169020 := by exact prefixLift 7169020
  have htrace : WordTrace (prefixWord ++ tailWord_7169020) baseStart_7169020 baseEnd_7169020 := by
    simpa [prefixWord, tailWord_7169020, baseEnd_7169020] using wordTrace_append hprefix tailTrace_7169020
  have hstable : (prefixWord ++ tailWord_7169020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169020).length < 2 ^ (prefixWord ++ tailWord_7169020).sum := by decide
  have hdescent : baseEnd_7169020 < baseStart_7169020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169084 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_7169084 : Nat := 118140960795 + 7169084 * 2 ^ 59
def prefixEnd_7169084 : Nat := 4983230072969 + 3 ^ 40 * 7169084 * 2
def baseEnd_7169084 : Nat := 3681185944457534159579989

theorem tailTrace_7169084 : CollatzResearch.WordTrace tailWord_7169084 prefixEnd_7169084 3681185944457534159579989 := by
  unfold tailWord_7169084
  simp only [CollatzResearch.WordTrace]
  refine ⟨130738987379820262457137153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174318649839760349942849537 130738987379820262457137153)
  ·
    refine ⟨98054240534865196842852865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130738987379820262457137153 98054240534865196842852865)
    ·
      refine ⟨73540680401148897632139649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98054240534865196842852865 73540680401148897632139649)
      ·
        refine ⟨55155510300861673224104737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73540680401148897632139649 55155510300861673224104737)
        ·
          refine ⟨41366632725646254918078553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55155510300861673224104737 41366632725646254918078553)
          ·
            refine ⟨31024974544234691188558915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41366632725646254918078553 31024974544234691188558915)
            ·
              refine ⟨46537461816352036782838373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31024974544234691188558915 46537461816352036782838373)
              ·
                refine ⟨8725774090566006896782195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46537461816352036782838373 8725774090566006896782195)
                ·
                  refine ⟨13088661135849010345173293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725774090566006896782195 13088661135849010345173293)
                  ·
                    refine ⟨4908247925943378879439985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13088661135849010345173293 4908247925943378879439985)
                    ·
                      refine ⟨3681185944457534159579989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908247925943378879439985 3681185944457534159579989)
                      ·
                        rfl

theorem cell23_7169084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_7169084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169084 prefixEnd_7169084 := by exact prefixLift 7169084
  have htrace : WordTrace (prefixWord ++ tailWord_7169084) baseStart_7169084 baseEnd_7169084 := by
    simpa [prefixWord, tailWord_7169084, baseEnd_7169084] using wordTrace_append hprefix tailTrace_7169084
  have hstable : (prefixWord ++ tailWord_7169084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169084).length < 2 ^ (prefixWord ++ tailWord_7169084).sum := by decide
  have hdescent : baseEnd_7169084 < baseStart_7169084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169100 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7169100 : Nat := 118140960795 + 7169100 * 2 ^ 59
def prefixEnd_7169100 : Nat := 4983230072969 + 3 ^ 40 * 7169100 * 2
def baseEnd_7169100 : Nat := 3681194160148006096979915

theorem tailTrace_7169100 : CollatzResearch.WordTrace tailWord_7169100 prefixEnd_7169100 3681194160148006096979915 := by
  unfold tailWord_7169100
  simp only [CollatzResearch.WordTrace]
  refine ⟨130739279163791279823428377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174319038885055039764571169 130739279163791279823428377)
  ·
    refine ⟨98054459372843459867571283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130739279163791279823428377 98054459372843459867571283)
    ·
      refine ⟨147081689059265189801356925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98054459372843459867571283 147081689059265189801356925)
      ·
        refine ⟨55155633397224446175508847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147081689059265189801356925 55155633397224446175508847)
        ·
          refine ⟨82733450095836669263263271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55155633397224446175508847 82733450095836669263263271)
          ·
            refine ⟨124100175143755003894894907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82733450095836669263263271 124100175143755003894894907)
            ·
              refine ⟨186150262715632505842342361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124100175143755003894894907 186150262715632505842342361)
              ·
                refine ⟨139612697036724379381756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186150262715632505842342361 139612697036724379381756771)
                ·
                  refine ⟨209419045555086569072635157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139612697036724379381756771 209419045555086569072635157)
                  ·
                    refine ⟨9816517760394682925279773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 209419045555086569072635157 9816517760394682925279773)
                    ·
                      refine ⟨3681194160148006096979915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816517760394682925279773 3681194160148006096979915)
                      ·
                        rfl

theorem cell23_7169100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7169100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169100 prefixEnd_7169100 := by exact prefixLift 7169100
  have htrace : WordTrace (prefixWord ++ tailWord_7169100) baseStart_7169100 baseEnd_7169100 := by
    simpa [prefixWord, tailWord_7169100, baseEnd_7169100] using wordTrace_append hprefix tailTrace_7169100
  have hstable : (prefixWord ++ tailWord_7169100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169100).length < 2 ^ (prefixWord ++ tailWord_7169100).sum := by decide
  have hdescent : baseEnd_7169100 < baseStart_7169100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169101 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7169101 : Nat := 118140960795 + 7169101 * 2 ^ 59
def prefixEnd_7169101 : Nat := 4983230072969 + 3 ^ 40 * 7169101 * 2
def baseEnd_7169101 : Nat := 3681194673628660593067411

theorem tailTrace_7169101 : CollatzResearch.WordTrace tailWord_7169101 prefixEnd_7169101 3681194673628660593067411 := by
  unfold tailWord_7169101
  simp only [CollatzResearch.WordTrace]
  refine ⟨261478594800578936817643157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174319063200385957878428771 261478594800578936817643157)
  ·
    refine ⟨12256809131277137663327023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261478594800578936817643157 12256809131277137663327023)
    ·
      refine ⟨18385213696915706494990535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256809131277137663327023 18385213696915706494990535)
      ·
        refine ⟨27577820545373559742485803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18385213696915706494990535 27577820545373559742485803)
        ·
          refine ⟨41366730818060339613728705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27577820545373559742485803 41366730818060339613728705)
          ·
            refine ⟨31025048113545254710296529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41366730818060339613728705 31025048113545254710296529)
            ·
              refine ⟨23268786085158941032722397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31025048113545254710296529 23268786085158941032722397)
              ·
                refine ⟨8725794781934602887270899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23268786085158941032722397 8725794781934602887270899)
                ·
                  refine ⟨13088692172901904330906349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725794781934602887270899 13088692172901904330906349)
                  ·
                    refine ⟨4908259564838214124089881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13088692172901904330906349 4908259564838214124089881)
                    ·
                      refine ⟨3681194673628660593067411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908259564838214124089881 3681194673628660593067411)
                      ·
                        rfl

theorem cell23_7169101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7169101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169101 prefixEnd_7169101 := by exact prefixLift 7169101
  have htrace : WordTrace (prefixWord ++ tailWord_7169101) baseStart_7169101 baseEnd_7169101 := by
    simpa [prefixWord, tailWord_7169101, baseEnd_7169101] using wordTrace_append hprefix tailTrace_7169101
  have hstable : (prefixWord ++ tailWord_7169101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169101).length < 2 ^ (prefixWord ++ tailWord_7169101).sum := by decide
  have hdescent : baseEnd_7169101 < baseStart_7169101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169200 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_7169200 : Nat := 118140960795 + 7169200 * 2 ^ 59
def prefixEnd_7169200 : Nat := 4983230072969 + 3 ^ 40 * 7169200 * 2
def baseEnd_7169200 : Nat := 3681245508213455705729455

theorem tailTrace_7169200 : CollatzResearch.WordTrace tailWord_7169200 prefixEnd_7169200 3681245508213455705729455 := by
  unfold tailWord_7169200
  simp only [CollatzResearch.WordTrace]
  refine ⟨130741102813610138362748527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174321470418146851150331369 130741102813610138362748527)
  ·
    refine ⟨196111654220415207544122791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130741102813610138362748527 196111654220415207544122791)
    ·
      refine ⟨294167481330622811316184187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196111654220415207544122791 294167481330622811316184187)
      ·
        refine ⟨441251221995934216974276281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294167481330622811316184187 441251221995934216974276281)
        ·
          refine ⟨330938416496950662730707211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441251221995934216974276281 330938416496950662730707211)
          ·
            refine ⟨496407624745425994096060817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330938416496950662730707211 496407624745425994096060817)
            ·
              refine ⟨372305718559069495572045613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496407624745425994096060817 372305718559069495572045613)
              ·
                refine ⟨139614644459651060839517105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372305718559069495572045613 139614644459651060839517105)
                ·
                  refine ⟨104710983344738295629637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139614644459651060839517105 104710983344738295629637829)
                  ·
                    refine ⟨19633309377138430430557093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104710983344738295629637829 19633309377138430430557093)
                    ·
                      refine ⟨3681245508213455705729455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19633309377138430430557093 3681245508213455705729455)
                      ·
                        rfl

theorem cell23_7169200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_7169200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169200 prefixEnd_7169200 := by exact prefixLift 7169200
  have htrace : WordTrace (prefixWord ++ tailWord_7169200) baseStart_7169200 baseEnd_7169200 := by
    simpa [prefixWord, tailWord_7169200, baseEnd_7169200] using wordTrace_append hprefix tailTrace_7169200
  have hstable : (prefixWord ++ tailWord_7169200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169200).length < 2 ^ (prefixWord ++ tailWord_7169200).sum := by decide
  have hdescent : baseEnd_7169200 < baseStart_7169200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169207 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_7169207 : Nat := 118140960795 + 7169207 * 2 ^ 59
def prefixEnd_7169207 : Nat := 4983230072969 + 3 ^ 40 * 7169207 * 2
def baseEnd_7169207 : Nat := 3681249102578037178341923

theorem tailTrace_7169207 : CollatzResearch.WordTrace tailWord_7169207 prefixEnd_7169207 3681249102578037178341923 := by
  unfold tailWord_7169207
  simp only [CollatzResearch.WordTrace]
  refine ⟨261482460938194916921001875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174321640625463277947334583 261482460938194916921001875)
  ·
    refine ⟨392223691407292375381502813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261482460938194916921001875 392223691407292375381502813)
    ·
      refine ⟨147083884277734640768063555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392223691407292375381502813 147083884277734640768063555)
      ·
        refine ⟨220625826416601961152095333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147083884277734640768063555 220625826416601961152095333)
        ·
          refine ⟨41367342453112867716017875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220625826416601961152095333 41367342453112867716017875)
          ·
            refine ⟨62051013679669301574026813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41367342453112867716017875 62051013679669301574026813)
            ·
              refine ⟨23269130129875988090260055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62051013679669301574026813 23269130129875988090260055)
              ·
                refine ⟨34903695194813982135390083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23269130129875988090260055 34903695194813982135390083)
                ·
                  refine ⟨52355542792220973203085125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34903695194813982135390083 52355542792220973203085125)
                  ·
                    refine ⟨9816664273541432475578461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52355542792220973203085125 9816664273541432475578461)
                    ·
                      refine ⟨3681249102578037178341923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816664273541432475578461 3681249102578037178341923)
                      ·
                        rfl

theorem cell23_7169207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_7169207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169207 prefixEnd_7169207 := by exact prefixLift 7169207
  have htrace : WordTrace (prefixWord ++ tailWord_7169207) baseStart_7169207 baseEnd_7169207 := by
    simpa [prefixWord, tailWord_7169207, baseEnd_7169207] using wordTrace_append hprefix tailTrace_7169207
  have hstable : (prefixWord ++ tailWord_7169207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169207).length < 2 ^ (prefixWord ++ tailWord_7169207).sum := by decide
  have hdescent : baseEnd_7169207 < baseStart_7169207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169210 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_7169210 : Nat := 118140960795 + 7169210 * 2 ^ 59
def prefixEnd_7169210 : Nat := 4983230072969 + 3 ^ 40 * 7169210 * 2
def baseEnd_7169210 : Nat := 409027849224444518511601

theorem tailTrace_7169210 : CollatzResearch.WordTrace tailWord_7169210 prefixEnd_7169210 409027849224444518511601 := by
  unfold tailWord_7169210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65370642589296012108340271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174321713571456032288907389 65370642589296012108340271)
  ·
    refine ⟨98055963883944018162510407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65370642589296012108340271 98055963883944018162510407)
    ·
      refine ⟨147083945825916027243765611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98055963883944018162510407 147083945825916027243765611)
      ·
        refine ⟨220625918738874040865648417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147083945825916027243765611 220625918738874040865648417)
        ·
          refine ⟨165469439054155530649236313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220625918738874040865648417 165469439054155530649236313)
          ·
            refine ⟨124102079290616647986927235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165469439054155530649236313 124102079290616647986927235)
            ·
              refine ⟨186153118935924971980390853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124102079290616647986927235 186153118935924971980390853)
              ·
                refine ⟨34903709800485932246323285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186153118935924971980390853 34903709800485932246323285)
                ·
                  refine ⟨409027849224444518511601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34903709800485932246323285 409027849224444518511601)
                  ·
                    rfl

theorem cell23_7169210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_7169210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169210 prefixEnd_7169210 := by exact prefixLift 7169210
  have htrace : WordTrace (prefixWord ++ tailWord_7169210) baseStart_7169210 baseEnd_7169210 := by
    simpa [prefixWord, tailWord_7169210, baseEnd_7169210] using wordTrace_append hprefix tailTrace_7169210
  have hstable : (prefixWord ++ tailWord_7169210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169210).length < 2 ^ (prefixWord ++ tailWord_7169210).sum := by decide
  have hdescent : baseEnd_7169210 < baseStart_7169210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169277 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_7169277 : Nat := 118140960795 + 7169277 * 2 ^ 59
def prefixEnd_7169277 : Nat := 4983230072969 + 3 ^ 40 * 7169277 * 2
def baseEnd_7169277 : Nat := 3681285046223851904466601

theorem tailTrace_7169277 : CollatzResearch.WordTrace tailWord_7169277 prefixEnd_7169277 3681285046223851904466601 := by
  unfold tailWord_7169277
  simp only [CollatzResearch.WordTrace]
  refine ⟨261485014047941318876050085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174323342698627545917366723 261485014047941318876050085)
  ·
    refine ⟨49028440133988997289259391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261485014047941318876050085 49028440133988997289259391)
    ·
      refine ⟨73542660200983495933889087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49028440133988997289259391 73542660200983495933889087)
      ·
        refine ⟨110313990301475243900833631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73542660200983495933889087 110313990301475243900833631)
        ·
          refine ⟨165470985452212865851250447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110313990301475243900833631 165470985452212865851250447)
          ·
            refine ⟨248206478178319298776875671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165470985452212865851250447 248206478178319298776875671)
            ·
              refine ⟨372309717267478948165313507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248206478178319298776875671 372309717267478948165313507)
              ·
                refine ⟨558464575901218422247970261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372309717267478948165313507 558464575901218422247970261)
                ·
                  refine ⟨13089013497684806771436803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 558464575901218422247970261 13089013497684806771436803)
                  ·
                    refine ⟨19633520246527210157155205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13089013497684806771436803 19633520246527210157155205)
                    ·
                      refine ⟨3681285046223851904466601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19633520246527210157155205 3681285046223851904466601)
                      ·
                        rfl

theorem cell23_7169277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_7169277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169277 prefixEnd_7169277 := by exact prefixLift 7169277
  have htrace : WordTrace (prefixWord ++ tailWord_7169277) baseStart_7169277 baseEnd_7169277 := by
    simpa [prefixWord, tailWord_7169277, baseEnd_7169277] using wordTrace_append hprefix tailTrace_7169277
  have hstable : (prefixWord ++ tailWord_7169277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169277).length < 2 ^ (prefixWord ++ tailWord_7169277).sum := by decide
  have hdescent : baseEnd_7169277 < baseStart_7169277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169281 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7169281 : Nat := 118140960795 + 7169281 * 2 ^ 59
def prefixEnd_7169281 : Nat := 4983230072969 + 3 ^ 40 * 7169281 * 2
def baseEnd_7169281 : Nat := 3681287100146469888816583

theorem tailTrace_7169281 : CollatzResearch.WordTrace tailWord_7169281 prefixEnd_7169281 3681287100146469888816583 := by
  unfold tailWord_7169281
  simp only [CollatzResearch.WordTrace]
  refine ⟨261485159939926827559195697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174323439959951218372797131 261485159939926827559195697)
  ·
    refine ⟨196113869954945120669396773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261485159939926827559195697 196113869954945120669396773)
    ·
      refine ⟨36771350616552210125511895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196113869954945120669396773 36771350616552210125511895)
      ·
        refine ⟨55157025924828315188267843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36771350616552210125511895 55157025924828315188267843)
        ·
          refine ⟨82735538887242472782401765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55157025924828315188267843 82735538887242472782401765)
          ·
            refine ⟨15512913541357963646700331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82735538887242472782401765 15512913541357963646700331)
            ·
              refine ⟨23269370312036945470050497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15512913541357963646700331 23269370312036945470050497)
              ·
                refine ⟨17452027734027709102537873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23269370312036945470050497 17452027734027709102537873)
                ·
                  refine ⟨13089020800520781826903405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17452027734027709102537873 13089020800520781826903405)
                  ·
                    refine ⟨4908382800195293185088777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13089020800520781826903405 4908382800195293185088777)
                    ·
                      refine ⟨3681287100146469888816583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908382800195293185088777 3681287100146469888816583)
                      ·
                        rfl

theorem cell23_7169281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7169281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169281 prefixEnd_7169281 := by exact prefixLift 7169281
  have htrace : WordTrace (prefixWord ++ tailWord_7169281) baseStart_7169281 baseEnd_7169281 := by
    simpa [prefixWord, tailWord_7169281, baseEnd_7169281] using wordTrace_append hprefix tailTrace_7169281
  have hstable : (prefixWord ++ tailWord_7169281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169281).length < 2 ^ (prefixWord ++ tailWord_7169281).sum := by decide
  have hdescent : baseEnd_7169281 < baseStart_7169281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169288 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_7169288 : Nat := 118140960795 + 7169288 * 2 ^ 59
def prefixEnd_7169288 : Nat := 4983230072969 + 3 ^ 40 * 7169288 * 2
def baseEnd_7169288 : Nat := 3681290694511051361429051

theorem tailTrace_7169288 : CollatzResearch.WordTrace tailWord_7169288 prefixEnd_7169288 3681290694511051361429051 := by
  unfold tailWord_7169288
  simp only [CollatzResearch.WordTrace]
  refine ⟨130742707625450733877350259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174323610167267645169800345 130742707625450733877350259)
  ·
    refine ⟨196114061438176100816025389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130742707625450733877350259 196114061438176100816025389)
    ·
      refine ⟨73542773039316037806009521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196114061438176100816025389 73542773039316037806009521)
      ·
        refine ⟨55157079779487028354507141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73542773039316037806009521 55157079779487028354507141)
        ·
          refine ⟨10341952458653817816470089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55157079779487028354507141 10341952458653817816470089)
          ·
            refine ⟨7756464343990363362352567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341952458653817816470089 7756464343990363362352567)
            ·
              refine ⟨11634696515985545043528851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756464343990363362352567 11634696515985545043528851)
              ·
                refine ⟨17452044773978317565293277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11634696515985545043528851 17452044773978317565293277)
                ·
                  refine ⟨6544516790241869086984979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17452044773978317565293277 6544516790241869086984979)
                  ·
                    refine ⟨9816775185362803630477469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6544516790241869086984979 9816775185362803630477469)
                    ·
                      refine ⟨3681290694511051361429051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816775185362803630477469 3681290694511051361429051)
                      ·
                        rfl

theorem cell23_7169288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_7169288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169288 prefixEnd_7169288 := by exact prefixLift 7169288
  have htrace : WordTrace (prefixWord ++ tailWord_7169288) baseStart_7169288 baseEnd_7169288 := by
    simpa [prefixWord, tailWord_7169288, baseEnd_7169288] using wordTrace_append hprefix tailTrace_7169288
  have hstable : (prefixWord ++ tailWord_7169288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169288).length < 2 ^ (prefixWord ++ tailWord_7169288).sum := by decide
  have hdescent : baseEnd_7169288 < baseStart_7169288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169297 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_7169297 : Nat := 118140960795 + 7169297 * 2 ^ 59
def prefixEnd_7169297 : Nat := 4983230072969 + 3 ^ 40 * 7169297 * 2
def baseEnd_7169297 : Nat := 3681295315836941826216509

theorem tailTrace_7169297 : CollatzResearch.WordTrace tailWord_7169297 prefixEnd_7169297 3681295315836941826216509 := by
  unfold tailWord_7169297
  simp only [CollatzResearch.WordTrace]
  refine ⟨261485743507868862291778145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174323829005245908194518763 261485743507868862291778145)
  ·
    refine ⟨196114307630901646718833609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261485743507868862291778145 196114307630901646718833609)
    ·
      refine ⟨147085730723176235039125207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196114307630901646718833609 147085730723176235039125207)
      ·
        refine ⟨220628596084764352558687811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147085730723176235039125207 220628596084764352558687811)
        ·
          refine ⟨330942894127146528838031717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220628596084764352558687811 330942894127146528838031717)
          ·
            refine ⟨62051792648839974157130947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330942894127146528838031717 62051792648839974157130947)
            ·
              refine ⟨93077688973259961235696421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62051792648839974157130947 93077688973259961235696421)
              ·
                refine ⟨17452066682486242731693079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93077688973259961235696421 17452066682486242731693079)
                ·
                  refine ⟨26178100023729364097539619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452066682486242731693079 26178100023729364097539619)
                  ·
                    refine ⟨39267150035594046146309429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26178100023729364097539619 39267150035594046146309429)
                    ·
                      refine ⟨3681295315836941826216509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39267150035594046146309429 3681295315836941826216509)
                      ·
                        rfl

theorem cell23_7169297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_7169297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169297 prefixEnd_7169297 := by exact prefixLift 7169297
  have htrace : WordTrace (prefixWord ++ tailWord_7169297) baseStart_7169297 baseEnd_7169297 := by
    simpa [prefixWord, tailWord_7169297, baseEnd_7169297] using wordTrace_append hprefix tailTrace_7169297
  have hstable : (prefixWord ++ tailWord_7169297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169297).length < 2 ^ (prefixWord ++ tailWord_7169297).sum := by decide
  have hdescent : baseEnd_7169297 < baseStart_7169297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169307 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_7169307 : Nat := 118140960795 + 7169307 * 2 ^ 59
def prefixEnd_7169307 : Nat := 4983230072969 + 3 ^ 40 * 7169307 * 2
def baseEnd_7169307 : Nat := 3681300450643486787091463

theorem tailTrace_7169307 : CollatzResearch.WordTrace tailWord_7169307 prefixEnd_7169307 3681300450643486787091463 := by
  unfold tailWord_7169307
  simp only [CollatzResearch.WordTrace]
  refine ⟨261486108237832633999642175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174324072158555089333094783 261486108237832633999642175)
  ·
    refine ⟨392229162356748950999463263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261486108237832633999642175 392229162356748950999463263)
    ·
      refine ⟨588343743535123426499194895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392229162356748950999463263 588343743535123426499194895)
      ·
        refine ⟨882515615302685139748792343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588343743535123426499194895 882515615302685139748792343)
        ·
          refine ⟨1323773422954027709623188515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882515615302685139748792343 1323773422954027709623188515)
          ·
            refine ⟨1985660134431041564434782773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323773422954027709623188515 1985660134431041564434782773)
            ·
              refine ⟨186155637602910146665760885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1985660134431041564434782773 186155637602910146665760885)
              ·
                refine ⟨17452091025272826249915083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186155637602910146665760885 17452091025272826249915083)
                ·
                  refine ⟨26178136537909239374872625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452091025272826249915083 26178136537909239374872625)
                  ·
                    refine ⟨19633602403431929531154469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26178136537909239374872625 19633602403431929531154469)
                    ·
                      refine ⟨3681300450643486787091463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19633602403431929531154469 3681300450643486787091463)
                      ·
                        rfl

theorem cell23_7169307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_7169307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169307 prefixEnd_7169307 := by exact prefixLift 7169307
  have htrace : WordTrace (prefixWord ++ tailWord_7169307) baseStart_7169307 baseEnd_7169307 := by
    simpa [prefixWord, tailWord_7169307, baseEnd_7169307] using wordTrace_append hprefix tailTrace_7169307
  have hstable : (prefixWord ++ tailWord_7169307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169307).length < 2 ^ (prefixWord ++ tailWord_7169307).sum := by decide
  have hdescent : baseEnd_7169307 < baseStart_7169307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169317 : List Nat := [1, 3, 1, 2, 4, 1, 2, 9]
def baseStart_7169317 : Nat := 118140960795 + 7169317 * 2 ^ 59
def prefixEnd_7169317 : Nat := 4983230072969 + 3 ^ 40 * 7169317 * 2
def baseEnd_7169317 : Nat := 136344651312964138813571

theorem tailTrace_7169317 : CollatzResearch.WordTrace tailWord_7169317 prefixEnd_7169317 136344651312964138813571 := by
  unfold tailWord_7169317
  simp only [CollatzResearch.WordTrace]
  refine ⟨261486472967796405707506205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174324315311864270471670803 261486472967796405707506205)
  ·
    refine ⟨98057427362923652140314827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261486472967796405707506205 98057427362923652140314827)
    ·
      refine ⟨147086141044385478210472241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98057427362923652140314827 147086141044385478210472241)
      ·
        refine ⟨110314605783289108657854181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147086141044385478210472241 110314605783289108657854181)
        ·
          refine ⟨20683988584366707873347659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110314605783289108657854181 20683988584366707873347659)
          ·
            refine ⟨31025982876550061810021489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20683988584366707873347659 31025982876550061810021489)
            ·
              refine ⟨23269487157412546357516117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31025982876550061810021489 23269487157412546357516117)
              ·
                refine ⟨136344651312964138813571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23269487157412546357516117 136344651312964138813571)
                ·
                  rfl

theorem cell23_7169317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 9].length) (baseStart_7169317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169317 prefixEnd_7169317 := by exact prefixLift 7169317
  have htrace : WordTrace (prefixWord ++ tailWord_7169317) baseStart_7169317 baseEnd_7169317 := by
    simpa [prefixWord, tailWord_7169317, baseEnd_7169317] using wordTrace_append hprefix tailTrace_7169317
  have hstable : (prefixWord ++ tailWord_7169317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169317).length < 2 ^ (prefixWord ++ tailWord_7169317).sum := by decide
  have hdescent : baseEnd_7169317 < baseStart_7169317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169328 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 1, 2, 2]
def baseStart_7169328 : Nat := 118140960795 + 7169328 * 2 ^ 59
def prefixEnd_7169328 : Nat := 4983230072969 + 3 ^ 40 * 7169328 * 2
def baseEnd_7169328 : Nat := 3681311233737231204928867

theorem tailTrace_7169328 : CollatzResearch.WordTrace tailWord_7169328 prefixEnd_7169328 3681311233737231204928867 := by
  unfold tailWord_7169328
  simp only [CollatzResearch.WordTrace]
  refine ⟨130743437085378277293078319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174324582780504369724104425 130743437085378277293078319)
  ·
    refine ⟨196115155628067415939617479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130743437085378277293078319 196115155628067415939617479)
    ·
      refine ⟨294172733442101123909426219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196115155628067415939617479 294172733442101123909426219)
      ·
        refine ⟨441259100163151685864139329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294172733442101123909426219 441259100163151685864139329)
        ·
          refine ⟨330944325122363764398104497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441259100163151685864139329 330944325122363764398104497)
          ·
            refine ⟨248208243841772823298578373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330944325122363764398104497 248208243841772823298578373)
            ·
              refine ⟨46539045720332404368483445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248208243841772823298578373 46539045720332404368483445)
              ·
                refine ⟨4363035536281162909545323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46539045720332404368483445 4363035536281162909545323)
                ·
                  refine ⟨6544553304421744364317985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363035536281162909545323 6544553304421744364317985)
                  ·
                    refine ⟨4908414978316308273238489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544553304421744364317985 4908414978316308273238489)
                    ·
                      refine ⟨3681311233737231204928867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908414978316308273238489 3681311233737231204928867)
                      ·
                        rfl

theorem cell23_7169328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 2, 2].length) (baseStart_7169328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169328 prefixEnd_7169328 := by exact prefixLift 7169328
  have htrace : WordTrace (prefixWord ++ tailWord_7169328) baseStart_7169328 baseEnd_7169328 := by
    simpa [prefixWord, tailWord_7169328, baseEnd_7169328] using wordTrace_append hprefix tailTrace_7169328
  have hstable : (prefixWord ++ tailWord_7169328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169328).length < 2 ^ (prefixWord ++ tailWord_7169328).sum := by decide
  have hdescent : baseEnd_7169328 < baseStart_7169328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169334 : List Nat := [5, 1, 2, 3, 12]
def baseStart_7169334 : Nat := 118140960795 + 7169334 * 2 ^ 59
def prefixEnd_7169334 : Nat := 4983230072969 + 3 ^ 40 * 7169334 * 2
def baseEnd_7169334 : Nat := 5049813874651794487591

theorem tailTrace_7169334 : CollatzResearch.WordTrace tailWord_7169334 prefixEnd_7169334 5049813874651794487591 := by
  unfold tailWord_7169334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342943313045926100679691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174324728672489878407250037 16342943313045926100679691)
  ·
    refine ⟨24514414969568889151019537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342943313045926100679691 24514414969568889151019537)
    ·
      refine ⟨18385811227176666863264653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24514414969568889151019537 18385811227176666863264653)
      ·
        refine ⟨6894679210191250073724245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18385811227176666863264653 6894679210191250073724245)
        ·
          refine ⟨5049813874651794487591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6894679210191250073724245 5049813874651794487591)
          ·
            rfl

theorem cell23_7169334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 12].length) (baseStart_7169334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169334 prefixEnd_7169334 := by exact prefixLift 7169334
  have htrace : WordTrace (prefixWord ++ tailWord_7169334) baseStart_7169334 baseEnd_7169334 := by
    simpa [prefixWord, tailWord_7169334, baseEnd_7169334] using wordTrace_append hprefix tailTrace_7169334
  have hstable : (prefixWord ++ tailWord_7169334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169334).length < 2 ^ (prefixWord ++ tailWord_7169334).sum := by decide
  have hdescent : baseEnd_7169334 < baseStart_7169334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169361 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_7169361 : Nat := 118140960795 + 7169361 * 2 ^ 59
def prefixEnd_7169361 : Nat := 4983230072969 + 3 ^ 40 * 7169361 * 2
def baseEnd_7169361 : Nat := 3681328178598829575816215

theorem tailTrace_7169361 : CollatzResearch.WordTrace tailWord_7169361 prefixEnd_7169361 3681328178598829575816215 := by
  unfold tailWord_7169361
  simp only [CollatzResearch.WordTrace]
  refine ⟨261488077779637001222107937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174325385186424667481405291 261488077779637001222107937)
  ·
    refine ⟨196116058334727750916580953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261488077779637001222107937 196116058334727750916580953)
    ·
      refine ⟨147087043751045813187435715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196116058334727750916580953 147087043751045813187435715)
      ·
        refine ⟨220630565626568719781153573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147087043751045813187435715 220630565626568719781153573)
        ·
          refine ⟨41368231054981634958966295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220630565626568719781153573 41368231054981634958966295)
          ·
            refine ⟨62052346582472452438449443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41368231054981634958966295 62052346582472452438449443)
            ·
              refine ⟨93078519873708678657674165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62052346582472452438449443 93078519873708678657674165)
              ·
                refine ⟨8726111238160188624156953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93078519873708678657674165 8726111238160188624156953)
                ·
                  refine ⟨6544583428620141468117715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8726111238160188624156953 6544583428620141468117715)
                  ·
                    refine ⟨9816875142930212202176573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6544583428620141468117715 9816875142930212202176573)
                    ·
                      refine ⟨3681328178598829575816215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9816875142930212202176573 3681328178598829575816215)
                      ·
                        rfl

theorem cell23_7169361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_7169361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169361 prefixEnd_7169361 := by exact prefixLift 7169361
  have htrace : WordTrace (prefixWord ++ tailWord_7169361) baseStart_7169361 baseEnd_7169361 := by
    simpa [prefixWord, tailWord_7169361, baseEnd_7169361] using wordTrace_append hprefix tailTrace_7169361
  have hstable : (prefixWord ++ tailWord_7169361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169361).length < 2 ^ (prefixWord ++ tailWord_7169361).sum := by decide
  have hdescent : baseEnd_7169361 < baseStart_7169361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169366 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7169366 : Nat := 118140960795 + 7169366 * 2 ^ 59
def prefixEnd_7169366 : Nat := 4983230072969 + 3 ^ 40 * 7169366 * 2
def baseEnd_7169366 : Nat := 3681330746002102056253693

theorem tailTrace_7169366 : CollatzResearch.WordTrace tailWord_7169366 prefixEnd_7169366 3681330746002102056253693 := by
  unfold tailWord_7169366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343016259038680442252497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174325506763079258050693301 16343016259038680442252497)
  ·
    refine ⟨12257262194279010331689373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16343016259038680442252497 12257262194279010331689373)
    ·
      refine ⟨4596473322854628874383515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12257262194279010331689373 4596473322854628874383515)
      ·
        refine ⟨6894709984281943311575273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596473322854628874383515 6894709984281943311575273)
        ·
          refine ⟨5171032488211457483681455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6894709984281943311575273 5171032488211457483681455)
          ·
            refine ⟨7756548732317186225522183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171032488211457483681455 7756548732317186225522183)
            ·
              refine ⟨11634823098475779338283275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756548732317186225522183 11634823098475779338283275)
              ·
                refine ⟨17452234647713669007424913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11634823098475779338283275 17452234647713669007424913)
                ·
                  refine ⟨13089175985785251755568685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17452234647713669007424913 13089175985785251755568685)
                  ·
                    refine ⟨4908440994669469408338257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13089175985785251755568685 4908440994669469408338257)
                    ·
                      refine ⟨3681330746002102056253693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908440994669469408338257 3681330746002102056253693)
                      ·
                        rfl

theorem cell23_7169366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7169366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169366 prefixEnd_7169366 := by exact prefixLift 7169366
  have htrace : WordTrace (prefixWord ++ tailWord_7169366) baseStart_7169366 baseEnd_7169366 := by
    simpa [prefixWord, tailWord_7169366, baseEnd_7169366] using wordTrace_append hprefix tailTrace_7169366
  have hstable : (prefixWord ++ tailWord_7169366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169366).length < 2 ^ (prefixWord ++ tailWord_7169366).sum := by decide
  have hdescent : baseEnd_7169366 < baseStart_7169366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169388 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_7169388 : Nat := 118140960795 + 7169388 * 2 ^ 59
def prefixEnd_7169388 : Nat := 4983230072969 + 3 ^ 40 * 7169388 * 2
def baseEnd_7169388 : Nat := 3681342042576500970178591

theorem tailTrace_7169388 : CollatzResearch.WordTrace tailWord_7169388 prefixEnd_7169388 3681342042576500970178591 := by
  unfold tailWord_7169388
  simp only [CollatzResearch.WordTrace]
  refine ⟨130744531275269592416670409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174326041700359456555560545 130744531275269592416670409)
  ·
    refine ⟨98058398456452194312502807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130744531275269592416670409 98058398456452194312502807)
    ·
      refine ⟨147087597684678291468754211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98058398456452194312502807 147087597684678291468754211)
      ·
        refine ⟨220631396527017437203131317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147087597684678291468754211 220631396527017437203131317)
        ·
          refine ⟨20684193424407884737793561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220631396527017437203131317 20684193424407884737793561)
          ·
            refine ⟨15513145068305913553345171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20684193424407884737793561 15513145068305913553345171)
            ·
              refine ⟨23269717602458870330017757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513145068305913553345171 23269717602458870330017757)
              ·
                refine ⟨8726144100922076373756659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23269717602458870330017757 8726144100922076373756659)
                ·
                  refine ⟨13089216151383114560634989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8726144100922076373756659 13089216151383114560634989)
                  ·
                    refine ⟨4908456056768667960238121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13089216151383114560634989 4908456056768667960238121)
                    ·
                      refine ⟨3681342042576500970178591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908456056768667960238121 3681342042576500970178591)
                      ·
                        rfl

theorem cell23_7169388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_7169388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169388 prefixEnd_7169388 := by exact prefixLift 7169388
  have htrace : WordTrace (prefixWord ++ tailWord_7169388) baseStart_7169388 baseEnd_7169388 := by
    simpa [prefixWord, tailWord_7169388, baseEnd_7169388] using wordTrace_append hprefix tailTrace_7169388
  have hstable : (prefixWord ++ tailWord_7169388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169388).length < 2 ^ (prefixWord ++ tailWord_7169388).sum := by decide
  have hdescent : baseEnd_7169388 < baseStart_7169388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169438 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7169438 : Nat := 118140960795 + 7169438 * 2 ^ 59
def prefixEnd_7169438 : Nat := 4983230072969 + 3 ^ 40 * 7169438 * 2
def baseEnd_7169438 : Nat := 3681367716609225774553361

theorem tailTrace_7169438 : CollatzResearch.WordTrace tailWord_7169438 prefixEnd_7169438 3681367716609225774553361 := by
  unfold tailWord_7169438
  simp only [CollatzResearch.WordTrace]
  refine ⟨32686360775044755421582621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174327257466905362248440645 32686360775044755421582621)
  ·
    refine ⟨12257385290641783283093483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32686360775044755421582621 12257385290641783283093483)
    ·
      refine ⟨18386077935962674924640225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12257385290641783283093483 18386077935962674924640225)
      ·
        refine ⟨13789558451972006193480169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18386077935962674924640225 13789558451972006193480169)
        ·
          refine ⟨10342168838979004645110127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13789558451972006193480169 10342168838979004645110127)
          ·
            refine ⟨15513253258468506967665191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342168838979004645110127 15513253258468506967665191)
            ·
              refine ⟨23269879887702760451497787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513253258468506967665191 23269879887702760451497787)
              ·
                refine ⟨34904819831554140677246681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23269879887702760451497787 34904819831554140677246681)
                ·
                  refine ⟨26178614873665605507935011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34904819831554140677246681 26178614873665605507935011)
                  ·
                    refine ⟨39267922310498408261902517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26178614873665605507935011 39267922310498408261902517)
                    ·
                      refine ⟨3681367716609225774553361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39267922310498408261902517 3681367716609225774553361)
                      ·
                        rfl

theorem cell23_7169438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7169438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169438 prefixEnd_7169438 := by exact prefixLift 7169438
  have htrace : WordTrace (prefixWord ++ tailWord_7169438) baseStart_7169438 baseEnd_7169438 := by
    simpa [prefixWord, tailWord_7169438, baseEnd_7169438] using wordTrace_append hprefix tailTrace_7169438
  have hstable : (prefixWord ++ tailWord_7169438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169438).length < 2 ^ (prefixWord ++ tailWord_7169438).sum := by decide
  have hdescent : baseEnd_7169438 < baseStart_7169438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169525 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7169525 : Nat := 118140960795 + 7169525 * 2 ^ 59
def prefixEnd_7169525 : Nat := 4983230072969 + 3 ^ 40 * 7169525 * 2
def baseEnd_7169525 : Nat := 3681412389426166934165461

theorem tailTrace_7169525 : CollatzResearch.WordTrace tailWord_7169525 prefixEnd_7169525 3681412389426166934165461 := by
  unfold tailWord_7169525
  simp only [CollatzResearch.WordTrace]
  refine ⟨261494059351042857231078029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174329372900695238154052019 261494059351042857231078029)
  ·
    refine ⟨98060272256641071461654261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261494059351042857231078029 98060272256641071461654261)
    ·
      refine ⟨9193150524060100449530087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98060272256641071461654261 9193150524060100449530087)
      ·
        refine ⟨13789725786090150674295131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193150524060100449530087 13789725786090150674295131)
        ·
          refine ⟨20684588679135226011442697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789725786090150674295131 20684588679135226011442697)
          ·
            refine ⟨15513441509351419508582023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20684588679135226011442697 15513441509351419508582023)
            ·
              refine ⟨23270162264027129262873035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513441509351419508582023 23270162264027129262873035)
              ·
                refine ⟨34905243396040693894309553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23270162264027129262873035 34905243396040693894309553)
                ·
                  refine ⟨26178932547030520420732165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34905243396040693894309553 26178932547030520420732165)
                  ·
                    refine ⟨4908549852568222578887281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26178932547030520420732165 4908549852568222578887281)
                    ·
                      refine ⟨3681412389426166934165461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908549852568222578887281 3681412389426166934165461)
                      ·
                        rfl

theorem cell23_7169525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7169525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169525 prefixEnd_7169525 := by exact prefixLift 7169525
  have htrace : WordTrace (prefixWord ++ tailWord_7169525) baseStart_7169525 baseEnd_7169525 := by
    simpa [prefixWord, tailWord_7169525, baseEnd_7169525] using wordTrace_append hprefix tailTrace_7169525
  have hstable : (prefixWord ++ tailWord_7169525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169525).length < 2 ^ (prefixWord ++ tailWord_7169525).sum := by decide
  have hdescent : baseEnd_7169525 < baseStart_7169525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169542 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7169542 : Nat := 118140960795 + 7169542 * 2 ^ 59
def prefixEnd_7169542 : Nat := 4983230072969 + 3 ^ 40 * 7169542 * 2
def baseEnd_7169542 : Nat := 3681421118597293367652883

theorem tailTrace_7169542 : CollatzResearch.WordTrace tailWord_7169542 prefixEnd_7169542 3681421118597293367652883 := by
  unfold tailWord_7169542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171708730999414660451465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174329786261320846089631253 8171708730999414660451465)
  ·
    refine ⟨6128781548249560995338599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8171708730999414660451465 6128781548249560995338599)
    ·
      refine ⟨9193172322374341493007899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6128781548249560995338599 9193172322374341493007899)
      ·
        refine ⟨13789758483561512239511849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193172322374341493007899 13789758483561512239511849)
        ·
          refine ⟨10342318862671134179633887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13789758483561512239511849 10342318862671134179633887)
          ·
            refine ⟨15513478294006701269450831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342318862671134179633887 15513478294006701269450831)
            ·
              refine ⟨23270217441010051904176247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513478294006701269450831 23270217441010051904176247)
              ·
                refine ⟨34905326161515077856264371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23270217441010051904176247 34905326161515077856264371)
                ·
                  refine ⟨52357989242272616784396557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34905326161515077856264371 52357989242272616784396557)
                  ·
                    refine ⟨19634245965852231294148709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52357989242272616784396557 19634245965852231294148709)
                    ·
                      refine ⟨3681421118597293367652883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19634245965852231294148709 3681421118597293367652883)
                      ·
                        rfl

theorem cell23_7169542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7169542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169542 prefixEnd_7169542 := by exact prefixLift 7169542
  have htrace : WordTrace (prefixWord ++ tailWord_7169542) baseStart_7169542 baseEnd_7169542 := by
    simpa [prefixWord, tailWord_7169542, baseEnd_7169542] using wordTrace_append hprefix tailTrace_7169542
  have hstable : (prefixWord ++ tailWord_7169542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169542).length < 2 ^ (prefixWord ++ tailWord_7169542).sum := by decide
  have hdescent : baseEnd_7169542 < baseStart_7169542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169591 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 6]
def baseStart_7169591 : Nat := 118140960795 + 7169591 * 2 ^ 59
def prefixEnd_7169591 : Nat := 4983230072969 + 3 ^ 40 * 7169591 * 2
def baseEnd_7169591 : Nat := 1227148759716454558646719

theorem tailTrace_7169591 : CollatzResearch.WordTrace tailWord_7169591 prefixEnd_7169591 1227148759716454558646719 := by
  unfold tailWord_7169591
  simp only [CollatzResearch.WordTrace]
  refine ⟨261496466568803750502980627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174330977712535833668653751 261496466568803750502980627)
  ·
    refine ⟨392244699853205625754470941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261496466568803750502980627 392244699853205625754470941)
    ·
      refine ⟨147091762444952109657926603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392244699853205625754470941 147091762444952109657926603)
      ·
        refine ⟨220637643667428164486889905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147091762444952109657926603 220637643667428164486889905)
        ·
          refine ⟨165478232750571123365167429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220637643667428164486889905 165478232750571123365167429)
          ·
            refine ⟨31027168640732085630968893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165478232750571123365167429 31027168640732085630968893)
            ·
              refine ⟨11635188240274532111613335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31027168640732085630968893 11635188240274532111613335)
              ·
                refine ⟨17452782360411798167420003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635188240274532111613335 17452782360411798167420003)
                ·
                  refine ⟨26179173540617697251130005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452782360411798167420003 26179173540617697251130005)
                  ·
                    refine ⟨1227148759716454558646719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26179173540617697251130005 1227148759716454558646719)
                    ·
                      rfl

theorem cell23_7169591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_7169591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169591 prefixEnd_7169591 := by exact prefixLift 7169591
  have htrace : WordTrace (prefixWord ++ tailWord_7169591) baseStart_7169591 baseEnd_7169591 := by
    simpa [prefixWord, tailWord_7169591, baseEnd_7169591] using wordTrace_append hprefix tailTrace_7169591
  have hstable : (prefixWord ++ tailWord_7169591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169591).length < 2 ^ (prefixWord ++ tailWord_7169591).sum := by decide
  have hdescent : baseEnd_7169591 < baseStart_7169591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169601 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7169601 : Nat := 118140960795 + 7169601 * 2 ^ 59
def prefixEnd_7169601 : Nat := 4983230072969 + 3 ^ 40 * 7169601 * 2
def baseEnd_7169601 : Nat := 3681451413955908636815111

theorem tailTrace_7169601 : CollatzResearch.WordTrace tailWord_7169601 prefixEnd_7169601 3681451413955908636815111 := by
  unfold tailWord_7169601
  simp only [CollatzResearch.WordTrace]
  refine ⟨261496831298767522210844657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174331220865845014807229771 261496831298767522210844657)
  ·
    refine ⟨196122623474075641658133493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261496831298767522210844657 196122623474075641658133493)
    ·
      refine ⟨18386495950694591405450015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196122623474075641658133493 18386495950694591405450015)
      ·
        refine ⟨27579743926041887108175023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18386495950694591405450015 27579743926041887108175023)
        ·
          refine ⟨41369615889062830662262535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27579743926041887108175023 41369615889062830662262535)
          ·
            refine ⟨62054423833594245993393803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41369615889062830662262535 62054423833594245993393803)
            ·
              refine ⟨93081635750391368990090705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62054423833594245993393803 93081635750391368990090705)
              ·
                refine ⟨69811226812793526742568029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93081635750391368990090705 69811226812793526742568029)
                ·
                  refine ⟨26179210054797572528463011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69811226812793526742568029 26179210054797572528463011)
                  ·
                    refine ⟨39268815082196358792694517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26179210054797572528463011 39268815082196358792694517)
                    ·
                      refine ⟨3681451413955908636815111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39268815082196358792694517 3681451413955908636815111)
                      ·
                        rfl

theorem cell23_7169601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7169601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169601 prefixEnd_7169601 := by exact prefixLift 7169601
  have htrace : WordTrace (prefixWord ++ tailWord_7169601) baseStart_7169601 baseEnd_7169601 := by
    simpa [prefixWord, tailWord_7169601, baseEnd_7169601] using wordTrace_append hprefix tailTrace_7169601
  have hstable : (prefixWord ++ tailWord_7169601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169601).length < 2 ^ (prefixWord ++ tailWord_7169601).sum := by decide
  have hdescent : baseEnd_7169601 < baseStart_7169601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169618 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_7169618 : Nat := 118140960795 + 7169618 * 2 ^ 59
def prefixEnd_7169618 : Nat := 4983230072969 + 3 ^ 40 * 7169618 * 2
def baseEnd_7169618 : Nat := 3681460143127035070302533

theorem tailTrace_7169618 : CollatzResearch.WordTrace tailWord_7169618 prefixEnd_7169618 3681460143127035070302533 := by
  unfold tailWord_7169618
  simp only [CollatzResearch.WordTrace]
  refine ⟨65374362834926483528553377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174331634226470622742809005 65374362834926483528553377)
  ·
    refine ⟨49030772126194862646415033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65374362834926483528553377 49030772126194862646415033)
    ·
      refine ⟨36773079094646146984811275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49030772126194862646415033 36773079094646146984811275)
      ·
        refine ⟨55159618641969220477216913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36773079094646146984811275 55159618641969220477216913)
        ·
          refine ⟨41369713981476915357912685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55159618641969220477216913 41369713981476915357912685)
          ·
            refine ⟨15513642743053843259217257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41369713981476915357912685 15513642743053843259217257)
            ·
              refine ⟨11635232057290382444412943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15513642743053843259217257 11635232057290382444412943)
              ·
                refine ⟨17452848085935573666619415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635232057290382444412943 17452848085935573666619415)
                ·
                  refine ⟨26179272128903360499929123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452848085935573666619415 26179272128903360499929123)
                  ·
                    refine ⟨39268908193355040749893685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26179272128903360499929123 39268908193355040749893685)
                    ·
                      refine ⟨3681460143127035070302533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39268908193355040749893685 3681460143127035070302533)
                      ·
                        rfl

theorem cell23_7169618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_7169618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169618 prefixEnd_7169618 := by exact prefixLift 7169618
  have htrace : WordTrace (prefixWord ++ tailWord_7169618) baseStart_7169618 baseEnd_7169618 := by
    simpa [prefixWord, tailWord_7169618, baseEnd_7169618] using wordTrace_append hprefix tailTrace_7169618
  have hstable : (prefixWord ++ tailWord_7169618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169618).length < 2 ^ (prefixWord ++ tailWord_7169618).sum := by decide
  have hdescent : baseEnd_7169618 < baseStart_7169618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169642 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7169642 : Nat := 118140960795 + 7169642 * 2 ^ 59
def prefixEnd_7169642 : Nat := 4983230072969 + 3 ^ 40 * 7169642 * 2
def baseEnd_7169642 : Nat := 1227157488887580992134141

theorem tailTrace_7169642 : CollatzResearch.WordTrace tailWord_7169642 prefixEnd_7169642 1227157488887580992134141 := by
  unfold tailWord_7169642
  simp only [CollatzResearch.WordTrace]
  refine ⟨65374581672904746553271795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174332217794412657475391453 65374581672904746553271795)
  ·
    refine ⟨98061872509357119829907693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65374581672904746553271795 98061872509357119829907693)
    ·
      refine ⟨36773202191008919936215385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98061872509357119829907693 36773202191008919936215385)
      ·
        refine ⟨27579901643256689952161539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36773202191008919936215385 27579901643256689952161539)
        ·
          refine ⟨41369852464885034928242309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27579901643256689952161539 41369852464885034928242309)
          ·
            refine ⟨7756847337165944049045433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41369852464885034928242309 7756847337165944049045433)
            ·
              refine ⟨5817635502874458036784075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756847337165944049045433 5817635502874458036784075)
              ·
                refine ⟨8726453254311687055176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817635502874458036784075 8726453254311687055176113)
                ·
                  refine ⟨6544839940733765291382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8726453254311687055176113 6544839940733765291382085)
                  ·
                    refine ⟨1227157488887580992134141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544839940733765291382085 1227157488887580992134141)
                    ·
                      rfl

theorem cell23_7169642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7169642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169642 prefixEnd_7169642 := by exact prefixLift 7169642
  have htrace : WordTrace (prefixWord ++ tailWord_7169642) baseStart_7169642 baseEnd_7169642 := by
    simpa [prefixWord, tailWord_7169642, baseEnd_7169642] using wordTrace_append hprefix tailTrace_7169642
  have hstable : (prefixWord ++ tailWord_7169642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169642).length < 2 ^ (prefixWord ++ tailWord_7169642).sum := by decide
  have hdescent : baseEnd_7169642 < baseStart_7169642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169701 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_7169701 : Nat := 118140960795 + 7169701 * 2 ^ 59
def prefixEnd_7169701 : Nat := 4983230072969 + 3 ^ 40 * 7169701 * 2
def baseEnd_7169701 : Nat := 3681502762021358245564651

theorem tailTrace_7169701 : CollatzResearch.WordTrace tailWord_7169701 prefixEnd_7169701 3681502762021358245564651 := by
  unfold tailWord_7169701
  simp only [CollatzResearch.WordTrace]
  refine ⟨261500478598405239289484957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174333652398936826192989971 261500478598405239289484957)
  ·
    refine ⟨98062679474401964733556859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261500478598405239289484957 98062679474401964733556859)
    ·
      refine ⟨147094019211602947100335289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98062679474401964733556859 147094019211602947100335289)
      ·
        refine ⟨110320514408702210325251467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147094019211602947100335289 110320514408702210325251467)
        ·
          refine ⟨165480771613053315487877201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110320514408702210325251467 165480771613053315487877201)
          ·
            refine ⟨124110578709789986615907901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165480771613053315487877201 124110578709789986615907901)
            ·
              refine ⟨46541467016171244980965463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124110578709789986615907901 46541467016171244980965463)
              ·
                refine ⟨69812200524256867471448195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46541467016171244980965463 69812200524256867471448195)
                ·
                  refine ⟨104718300786385301207172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69812200524256867471448195 104718300786385301207172293)
                  ·
                    refine ⟨19634681397447243976344805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104718300786385301207172293 19634681397447243976344805)
                    ·
                      refine ⟨3681502762021358245564651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19634681397447243976344805 3681502762021358245564651)
                      ·
                        rfl

theorem cell23_7169701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_7169701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169701 prefixEnd_7169701 := by exact prefixLift 7169701
  have htrace : WordTrace (prefixWord ++ tailWord_7169701) baseStart_7169701 baseEnd_7169701 := by
    simpa [prefixWord, tailWord_7169701, baseEnd_7169701] using wordTrace_append hprefix tailTrace_7169701
  have hstable : (prefixWord ++ tailWord_7169701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169701).length < 2 ^ (prefixWord ++ tailWord_7169701).sum := by decide
  have hdescent : baseEnd_7169701 < baseStart_7169701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169711 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 7]
def baseStart_7169711 : Nat := 118140960795 + 7169711 * 2 ^ 59
def prefixEnd_7169711 : Nat := 4983230072969 + 3 ^ 40 * 7169711 * 2
def baseEnd_7169711 : Nat := 409056432980878134048845

theorem tailTrace_7169711 : CollatzResearch.WordTrace tailWord_7169711 prefixEnd_7169711 409056432980878134048845 := by
  unfold tailWord_7169711
  simp only [CollatzResearch.WordTrace]
  refine ⟨261500843328369010997348987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174333895552246007331565991 261500843328369010997348987)
  ·
    refine ⟨392251264992553516496023481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261500843328369010997348987 392251264992553516496023481)
    ·
      refine ⟨294188448744415137372017611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392251264992553516496023481 294188448744415137372017611)
      ·
        refine ⟨441282673116622706058026417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294188448744415137372017611 441282673116622706058026417)
        ·
          refine ⟨330962004837467029543519813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441282673116622706058026417 330962004837467029543519813)
          ·
            refine ⟨62055375907025068039409965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330962004837467029543519813 62055375907025068039409965)
            ·
              refine ⟨23270765965134400514778737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62055375907025068039409965 23270765965134400514778737)
              ·
                refine ⟨17453074473850800386084053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23270765965134400514778737 17453074473850800386084053)
                ·
                  refine ⟨409056432980878134048845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17453074473850800386084053 409056432980878134048845)
                  ·
                    rfl

theorem cell23_7169711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 7].length) (baseStart_7169711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169711 prefixEnd_7169711 := by exact prefixLift 7169711
  have htrace : WordTrace (prefixWord ++ tailWord_7169711) baseStart_7169711 baseEnd_7169711 := by
    simpa [prefixWord, tailWord_7169711, baseEnd_7169711] using wordTrace_append hprefix tailTrace_7169711
  have hstable : (prefixWord ++ tailWord_7169711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169711).length < 2 ^ (prefixWord ++ tailWord_7169711).sum := by decide
  have hdescent : baseEnd_7169711 < baseStart_7169711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169751 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_7169751 : Nat := 118140960795 + 7169751 * 2 ^ 59
def prefixEnd_7169751 : Nat := 4983230072969 + 3 ^ 40 * 7169751 * 2
def baseEnd_7169751 : Nat := 3681528436054083049939421

theorem tailTrace_7169751 : CollatzResearch.WordTrace tailWord_7169751 prefixEnd_7169751 3681528436054083049939421 := by
  unfold tailWord_7169751
  simp only [CollatzResearch.WordTrace]
  refine ⟨261502302248224097828805107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174334868165482731885870071 261502302248224097828805107)
  ·
    refine ⟨392253453372336146743207661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261502302248224097828805107 392253453372336146743207661)
    ·
      refine ⟨147095045014626055028702873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392253453372336146743207661 147095045014626055028702873)
      ·
        refine ⟨110321283760969541271527155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147095045014626055028702873 110321283760969541271527155)
        ·
          refine ⟨165481925641454311907290733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110321283760969541271527155 165481925641454311907290733)
          ·
            refine ⟨62055722115545366965234025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165481925641454311907290733 62055722115545366965234025)
            ·
              refine ⟨46541791586659025223925519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62055722115545366965234025 46541791586659025223925519)
              ·
                refine ⟨69812687379988537835888279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46541791586659025223925519 69812687379988537835888279)
                ·
                  refine ⟨104719031069982806753832419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69812687379988537835888279 104719031069982806753832419)
                  ·
                    refine ⟨157078546604974210130748629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104719031069982806753832419 157078546604974210130748629)
                    ·
                      refine ⟨3681528436054083049939421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157078546604974210130748629 3681528436054083049939421)
                      ·
                        rfl

theorem cell23_7169751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_7169751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169751 prefixEnd_7169751 := by exact prefixLift 7169751
  have htrace : WordTrace (prefixWord ++ tailWord_7169751) baseStart_7169751 baseEnd_7169751 := by
    simpa [prefixWord, tailWord_7169751, baseEnd_7169751] using wordTrace_append hprefix tailTrace_7169751
  have hstable : (prefixWord ++ tailWord_7169751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169751).length < 2 ^ (prefixWord ++ tailWord_7169751).sum := by decide
  have hdescent : baseEnd_7169751 < baseStart_7169751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169756 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7169756 : Nat := 118140960795 + 7169756 * 2 ^ 59
def prefixEnd_7169756 : Nat := 4983230072969 + 3 ^ 40 * 7169756 * 2
def baseEnd_7169756 : Nat := 3681531003457355530376899

theorem tailTrace_7169756 : CollatzResearch.WordTrace tailWord_7169756 prefixEnd_7169756 3681531003457355530376899 := by
  unfold tailWord_7169756
  simp only [CollatzResearch.WordTrace]
  refine ⟨130751242306602991841368561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174334989742137322455158081 130751242306602991841368561)
  ·
    refine ⟨98063431729952243881026421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130751242306602991841368561 98063431729952243881026421)
    ·
      refine ⟨9193446724683022863846227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98063431729952243881026421 9193446724683022863846227)
      ·
        refine ⟨13790170087024534295769341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193446724683022863846227 13790170087024534295769341)
        ·
          refine ⟨5171313782634200360913503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13790170087024534295769341 5171313782634200360913503)
          ·
            refine ⟨7756970673951300541370255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171313782634200360913503 7756970673951300541370255)
            ·
              refine ⟨11635456010926950812055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756970673951300541370255 11635456010926950812055383)
              ·
                refine ⟨17453184016390426218083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635456010926950812055383 17453184016390426218083075)
                ·
                  refine ⟨26179776024585639327124613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17453184016390426218083075 26179776024585639327124613)
                  ·
                    refine ⟨4908708004609807373835865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26179776024585639327124613 4908708004609807373835865)
                    ·
                      refine ⟨3681531003457355530376899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908708004609807373835865 3681531003457355530376899)
                      ·
                        rfl

theorem cell23_7169756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7169756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169756 prefixEnd_7169756 := by exact prefixLift 7169756
  have htrace : WordTrace (prefixWord ++ tailWord_7169756) baseStart_7169756 baseEnd_7169756 := by
    simpa [prefixWord, tailWord_7169756, baseEnd_7169756] using wordTrace_append hprefix tailTrace_7169756
  have hstable : (prefixWord ++ tailWord_7169756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169756).length < 2 ^ (prefixWord ++ tailWord_7169756).sum := by decide
  have hdescent : baseEnd_7169756 < baseStart_7169756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169778 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7169778 : Nat := 118140960795 + 7169778 * 2 ^ 59
def prefixEnd_7169778 : Nat := 4983230072969 + 3 ^ 40 * 7169778 * 2
def baseEnd_7169778 : Nat := 3681542300031754444301797

theorem tailTrace_7169778 : CollatzResearch.WordTrace tailWord_7169778 prefixEnd_7169778 3681542300031754444301797 := by
  unfold tailWord_7169778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65375821754781570360009497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174335524679417520960025325 65375821754781570360009497)
  ·
    refine ⟨49031866316086177770007123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65375821754781570360009497 49031866316086177770007123)
    ·
      refine ⟨73547799474129266655010685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49031866316086177770007123 73547799474129266655010685)
      ·
        refine ⟨27580424802798474995629007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73547799474129266655010685 27580424802798474995629007)
        ·
          refine ⟨41370637204197712493443511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27580424802798474995629007 41370637204197712493443511)
          ·
            refine ⟨62055955806296568740165267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41370637204197712493443511 62055955806296568740165267)
            ·
              refine ⟨93083933709444853110247901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62055955806296568740165267 93083933709444853110247901)
              ·
                refine ⟨34906475141041819916342963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93083933709444853110247901 34906475141041819916342963)
                ·
                  refine ⟨52359712711562729874514445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34906475141041819916342963 52359712711562729874514445)
                  ·
                    refine ⟨19634892266836023702942917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52359712711562729874514445 19634892266836023702942917)
                    ·
                      refine ⟨3681542300031754444301797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19634892266836023702942917 3681542300031754444301797)
                      ·
                        rfl

theorem cell23_7169778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7169778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169778 prefixEnd_7169778 := by exact prefixLift 7169778
  have htrace : WordTrace (prefixWord ++ tailWord_7169778) baseStart_7169778 baseEnd_7169778 := by
    simpa [prefixWord, tailWord_7169778, baseEnd_7169778] using wordTrace_append hprefix tailTrace_7169778
  have hstable : (prefixWord ++ tailWord_7169778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169778).length < 2 ^ (prefixWord ++ tailWord_7169778).sum := by decide
  have hdescent : baseEnd_7169778 < baseStart_7169778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169791 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_7169791 : Nat := 118140960795 + 7169791 * 2 ^ 59
def prefixEnd_7169791 : Nat := 4983230072969 + 3 ^ 40 * 7169791 * 2
def baseEnd_7169791 : Nat := 3681548975280262893439237

theorem tailTrace_7169791 : CollatzResearch.WordTrace tailWord_7169791 prefixEnd_7169791 3681548975280262893439237 := by
  unfold tailWord_7169791
  simp only [CollatzResearch.WordTrace]
  refine ⟨261503761168079184660261227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174335840778719456440174151 261503761168079184660261227)
  ·
    refine ⟨392255641752118776990391841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261503761168079184660261227 392255641752118776990391841)
    ·
      refine ⟨294191731314089082742793881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392255641752118776990391841 294191731314089082742793881)
      ·
        refine ⟨220643798485566812057095411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294191731314089082742793881 220643798485566812057095411)
        ·
          refine ⟨330965697728350218085643117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220643798485566812057095411 330965697728350218085643117)
          ·
            refine ⟨124112136648131331782116169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330965697728350218085643117 124112136648131331782116169)
            ·
              refine ⟨93084102486098498836587127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124112136648131331782116169 93084102486098498836587127)
              ·
                refine ⟨139626153729147748254880691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93084102486098498836587127 139626153729147748254880691)
                ·
                  refine ⟨209439230593721622382321037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139626153729147748254880691 209439230593721622382321037)
                  ·
                    refine ⟨78539711472645608393370389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209439230593721622382321037 78539711472645608393370389)
                    ·
                      refine ⟨3681548975280262893439237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78539711472645608393370389 3681548975280262893439237)
                      ·
                        rfl

theorem cell23_7169791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_7169791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169791 prefixEnd_7169791 := by exact prefixLift 7169791
  have htrace : WordTrace (prefixWord ++ tailWord_7169791) baseStart_7169791 baseEnd_7169791 := by
    simpa [prefixWord, tailWord_7169791, baseEnd_7169791] using wordTrace_append hprefix tailTrace_7169791
  have hstable : (prefixWord ++ tailWord_7169791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169791).length < 2 ^ (prefixWord ++ tailWord_7169791).sum := by decide
  have hdescent : baseEnd_7169791 < baseStart_7169791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169832 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7169832 : Nat := 118140960795 + 7169832 * 2 ^ 59
def prefixEnd_7169832 : Nat := 4983230072969 + 3 ^ 40 * 7169832 * 2
def baseEnd_7169832 : Nat := 3681570027987097233026549

theorem tailTrace_7169832 : CollatzResearch.WordTrace tailWord_7169832 prefixEnd_7169832 3681570027987097233026549 := by
  unfold tailWord_7169832
  simp only [CollatzResearch.WordTrace]
  refine ⟨130752628280465324331251875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174336837707287099108335833 130752628280465324331251875)
  ·
    refine ⟨196128942420697986496877813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130752628280465324331251875 196128942420697986496877813)
    ·
      refine ⟨18387088351940436234082295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196128942420697986496877813 18387088351940436234082295)
      ·
        refine ⟨27580632527910654351123443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387088351940436234082295 27580632527910654351123443)
        ·
          refine ⟨41370948791865981526685165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27580632527910654351123443 41370948791865981526685165)
          ·
            refine ⟨15514105796949743072506937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41370948791865981526685165 15514105796949743072506937)
            ·
              refine ⟨11635579347712307304380203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15514105796949743072506937 11635579347712307304380203)
              ·
                refine ⟨17453369021568460956570305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635579347712307304380203 17453369021568460956570305)
                ·
                  refine ⟨13090026766176345717427729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17453369021568460956570305 13090026766176345717427729)
                  ·
                    refine ⟨9817520074632259288070797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13090026766176345717427729 9817520074632259288070797)
                    ·
                      refine ⟨3681570027987097233026549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9817520074632259288070797 3681570027987097233026549)
                      ·
                        rfl

theorem cell23_7169832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7169832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169832 prefixEnd_7169832 := by exact prefixLift 7169832
  have htrace : WordTrace (prefixWord ++ tailWord_7169832) baseStart_7169832 baseEnd_7169832 := by
    simpa [prefixWord, tailWord_7169832, baseEnd_7169832] using wordTrace_append hprefix tailTrace_7169832
  have hstable : (prefixWord ++ tailWord_7169832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169832).length < 2 ^ (prefixWord ++ tailWord_7169832).sum := by decide
  have hdescent : baseEnd_7169832 < baseStart_7169832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169895 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 4, 4]
def baseStart_7169895 : Nat := 118140960795 + 7169895 * 2 ^ 59
def prefixEnd_7169895 : Nat := 4983230072969 + 3 ^ 40 * 7169895 * 2
def baseEnd_7169895 : Nat := 1227200792422776828846253

theorem tailTrace_7169895 : CollatzResearch.WordTrace tailWord_7169895 prefixEnd_7169895 1227200792422776828846253 := by
  unfold tailWord_7169895
  simp only [CollatzResearch.WordTrace]
  refine ⟨261507554359702410422047139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174338369573134940281364759 261507554359702410422047139)
  ·
    refine ⟨392261331539553615633070709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261507554359702410422047139 392261331539553615633070709)
    ·
      refine ⟨36774499831833151465600379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392261331539553615633070709 36774499831833151465600379)
      ·
        refine ⟨55161749747749727198400569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36774499831833151465600379 55161749747749727198400569)
        ·
          refine ⟨41371312310812295398800427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55161749747749727198400569 41371312310812295398800427)
          ·
            refine ⟨62056968466218443098200641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41371312310812295398800427 62056968466218443098200641)
            ·
              refine ⟨46542726349663832323650481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62056968466218443098200641 46542726349663832323650481)
              ·
                refine ⟨34907044762247874242737861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46542726349663832323650481 34907044762247874242737861)
                ·
                  refine ⟨6545070892921476420513349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34907044762247874242737861 6545070892921476420513349)
                  ·
                    refine ⟨1227200792422776828846253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545070892921476420513349 1227200792422776828846253)
                    ·
                      rfl

theorem cell23_7169895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_7169895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169895 prefixEnd_7169895 := by exact prefixLift 7169895
  have htrace : WordTrace (prefixWord ++ tailWord_7169895) baseStart_7169895 baseEnd_7169895 := by
    simpa [prefixWord, tailWord_7169895, baseEnd_7169895] using wordTrace_append hprefix tailTrace_7169895
  have hstable : (prefixWord ++ tailWord_7169895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169895).length < 2 ^ (prefixWord ++ tailWord_7169895).sum := by decide
  have hdescent : baseEnd_7169895 < baseStart_7169895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7169996 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7169996 : Nat := 118140960795 + 7169996 * 2 ^ 59
def prefixEnd_7169996 : Nat := 4983230072969 + 3 ^ 40 * 7169996 * 2
def baseEnd_7169996 : Nat := 3681654238814434591375795

theorem tailTrace_7169996 : CollatzResearch.WordTrace tailWord_7169996 prefixEnd_7169996 3681654238814434591375795 := by
  unfold tailWord_7169996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130755619066168252335736921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174340825421557669780982561 130755619066168252335736921)
  ·
    refine ⟨98066714299626189251802691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130755619066168252335736921 98066714299626189251802691)
    ·
      refine ⟨147100071449439283877704037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98066714299626189251802691 147100071449439283877704037)
      ·
        refine ⟨27581263396769865727069507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147100071449439283877704037 27581263396769865727069507)
        ·
          refine ⟨41371895095154798590604261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581263396769865727069507 41371895095154798590604261)
          ·
            refine ⟨7757230330341524735738299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41371895095154798590604261 7757230330341524735738299)
            ·
              refine ⟨11635845495512287103607449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757230330341524735738299 11635845495512287103607449)
              ·
                refine ⟨8726884121634215327705587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11635845495512287103607449 8726884121634215327705587)
                ·
                  refine ⟨13090326182451322991558381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8726884121634215327705587 13090326182451322991558381)
                  ·
                    refine ⟨4908872318419246121834393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13090326182451322991558381 4908872318419246121834393)
                    ·
                      refine ⟨3681654238814434591375795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908872318419246121834393 3681654238814434591375795)
                      ·
                        rfl

theorem cell23_7169996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7169996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7169996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7169996 prefixEnd_7169996 := by exact prefixLift 7169996
  have htrace : WordTrace (prefixWord ++ tailWord_7169996) baseStart_7169996 baseEnd_7169996 := by
    simpa [prefixWord, tailWord_7169996, baseEnd_7169996] using wordTrace_append hprefix tailTrace_7169996
  have hstable : (prefixWord ++ tailWord_7169996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7169996).length < 2 ^ (prefixWord ++ tailWord_7169996).sum := by decide
  have hdescent : baseEnd_7169996 < baseStart_7169996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7169996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170009 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 4, 2]
def baseStart_7170009 : Nat := 118140960795 + 7170009 * 2 ^ 59
def prefixEnd_7170009 : Nat := 4983230072969 + 3 ^ 40 * 7170009 * 2
def baseEnd_7170009 : Nat := 3681660914062943040513235

theorem tailTrace_7170009 : CollatzResearch.WordTrace tailWord_7170009 prefixEnd_7170009 3681660914062943040513235 := by
  unfold tailWord_7170009
  simp only [CollatzResearch.WordTrace]
  refine ⟨261511712281289407891697081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174341141520859605261131387 261511712281289407891697081)
  ·
    refine ⟨196133784210967055918772811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261511712281289407891697081 196133784210967055918772811)
    ·
      refine ⟨294200676316450583878159217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196133784210967055918772811 294200676316450583878159217)
      ·
        refine ⟨220650507237337937908619413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294200676316450583878159217 220650507237337937908619413)
        ·
          refine ⟨10342992526750215839466535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220650507237337937908619413 10342992526750215839466535)
          ·
            refine ⟨15514488790125323759199803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342992526750215839466535 15514488790125323759199803)
            ·
              refine ⟨23271733185187985638799705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15514488790125323759199803 23271733185187985638799705)
              ·
                refine ⟨17453799888890989229099779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23271733185187985638799705 17453799888890989229099779)
                ·
                  refine ⟨26180699833336483843649669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17453799888890989229099779 26180699833336483843649669)
                  ·
                    refine ⟨4908881218750590720684313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26180699833336483843649669 4908881218750590720684313)
                    ·
                      refine ⟨3681660914062943040513235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908881218750590720684313 3681660914062943040513235)
                      ·
                        rfl

theorem cell23_7170009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_7170009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170009 prefixEnd_7170009 := by exact prefixLift 7170009
  have htrace : WordTrace (prefixWord ++ tailWord_7170009) baseStart_7170009 baseEnd_7170009 := by
    simpa [prefixWord, tailWord_7170009, baseEnd_7170009] using wordTrace_append hprefix tailTrace_7170009
  have hstable : (prefixWord ++ tailWord_7170009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170009).length < 2 ^ (prefixWord ++ tailWord_7170009).sum := by decide
  have hdescent : baseEnd_7170009 < baseStart_7170009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170013 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_7170013 : Nat := 118140960795 + 7170013 * 2 ^ 59
def prefixEnd_7170013 : Nat := 4983230072969 + 3 ^ 40 * 7170013 * 2
def baseEnd_7170013 : Nat := 3681662967985561024863217

theorem tailTrace_7170013 : CollatzResearch.WordTrace tailWord_7170013 prefixEnd_7170013 3681662967985561024863217 := by
  unfold tailWord_7170013
  simp only [CollatzResearch.WordTrace]
  refine ⟨261511858173274916574842693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174341238782183277716561795 261511858173274916574842693)
  ·
    refine ⟨49033473407489046857783005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261511858173274916574842693 49033473407489046857783005)
    ·
      refine ⟨18387552527808392571668627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49033473407489046857783005 18387552527808392571668627)
      ·
        refine ⟨27581328791712588857502941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387552527808392571668627 27581328791712588857502941)
        ·
          refine ⟨10342998296892220821563603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27581328791712588857502941 10342998296892220821563603)
          ·
            refine ⟨15514497445338331232345405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342998296892220821563603 15514497445338331232345405)
            ·
              refine ⟨5817936542001874212129527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15514497445338331232345405 5817936542001874212129527)
              ·
                refine ⟨8726904813002811318194291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817936542001874212129527 8726904813002811318194291)
                ·
                  refine ⟨13090357219504216977291437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8726904813002811318194291 13090357219504216977291437)
                  ·
                    refine ⟨4908883957314081366484289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13090357219504216977291437 4908883957314081366484289)
                    ·
                      refine ⟨3681662967985561024863217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908883957314081366484289 3681662967985561024863217)
                      ·
                        rfl

theorem cell23_7170013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_7170013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170013 prefixEnd_7170013 := by exact prefixLift 7170013
  have htrace : WordTrace (prefixWord ++ tailWord_7170013) baseStart_7170013 baseEnd_7170013 := by
    simpa [prefixWord, tailWord_7170013, baseEnd_7170013] using wordTrace_append hprefix tailTrace_7170013
  have hstable : (prefixWord ++ tailWord_7170013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170013).length < 2 ^ (prefixWord ++ tailWord_7170013).sum := by decide
  have hdescent : baseEnd_7170013 < baseStart_7170013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170026 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_7170026 : Nat := 118140960795 + 7170026 * 2 ^ 59
def prefixEnd_7170026 : Nat := 4983230072969 + 3 ^ 40 * 7170026 * 2
def baseEnd_7170026 : Nat := 3681669643234069474000657

theorem tailTrace_7170026 : CollatzResearch.WordTrace tailWord_7170026 prefixEnd_7170026 3681669643234069474000657 := by
  unfold tailWord_7170026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378083080556954948766483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174341554881485213196710621 65378083080556954948766483)
  ·
    refine ⟨98067124620835432423149725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65378083080556954948766483 98067124620835432423149725)
    ·
      refine ⟨36775171732813287158681147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98067124620835432423149725 36775171732813287158681147)
      ·
        refine ⟨55162757599219930738021721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36775171732813287158681147 55162757599219930738021721)
        ·
          refine ⟨41372068199414948053516291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55162757599219930738021721 41372068199414948053516291)
          ·
            refine ⟨62058102299122422080274437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41372068199414948053516291 62058102299122422080274437)
            ·
              refine ⟨11635894181085454140051457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62058102299122422080274437 11635894181085454140051457)
              ·
                refine ⟨8726920635814090605038593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11635894181085454140051457 8726920635814090605038593)
                ·
                  refine ⟨6545190476860567953778945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8726920635814090605038593 6545190476860567953778945)
                  ·
                    refine ⟨4908892857645425965334209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545190476860567953778945 4908892857645425965334209)
                    ·
                      refine ⟨3681669643234069474000657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4908892857645425965334209 3681669643234069474000657)
                      ·
                        rfl

theorem cell23_7170026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_7170026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170026 prefixEnd_7170026 := by exact prefixLift 7170026
  have htrace : WordTrace (prefixWord ++ tailWord_7170026) baseStart_7170026 baseEnd_7170026 := by
    simpa [prefixWord, tailWord_7170026, baseEnd_7170026] using wordTrace_append hprefix tailTrace_7170026
  have hstable : (prefixWord ++ tailWord_7170026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170026).length < 2 ^ (prefixWord ++ tailWord_7170026).sum := by decide
  have hdescent : baseEnd_7170026 < baseStart_7170026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170045 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_7170045 : Nat := 118140960795 + 7170045 * 2 ^ 59
def prefixEnd_7170045 : Nat := 4983230072969 + 3 ^ 40 * 7170045 * 2
def baseEnd_7170045 : Nat := 1227226466455501633221023

theorem tailTrace_7170045 : CollatzResearch.WordTrace tailWord_7170045 prefixEnd_7170045 1227226466455501633221023 := by
  unfold tailWord_7170045
  simp only [CollatzResearch.WordTrace]
  refine ⟨261513025309158986040007589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174342016872772657360005059 261513025309158986040007589)
  ·
    refine ⟨49033692245467309882501423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261513025309158986040007589 49033692245467309882501423)
    ·
      refine ⟨73550538368200964823752135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49033692245467309882501423 73550538368200964823752135)
      ·
        refine ⟨110325807552301447235628203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73550538368200964823752135 110325807552301447235628203)
        ·
          refine ⟨165488711328452170853442305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110325807552301447235628203 165488711328452170853442305)
          ·
            refine ⟨124116533496339128140081729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165488711328452170853442305 124116533496339128140081729)
            ·
              refine ⟨93087400122254346105061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124116533496339128140081729 93087400122254346105061297)
              ·
                refine ⟨69815550091690759578795973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93087400122254346105061297 69815550091690759578795973)
                ·
                  refine ⟨13090415642192017421024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69815550091690759578795973 13090415642192017421024245)
                  ·
                    refine ⟨1227226466455501633221023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13090415642192017421024245 1227226466455501633221023)
                    ·
                      rfl

theorem cell23_7170045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_7170045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170045 prefixEnd_7170045 := by exact prefixLift 7170045
  have htrace : WordTrace (prefixWord ++ tailWord_7170045) baseStart_7170045 baseEnd_7170045 := by
    simpa [prefixWord, tailWord_7170045, baseEnd_7170045] using wordTrace_append hprefix tailTrace_7170045
  have hstable : (prefixWord ++ tailWord_7170045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170045).length < 2 ^ (prefixWord ++ tailWord_7170045).sum := by decide
  have hdescent : baseEnd_7170045 < baseStart_7170045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170082 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7170082 : Nat := 118140960795 + 7170082 * 2 ^ 59
def prefixEnd_7170082 : Nat := 4983230072969 + 3 ^ 40 * 7170082 * 2
def baseEnd_7170082 : Nat := 3681698398150721254900399

theorem tailTrace_7170082 : CollatzResearch.WordTrace tailWord_7170082 prefixEnd_7170082 3681698398150721254900399 := by
  unfold tailWord_7170082
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378593702506235339776125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174342916540016627572736333 65378593702506235339776125)
  ·
    refine ⟨24516972638439838252416047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65378593702506235339776125 24516972638439838252416047)
    ·
      refine ⟨36775458957659757378624071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24516972638439838252416047 36775458957659757378624071)
      ·
        refine ⟨55163188436489636067936107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36775458957659757378624071 55163188436489636067936107)
        ·
          refine ⟨82744782654734454101904161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55163188436489636067936107 82744782654734454101904161)
          ·
            refine ⟨62058586991050840576428121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82744782654734454101904161 62058586991050840576428121)
            ·
              refine ⟨46543940243288130432321091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62058586991050840576428121 46543940243288130432321091)
              ·
                refine ⟨69815910364932195648481637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46543940243288130432321091 69815910364932195648481637)
                ·
                  refine ⟨13090483193424786684090307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69815910364932195648481637 13090483193424786684090307)
                  ·
                    refine ⟨19635724790137180026135461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13090483193424786684090307 19635724790137180026135461)
                    ·
                      refine ⟨3681698398150721254900399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19635724790137180026135461 3681698398150721254900399)
                      ·
                        rfl

theorem cell23_7170082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7170082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170082 prefixEnd_7170082 := by exact prefixLift 7170082
  have htrace : WordTrace (prefixWord ++ tailWord_7170082) baseStart_7170082 baseEnd_7170082 := by
    simpa [prefixWord, tailWord_7170082, baseEnd_7170082] using wordTrace_append hprefix tailTrace_7170082
  have hstable : (prefixWord ++ tailWord_7170082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170082).length < 2 ^ (prefixWord ++ tailWord_7170082).sum := by decide
  have hdescent : baseEnd_7170082 < baseStart_7170082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170126 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_7170126 : Nat := 118140960795 + 7170126 * 2 ^ 59
def prefixEnd_7170126 : Nat := 4983230072969 + 3 ^ 40 * 7170126 * 2
def baseEnd_7170126 : Nat := 1227240330433173027583399

theorem tailTrace_7170126 : CollatzResearch.WordTrace tailWord_7170126 prefixEnd_7170126 1227240330433173027583399 := by
  unfold tailWord_7170126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689497452733192109213279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174343986414577024582470821 32689497452733192109213279)
  ·
    refine ⟨49034246179099788163819919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32689497452733192109213279 49034246179099788163819919)
    ·
      refine ⟨73551369268649682245729879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49034246179099788163819919 73551369268649682245729879)
      ·
        refine ⟨110327053902974523368594819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73551369268649682245729879 110327053902974523368594819)
        ·
          refine ⟨165490580854461785052892229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110327053902974523368594819 165490580854461785052892229)
          ·
            refine ⟨31029483910211584697417293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165490580854461785052892229 31029483910211584697417293)
            ·
              refine ⟨11636056466329344261531485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31029483910211584697417293 11636056466329344261531485)
              ·
                refine ⟨4363521174873504098074307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11636056466329344261531485 4363521174873504098074307)
                ·
                  refine ⟨6545281762310256147111461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363521174873504098074307 6545281762310256147111461)
                  ·
                    refine ⟨1227240330433173027583399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545281762310256147111461 1227240330433173027583399)
                    ·
                      rfl

theorem cell23_7170126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_7170126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170126 prefixEnd_7170126 := by exact prefixLift 7170126
  have htrace : WordTrace (prefixWord ++ tailWord_7170126) baseStart_7170126 baseEnd_7170126 := by
    simpa [prefixWord, tailWord_7170126, baseEnd_7170126] using wordTrace_append hprefix tailTrace_7170126
  have hstable : (prefixWord ++ tailWord_7170126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170126).length < 2 ^ (prefixWord ++ tailWord_7170126).sum := by decide
  have hdescent : baseEnd_7170126 < baseStart_7170126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170145 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7170145 : Nat := 118140960795 + 7170145 * 2 ^ 59
def prefixEnd_7170145 : Nat := 4983230072969 + 3 ^ 40 * 7170145 * 2
def baseEnd_7170145 : Nat := 3681730747431954508412609

theorem tailTrace_7170145 : CollatzResearch.WordTrace tailWord_7170145 prefixEnd_7170145 3681730747431954508412609 := by
  unfold tailWord_7170145
  simp only [CollatzResearch.WordTrace]
  refine ⟨261516672608796703118647889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174344448405864468745765259 261516672608796703118647889)
  ·
    refine ⟨196137504456597527338985917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261516672608796703118647889 196137504456597527338985917)
    ·
      refine ⟨73551564171224072752119719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196137504456597527338985917 73551564171224072752119719)
      ·
        refine ⟨110327346256836109128179579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73551564171224072752119719 110327346256836109128179579)
        ·
          refine ⟨165491019385254163692269369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110327346256836109128179579 165491019385254163692269369)
          ·
            refine ⟨124118264538940622769202027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165491019385254163692269369 124118264538940622769202027)
            ·
              refine ⟨186177396808410934153803041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124118264538940622769202027 186177396808410934153803041)
              ·
                refine ⟨139633047606308200615352281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186177396808410934153803041 139633047606308200615352281)
                ·
                  refine ⟨104724785704731150461514211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139633047606308200615352281 104724785704731150461514211)
                  ·
                    refine ⟨157087178557096725692271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104724785704731150461514211 157087178557096725692271317)
                    ·
                      refine ⟨3681730747431954508412609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157087178557096725692271317 3681730747431954508412609)
                      ·
                        rfl

theorem cell23_7170145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7170145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170145 prefixEnd_7170145 := by exact prefixLift 7170145
  have htrace : WordTrace (prefixWord ++ tailWord_7170145) baseStart_7170145 baseEnd_7170145 := by
    simpa [prefixWord, tailWord_7170145, baseEnd_7170145] using wordTrace_append hprefix tailTrace_7170145
  have hstable : (prefixWord ++ tailWord_7170145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170145).length < 2 ^ (prefixWord ++ tailWord_7170145).sum := by decide
  have hdescent : baseEnd_7170145 < baseStart_7170145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170169 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_7170169 : Nat := 118140960795 + 7170169 * 2 ^ 59
def prefixEnd_7170169 : Nat := 4983230072969 + 3 ^ 40 * 7170169 * 2
def baseEnd_7170169 : Nat := 1227247690322554138170833

theorem tailTrace_7170169 : CollatzResearch.WordTrace tailWord_7170169 prefixEnd_7170169 1227247690322554138170833 := by
  unfold tailWord_7170169
  simp only [CollatzResearch.WordTrace]
  refine ⟨261517547960709755217521561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174345031973806503478347707 261517547960709755217521561)
  ·
    refine ⟨196138160970532316413141171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261517547960709755217521561 196138160970532316413141171)
    ·
      refine ⟨294207241455798474619711757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196138160970532316413141171 294207241455798474619711757)
      ·
        refine ⟨110327715545924427982391909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294207241455798474619711757 110327715545924427982391909)
        ·
          refine ⟨20686446664860830246698483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110327715545924427982391909 20686446664860830246698483)
          ·
            refine ⟨31029669997291245370047725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20686446664860830246698483 31029669997291245370047725)
            ·
              refine ⟨11636126248984217013767897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31029669997291245370047725 11636126248984217013767897)
              ·
                refine ⟨8727094686738162760325923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11636126248984217013767897 8727094686738162760325923)
                ·
                  refine ⟨13090642030107244140488885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727094686738162760325923 13090642030107244140488885)
                  ·
                    refine ⟨1227247690322554138170833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13090642030107244140488885 1227247690322554138170833)
                    ·
                      rfl

theorem cell23_7170169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_7170169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170169 prefixEnd_7170169 := by exact prefixLift 7170169
  have htrace : WordTrace (prefixWord ++ tailWord_7170169) baseStart_7170169 baseEnd_7170169 := by
    simpa [prefixWord, tailWord_7170169, baseEnd_7170169] using wordTrace_append hprefix tailTrace_7170169
  have hstable : (prefixWord ++ tailWord_7170169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170169).length < 2 ^ (prefixWord ++ tailWord_7170169).sum := by decide
  have hdescent : baseEnd_7170169 < baseStart_7170169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170175 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_7170175 : Nat := 118140960795 + 7170175 * 2 ^ 59
def prefixEnd_7170175 : Nat := 4983230072969 + 3 ^ 40 * 7170175 * 2
def baseEnd_7170175 : Nat := 3681746151851589391037471

theorem tailTrace_7170175 : CollatzResearch.WordTrace tailWord_7170175 prefixEnd_7170175 3681746151851589391037471 := by
  unfold tailWord_7170175
  simp only [CollatzResearch.WordTrace]
  refine ⟨261517766798688018242239979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174345177865792012161493319 261517766798688018242239979)
  ·
    refine ⟨392276650198032027363359969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261517766798688018242239979 392276650198032027363359969)
    ·
      refine ⟨294207487648524020522519977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392276650198032027363359969 294207487648524020522519977)
      ·
        refine ⟨220655615736393015391889983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294207487648524020522519977 220655615736393015391889983)
        ·
          refine ⟨330983423604589523087834975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220655615736393015391889983 330983423604589523087834975)
          ·
            refine ⟨496475135406884284631752463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330983423604589523087834975 496475135406884284631752463)
            ·
              refine ⟨744712703110326426947628695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496475135406884284631752463 744712703110326426947628695)
              ·
                refine ⟨1117069054665489640421443043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744712703110326426947628695 1117069054665489640421443043)
                ·
                  refine ⟨1675603581998234460632164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117069054665489640421443043 1675603581998234460632164565)
                  ·
                    refine ⟨39271958953083620171066357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1675603581998234460632164565 39271958953083620171066357)
                    ·
                      refine ⟨3681746151851589391037471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39271958953083620171066357 3681746151851589391037471)
                      ·
                        rfl

theorem cell23_7170175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_7170175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170175 prefixEnd_7170175 := by exact prefixLift 7170175
  have htrace : WordTrace (prefixWord ++ tailWord_7170175) baseStart_7170175 baseEnd_7170175 := by
    simpa [prefixWord, tailWord_7170175, baseEnd_7170175] using wordTrace_append hprefix tailTrace_7170175
  have hstable : (prefixWord ++ tailWord_7170175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170175).length < 2 ^ (prefixWord ++ tailWord_7170175).sum := by decide
  have hdescent : baseEnd_7170175 < baseStart_7170175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170186 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_7170186 : Nat := 118140960795 + 7170186 * 2 ^ 59
def prefixEnd_7170186 : Nat := 4983230072969 + 3 ^ 40 * 7170186 * 2
def baseEnd_7170186 : Nat := 1227250600046262949333307

theorem tailTrace_7170186 : CollatzResearch.WordTrace tailWord_7170186 prefixEnd_7170186 1227250600046262949333307 := by
  unfold tailWord_7170186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65379542000412041780222603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174345445334432111413926941 65379542000412041780222603)
  ·
    refine ⟨98069313000618062670333905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65379542000412041780222603 98069313000618062670333905)
    ·
      refine ⟨73551984750463547002750429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98069313000618062670333905 73551984750463547002750429)
      ·
        refine ⟨27581994281423830126031411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73551984750463547002750429 27581994281423830126031411)
        ·
          refine ⟨41372991422135745189047117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581994281423830126031411 41372991422135745189047117)
          ·
            refine ⟨15514871783300904445892669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41372991422135745189047117 15514871783300904445892669)
            ·
              refine ⟨5818076918737839167209751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15514871783300904445892669 5818076918737839167209751)
              ·
                refine ⟨8727115378106758750814627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818076918737839167209751 8727115378106758750814627)
                ·
                  refine ⟨13090673067160138126221941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727115378106758750814627 13090673067160138126221941)
                  ·
                    refine ⟨1227250600046262949333307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13090673067160138126221941 1227250600046262949333307)
                    ·
                      rfl

theorem cell23_7170186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_7170186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170186 prefixEnd_7170186 := by exact prefixLift 7170186
  have htrace : WordTrace (prefixWord ++ tailWord_7170186) baseStart_7170186 baseEnd_7170186 := by
    simpa [prefixWord, tailWord_7170186, baseEnd_7170186] using wordTrace_append hprefix tailTrace_7170186
  have hstable : (prefixWord ++ tailWord_7170186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170186).length < 2 ^ (prefixWord ++ tailWord_7170186).sum := by decide
  have hdescent : baseEnd_7170186 < baseStart_7170186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170209 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7170209 : Nat := 118140960795 + 7170209 * 2 ^ 59
def prefixEnd_7170209 : Nat := 4983230072969 + 3 ^ 40 * 7170209 * 2
def baseEnd_7170209 : Nat := 3681763610193842258012315

theorem tailTrace_7170209 : CollatzResearch.WordTrace tailWord_7170209 prefixEnd_7170209 3681763610193842258012315 := by
  unfold tailWord_7170209
  simp only [CollatzResearch.WordTrace]
  refine ⟨261519006880564842048977681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174346004587043228032651787 261519006880564842048977681)
  ·
    refine ⟨196139255160423631536733261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261519006880564842048977681 196139255160423631536733261)
    ·
      refine ⟨73552220685158861826274973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196139255160423631536733261 73552220685158861826274973)
      ·
        refine ⟨27582082756934573184853115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73552220685158861826274973 27582082756934573184853115)
        ·
          refine ⟨41373124135401859777279673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582082756934573184853115 41373124135401859777279673)
          ·
            refine ⟨31029843101551394832959755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41373124135401859777279673 31029843101551394832959755)
            ·
              refine ⟨46544764652327092249439633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31029843101551394832959755 46544764652327092249439633)
              ·
                refine ⟨34908573489245319187079725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46544764652327092249439633 34908573489245319187079725)
                ·
                  refine ⟨13090715058466994695154897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34908573489245319187079725 13090715058466994695154897)
                  ·
                    refine ⟨9818036293850246021366173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13090715058466994695154897 9818036293850246021366173)
                    ·
                      refine ⟨3681763610193842258012315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9818036293850246021366173 3681763610193842258012315)
                      ·
                        rfl

theorem cell23_7170209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7170209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170209 prefixEnd_7170209 := by exact prefixLift 7170209
  have htrace : WordTrace (prefixWord ++ tailWord_7170209) baseStart_7170209 baseEnd_7170209 := by
    simpa [prefixWord, tailWord_7170209, baseEnd_7170209] using wordTrace_append hprefix tailTrace_7170209
  have hstable : (prefixWord ++ tailWord_7170209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170209).length < 2 ^ (prefixWord ++ tailWord_7170209).sum := by decide
  have hdescent : baseEnd_7170209 < baseStart_7170209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170239 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_7170239 : Nat := 118140960795 + 7170239 * 2 ^ 59
def prefixEnd_7170239 : Nat := 4983230072969 + 3 ^ 40 * 7170239 * 2
def baseEnd_7170239 : Nat := 3681779014613477140637177

theorem tailTrace_7170239 : CollatzResearch.WordTrace tailWord_7170239 prefixEnd_7170239 3681779014613477140637177 := by
  unfold tailWord_7170239
  simp only [CollatzResearch.WordTrace]
  refine ⟨261520101070456157172569771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174346734046970771448379847 261520101070456157172569771)
  ·
    refine ⟨392280151605684235758854657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261520101070456157172569771 392280151605684235758854657)
    ·
      refine ⟨294210113704263176819140993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392280151605684235758854657 294210113704263176819140993)
      ·
        refine ⟨220657585278197382614355745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294210113704263176819140993 220657585278197382614355745)
        ·
          refine ⟨165493188958648036960766809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220657585278197382614355745 165493188958648036960766809)
          ·
            refine ⟨124119891718986027720575107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165493188958648036960766809 124119891718986027720575107)
            ·
              refine ⟨186179837578479041580862661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124119891718986027720575107 186179837578479041580862661)
              ·
                refine ⟨34908719545964820296411749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186179837578479041580862661 34908719545964820296411749)
                ·
                  refine ⟨6545384914868403805577203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34908719545964820296411749 6545384914868403805577203)
                  ·
                    refine ⟨9818077372302605708365805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6545384914868403805577203 9818077372302605708365805)
                    ·
                      refine ⟨3681779014613477140637177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9818077372302605708365805 3681779014613477140637177)
                      ·
                        rfl

theorem cell23_7170239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_7170239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170239 prefixEnd_7170239 := by exact prefixLift 7170239
  have htrace : WordTrace (prefixWord ++ tailWord_7170239) baseStart_7170239 baseEnd_7170239 := by
    simpa [prefixWord, tailWord_7170239, baseEnd_7170239] using wordTrace_append hprefix tailTrace_7170239
  have hstable : (prefixWord ++ tailWord_7170239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170239).length < 2 ^ (prefixWord ++ tailWord_7170239).sum := by decide
  have hdescent : baseEnd_7170239 < baseStart_7170239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170240 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 1, 2, 2]
def baseStart_7170240 : Nat := 118140960795 + 7170240 * 2 ^ 59
def prefixEnd_7170240 : Nat := 4983230072969 + 3 ^ 40 * 7170240 * 2
def baseEnd_7170240 : Nat := 3681779528094131636724673

theorem tailTrace_7170240 : CollatzResearch.WordTrace tailWord_7170240 prefixEnd_7170240 3681779528094131636724673 := by
  unfold tailWord_7170240
  simp only [CollatzResearch.WordTrace]
  refine ⟨130760068771726267171678087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174346758362301689562237449 130760068771726267171678087)
  ·
    refine ⟨196140103157589400757517131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130760068771726267171678087 196140103157589400757517131)
    ·
      refine ⟨294210154736384101136275697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196140103157589400757517131 294210154736384101136275697)
      ·
        refine ⟨220657616052288075852206773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294210154736384101136275697 220657616052288075852206773)
        ·
          refine ⟨20686651504902007111144385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220657616052288075852206773 20686651504902007111144385)
          ·
            refine ⟨15514988628676505333358289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20686651504902007111144385 15514988628676505333358289)
            ·
              refine ⟨11636241471507379000018717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15514988628676505333358289 11636241471507379000018717)
              ·
                refine ⟨4363590551815267125007019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11636241471507379000018717 4363590551815267125007019)
                ·
                  refine ⟨6545385827722900687510529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363590551815267125007019 6545385827722900687510529)
                  ·
                    refine ⟨4909039370792175515632897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545385827722900687510529 4909039370792175515632897)
                    ·
                      refine ⟨3681779528094131636724673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909039370792175515632897 3681779528094131636724673)
                      ·
                        rfl

theorem cell23_7170240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_7170240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170240 prefixEnd_7170240 := by exact prefixLift 7170240
  have htrace : WordTrace (prefixWord ++ tailWord_7170240) baseStart_7170240 baseEnd_7170240 := by
    simpa [prefixWord, tailWord_7170240, baseEnd_7170240] using wordTrace_append hprefix tailTrace_7170240
  have hstable : (prefixWord ++ tailWord_7170240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170240).length < 2 ^ (prefixWord ++ tailWord_7170240).sum := by decide
  have hdescent : baseEnd_7170240 < baseStart_7170240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 5, 3, 2]
def baseStart_7170249 : Nat := 118140960795 + 7170249 * 2 ^ 59
def prefixEnd_7170249 : Nat := 4983230072969 + 3 ^ 40 * 7170249 * 2
def baseEnd_7170249 : Nat := 3681784149420022101512131

theorem tailTrace_7170249 : CollatzResearch.WordTrace tailWord_7170249 prefixEnd_7170249 3681784149420022101512131 := by
  unfold tailWord_7170249
  simp only [CollatzResearch.WordTrace]
  refine ⟨261520465800419928880433801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174346977200279952586955867 261520465800419928880433801)
  ·
    refine ⟨196140349350314946660325351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261520465800419928880433801 196140349350314946660325351)
    ·
      refine ⟨294210524025472419990488027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196140349350314946660325351 294210524025472419990488027)
      ·
        refine ⟨441315786038208629985732041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294210524025472419990488027 441315786038208629985732041)
        ·
          refine ⟨330986839528656472489299031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441315786038208629985732041 330986839528656472489299031)
          ·
            refine ⟨496480259292984708733948547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330986839528656472489299031 496480259292984708733948547)
            ·
              refine ⟨744720388939477063100922821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496480259292984708733948547 744720388939477063100922821)
              ·
                refine ⟨139635072926151949331423029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744720388939477063100922821 139635072926151949331423029)
                ·
                  refine ⟨13090788086826745249820909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139635072926151949331423029 13090788086826745249820909)
                  ·
                    refine ⟨4909045532560029468682841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13090788086826745249820909 4909045532560029468682841)
                    ·
                      refine ⟨3681784149420022101512131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909045532560029468682841 3681784149420022101512131)
                      ·
                        rfl

theorem cell23_7170249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3, 2].length) (baseStart_7170249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170249 prefixEnd_7170249 := by exact prefixLift 7170249
  have htrace : WordTrace (prefixWord ++ tailWord_7170249) baseStart_7170249 baseEnd_7170249 := by
    simpa [prefixWord, tailWord_7170249, baseEnd_7170249] using wordTrace_append hprefix tailTrace_7170249
  have hstable : (prefixWord ++ tailWord_7170249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170249).length < 2 ^ (prefixWord ++ tailWord_7170249).sum := by decide
  have hdescent : baseEnd_7170249 < baseStart_7170249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170272 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_7170272 : Nat := 118140960795 + 7170272 * 2 ^ 59
def prefixEnd_7170272 : Nat := 4983230072969 + 3 ^ 40 * 7170272 * 2
def baseEnd_7170272 : Nat := 1227265319825025170508175

theorem tailTrace_7170272 : CollatzResearch.WordTrace tailWord_7170272 prefixEnd_7170272 1227265319825025170508175 := by
  unfold tailWord_7170272
  simp only [CollatzResearch.WordTrace]
  refine ⟨130760652339668301904260535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174347536452891069205680713 130760652339668301904260535)
  ·
    refine ⟨196140978509502452856390803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130760652339668301904260535 196140978509502452856390803)
    ·
      refine ⟨294211467764253679284586205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196140978509502452856390803 294211467764253679284586205)
      ·
        refine ⟨110329300411595129731719827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294211467764253679284586205 110329300411595129731719827)
        ·
          refine ⟨165493950617392694597579741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110329300411595129731719827 165493950617392694597579741)
          ·
            refine ⟨62060231481522260474092403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165493950617392694597579741 62060231481522260474092403)
            ·
              refine ⟨93090347222283390711138605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62060231481522260474092403 93090347222283390711138605)
              ·
                refine ⟨34908880208356271516676977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93090347222283390711138605 34908880208356271516676977)
                ·
                  refine ⟨26181660156267203637507733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34908880208356271516676977 26181660156267203637507733)
                  ·
                    refine ⟨1227265319825025170508175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26181660156267203637507733 1227265319825025170508175)
                    ·
                      rfl

theorem cell23_7170272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_7170272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170272 prefixEnd_7170272 := by exact prefixLift 7170272
  have htrace : WordTrace (prefixWord ++ tailWord_7170272) baseStart_7170272 baseEnd_7170272 := by
    simpa [prefixWord, tailWord_7170272, baseEnd_7170272] using wordTrace_append hprefix tailTrace_7170272
  have hstable : (prefixWord ++ tailWord_7170272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170272).length < 2 ^ (prefixWord ++ tailWord_7170272).sum := by decide
  have hdescent : baseEnd_7170272 < baseStart_7170272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170273 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_7170273 : Nat := 118140960795 + 7170273 * 2 ^ 59
def prefixEnd_7170273 : Nat := 4983230072969 + 3 ^ 40 * 7170273 * 2
def baseEnd_7170273 : Nat := 3681796472955730007612021

theorem tailTrace_7170273 : CollatzResearch.WordTrace tailWord_7170273 prefixEnd_7170273 3681796472955730007612021 := by
  unfold tailWord_7170273
  simp only [CollatzResearch.WordTrace]
  refine ⟨261521341152332980979307473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174347560768221987319538315 261521341152332980979307473)
  ·
    refine ⟨196141005864249735734480605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261521341152332980979307473 196141005864249735734480605)
    ·
      refine ⟨73552877199093650900430227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196141005864249735734480605 73552877199093650900430227)
      ·
        refine ⟨110329315798640476350645341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73552877199093650900430227 110329315798640476350645341)
        ·
          refine ⟨41373493424490178631492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110329315798640476350645341 41373493424490178631492003)
          ·
            refine ⟨62060240136735267947238005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41373493424490178631492003 62060240136735267947238005)
            ·
              refine ⟨5818147512818931370053563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62060240136735267947238005 5818147512818931370053563)
              ·
                refine ⟨8727221269228397055080345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818147512818931370053563 8727221269228397055080345)
                ·
                  refine ⟨6545415951921297791310259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8727221269228397055080345 6545415951921297791310259)
                  ·
                    refine ⟨9818123927881946686965389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6545415951921297791310259 9818123927881946686965389)
                    ·
                      refine ⟨3681796472955730007612021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9818123927881946686965389 3681796472955730007612021)
                      ·
                        rfl

theorem cell23_7170273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_7170273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170273 prefixEnd_7170273 := by exact prefixLift 7170273
  have htrace : WordTrace (prefixWord ++ tailWord_7170273) baseStart_7170273 baseEnd_7170273 := by
    simpa [prefixWord, tailWord_7170273, baseEnd_7170273] using wordTrace_append hprefix tailTrace_7170273
  have hstable : (prefixWord ++ tailWord_7170273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170273).length < 2 ^ (prefixWord ++ tailWord_7170273).sum := by decide
  have hdescent : baseEnd_7170273 < baseStart_7170273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170319 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 5]
def baseStart_7170319 : Nat := 118140960795 + 7170319 * 2 ^ 59
def prefixEnd_7170319 : Nat := 4983230072969 + 3 ^ 40 * 7170319 * 2
def baseEnd_7170319 : Nat := 409091121451759647515201

theorem tailTrace_7170319 : CollatzResearch.WordTrace tailWord_7170319 prefixEnd_7170319 409091121451759647515201 := by
  unfold tailWord_7170319
  simp only [CollatzResearch.WordTrace]
  refine ⟨261523018910166330835482011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174348679273444220556988007 261523018910166330835482011)
  ·
    refine ⟨392284528365249496253223017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261523018910166330835482011 392284528365249496253223017)
    ·
      refine ⟨294213396273937122189917263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392284528365249496253223017 294213396273937122189917263)
      ·
        refine ⟨441320094410905683284875895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294213396273937122189917263 441320094410905683284875895)
        ·
          refine ⟨661980141616358524927313843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441320094410905683284875895 661980141616358524927313843)
          ·
            refine ⟨992970212424537787390970765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661980141616358524927313843 992970212424537787390970765)
            ·
              refine ⟨372363829659201670271614037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992970212424537787390970765 372363829659201670271614037)
              ·
                refine ⟨4363638628818769573495477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 372363829659201670271614037 4363638628818769573495477)
                ·
                  refine ⟨409091121451759647515201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4363638628818769573495477 409091121451759647515201)
                  ·
                    rfl

theorem cell23_7170319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 5].length) (baseStart_7170319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170319 prefixEnd_7170319 := by exact prefixLift 7170319
  have htrace : WordTrace (prefixWord ++ tailWord_7170319) baseStart_7170319 baseEnd_7170319 := by
    simpa [prefixWord, tailWord_7170319, baseEnd_7170319] using wordTrace_append hprefix tailTrace_7170319
  have hstable : (prefixWord ++ tailWord_7170319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170319).length < 2 ^ (prefixWord ++ tailWord_7170319).sum := by decide
  have hdescent : baseEnd_7170319 < baseStart_7170319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170330 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_7170330 : Nat := 118140960795 + 7170330 * 2 ^ 59
def prefixEnd_7170330 : Nat := 4983230072969 + 3 ^ 40 * 7170330 * 2
def baseEnd_7170330 : Nat := 3681825741353036284599259

theorem tailTrace_7170330 : CollatzResearch.WordTrace tailWord_7170330 prefixEnd_7170330 3681825741353036284599259 := by
  unfold tailWord_7170330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65380855028281619928533111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174348946742084319809421629 65380855028281619928533111)
  ·
    refine ⟨98071282542422429892799667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65380855028281619928533111 98071282542422429892799667)
    ·
      refine ⟨147106923813633644839199501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98071282542422429892799667 147106923813633644839199501)
      ·
        refine ⟨55165096430112616814699813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147106923813633644839199501 55165096430112616814699813)
        ·
          refine ⟨10343455580646115652756215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55165096430112616814699813 10343455580646115652756215)
          ·
            refine ⟨15515183370969173479134323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343455580646115652756215 15515183370969173479134323)
            ·
              refine ⟨23272775056453760218701485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515183370969173479134323 23272775056453760218701485)
              ·
                refine ⟨8727290646170160082013057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23272775056453760218701485 8727290646170160082013057)
                ·
                  refine ⟨6545467984627620061509793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8727290646170160082013057 6545467984627620061509793)
                  ·
                    refine ⟨4909100988470715046132345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545467984627620061509793 4909100988470715046132345)
                    ·
                      refine ⟨3681825741353036284599259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909100988470715046132345 3681825741353036284599259)
                      ·
                        rfl

theorem cell23_7170330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_7170330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170330 prefixEnd_7170330 := by exact prefixLift 7170330
  have htrace : WordTrace (prefixWord ++ tailWord_7170330) baseStart_7170330 baseEnd_7170330 := by
    simpa [prefixWord, tailWord_7170330, baseEnd_7170330] using wordTrace_append hprefix tailTrace_7170330
  have hstable : (prefixWord ++ tailWord_7170330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170330).length < 2 ^ (prefixWord ++ tailWord_7170330).sum := by decide
  have hdescent : baseEnd_7170330 < baseStart_7170330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170366 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_7170366 : Nat := 118140960795 + 7170366 * 2 ^ 59
def prefixEnd_7170366 : Nat := 4983230072969 + 3 ^ 40 * 7170366 * 2
def baseEnd_7170366 : Nat := 1227281408885532714583031

theorem tailTrace_7170366 : CollatzResearch.WordTrace tailWord_7170366 prefixEnd_7170366 1227281408885532714583031 := by
  unfold tailWord_7170366
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690591642624507232805369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174349822093997371908295301 32690591642624507232805369)
  ·
    refine ⟨24517943731968380424604027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32690591642624507232805369 24517943731968380424604027)
    ·
      refine ⟨36776915597952570636906041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24517943731968380424604027 36776915597952570636906041)
      ·
        refine ⟨27582686698464427977679531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36776915597952570636906041 27582686698464427977679531)
        ·
          refine ⟨41374030047696641966519297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582686698464427977679531 41374030047696641966519297)
          ·
            refine ⟨31030522535772481474889473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41374030047696641966519297 31030522535772481474889473)
            ·
              refine ⟨23272891901829361106167105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31030522535772481474889473 23272891901829361106167105)
              ·
                refine ⟨17454668926372020829625329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23272891901829361106167105 17454668926372020829625329)
                ·
                  refine ⟨13091001694779015622218997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17454668926372020829625329 13091001694779015622218997)
                  ·
                    refine ⟨1227281408885532714583031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13091001694779015622218997 1227281408885532714583031)
                    ·
                      rfl

theorem cell23_7170366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_7170366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170366 prefixEnd_7170366 := by exact prefixLift 7170366
  have htrace : WordTrace (prefixWord ++ tailWord_7170366) baseStart_7170366 baseEnd_7170366 := by
    simpa [prefixWord, tailWord_7170366, baseEnd_7170366] using wordTrace_append hprefix tailTrace_7170366
  have hstable : (prefixWord ++ tailWord_7170366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170366).length < 2 ^ (prefixWord ++ tailWord_7170366).sum := by decide
  have hdescent : baseEnd_7170366 < baseStart_7170366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170386 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_7170386 : Nat := 118140960795 + 7170386 * 2 ^ 59
def prefixEnd_7170386 : Nat := 4983230072969 + 3 ^ 40 * 7170386 * 2
def baseEnd_7170386 : Nat := 3681854496269688065499001

theorem tailTrace_7170386 : CollatzResearch.WordTrace tailWord_7170386 prefixEnd_7170386 3681854496269688065499001 := by
  unfold tailWord_7170386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65381365650230900319542753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174350308400615734185447341 65381365650230900319542753)
  ·
    refine ⟨49036024237673175239657065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65381365650230900319542753 49036024237673175239657065)
    ·
      refine ⟨36777018178254881429742799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49036024237673175239657065 36777018178254881429742799)
      ·
        refine ⟨55165527267382322144614199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36777018178254881429742799 55165527267382322144614199)
        ·
          refine ⟨82748290901073483216921299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55165527267382322144614199 82748290901073483216921299)
          ·
            refine ⟨124122436351610224825381949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82748290901073483216921299 124122436351610224825381949)
            ·
              refine ⟨46545913631853834309518231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124122436351610224825381949 46545913631853834309518231)
              ·
                refine ⟨69818870447780751464277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46545913631853834309518231 69818870447780751464277347)
                ·
                  refine ⟨104728305671671127196416021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69818870447780751464277347 104728305671671127196416021)
                  ·
                    refine ⟨4909139328359584087332001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104728305671671127196416021 4909139328359584087332001)
                    ·
                      refine ⟨3681854496269688065499001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909139328359584087332001 3681854496269688065499001)
                      ·
                        rfl

theorem cell23_7170386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_7170386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170386 prefixEnd_7170386 := by exact prefixLift 7170386
  have htrace : WordTrace (prefixWord ++ tailWord_7170386) baseStart_7170386 baseEnd_7170386 := by
    simpa [prefixWord, tailWord_7170386, baseEnd_7170386] using wordTrace_append hprefix tailTrace_7170386
  have hstable : (prefixWord ++ tailWord_7170386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170386).length < 2 ^ (prefixWord ++ tailWord_7170386).sum := by decide
  have hdescent : baseEnd_7170386 < baseStart_7170386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170429 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_7170429 : Nat := 118140960795 + 7170429 * 2 ^ 59
def prefixEnd_7170429 : Nat := 4983230072969 + 3 ^ 40 * 7170429 * 2
def baseEnd_7170429 : Nat := 3681876575937831397261303

theorem tailTrace_7170429 : CollatzResearch.WordTrace tailWord_7170429 prefixEnd_7170429 3681876575937831397261303 := by
  unfold tailWord_7170429
  simp only [CollatzResearch.WordTrace]
  refine ⟨261527030939767819621986341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174351353959845213081324227 261527030939767819621986341)
  ·
    refine ⟨49036318301206466179122439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261527030939767819621986341 49036318301206466179122439)
    ·
      refine ⟨73554477451809699268683659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49036318301206466179122439 73554477451809699268683659)
      ·
        refine ⟨110331716177714548903025489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73554477451809699268683659 110331716177714548903025489)
        ·
          refine ⟨82748787133285911677269117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110331716177714548903025489 82748787133285911677269117)
          ·
            refine ⟨31030795174982216878975919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82748787133285911677269117 31030795174982216878975919)
            ·
              refine ⟨46546192762473325318463879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31030795174982216878975919 46546192762473325318463879)
              ·
                refine ⟨69819289143709987977695819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46546192762473325318463879 69819289143709987977695819)
                ·
                  refine ⟨104728933715564981966543729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69819289143709987977695819 104728933715564981966543729)
                  ·
                    refine ⟨78546700286673736474907797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104728933715564981966543729 78546700286673736474907797)
                    ·
                      refine ⟨3681876575937831397261303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78546700286673736474907797 3681876575937831397261303)
                      ·
                        rfl

theorem cell23_7170429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_7170429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170429 prefixEnd_7170429 := by exact prefixLift 7170429
  have htrace : WordTrace (prefixWord ++ tailWord_7170429) baseStart_7170429 baseEnd_7170429 := by
    simpa [prefixWord, tailWord_7170429, baseEnd_7170429] using wordTrace_append hprefix tailTrace_7170429
  have hstable : (prefixWord ++ tailWord_7170429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170429).length < 2 ^ (prefixWord ++ tailWord_7170429).sum := by decide
  have hdescent : baseEnd_7170429 < baseStart_7170429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170463 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7170463 : Nat := 118140960795 + 7170463 * 2 ^ 59
def prefixEnd_7170463 : Nat := 4983230072969 + 3 ^ 40 * 7170463 * 2
def baseEnd_7170463 : Nat := 3681894034280084264236147

theorem tailTrace_7170463 : CollatzResearch.WordTrace tailWord_7170463 prefixEnd_7170463 3681894034280084264236147 := by
  unfold tailWord_7170463
  simp only [CollatzResearch.WordTrace]
  refine ⟨261528271021644643428724043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174352180681096428952482695 261528271021644643428724043)
  ·
    refine ⟨392292406532466965143086065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261528271021644643428724043 392292406532466965143086065)
    ·
      refine ⟨294219304899350223857314549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392292406532466965143086065 294219304899350223857314549)
      ·
        refine ⟨27583059834314083486623239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294219304899350223857314549 27583059834314083486623239)
        ·
          refine ⟨41374589751471125229934859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27583059834314083486623239 41374589751471125229934859)
          ·
            refine ⟨62061884627206687844902289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41374589751471125229934859 62061884627206687844902289)
            ·
              refine ⟨46546413470405015883676717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62061884627206687844902289 46546413470405015883676717)
              ·
                refine ⟨17454905051401880956378769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46546413470405015883676717 17454905051401880956378769)
                ·
                  refine ⟨13091178788551410717284077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17454905051401880956378769 13091178788551410717284077)
                  ·
                    refine ⟨4909192045706779018981529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13091178788551410717284077 4909192045706779018981529)
                    ·
                      refine ⟨3681894034280084264236147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909192045706779018981529 3681894034280084264236147)
                      ·
                        rfl

theorem cell23_7170463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7170463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170463 prefixEnd_7170463 := by exact prefixLift 7170463
  have htrace : WordTrace (prefixWord ++ tailWord_7170463) baseStart_7170463 baseEnd_7170463 := by
    simpa [prefixWord, tailWord_7170463, baseEnd_7170463] using wordTrace_append hprefix tailTrace_7170463
  have hstable : (prefixWord ++ tailWord_7170463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170463).length < 2 ^ (prefixWord ++ tailWord_7170463).sum := by decide
  have hdescent : baseEnd_7170463 < baseStart_7170463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170469 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_7170469 : Nat := 118140960795 + 7170469 * 2 ^ 59
def prefixEnd_7170469 : Nat := 4983230072969 + 3 ^ 40 * 7170469 * 2
def baseEnd_7170469 : Nat := 1227299038388003746920373

theorem tailTrace_7170469 : CollatzResearch.WordTrace tailWord_7170469 prefixEnd_7170469 1227299038388003746920373 := by
  unfold tailWord_7170469
  simp only [CollatzResearch.WordTrace]
  refine ⟨261528489859622906453442461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174352326573081937635628307 261528489859622906453442461)
  ·
    refine ⟨98073183697358589920040923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261528489859622906453442461 98073183697358589920040923)
    ·
      refine ⟨147109775546037884880061385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98073183697358589920040923 147109775546037884880061385)
      ·
        refine ⟨110332331659528413660046039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147109775546037884880061385 110332331659528413660046039)
        ·
          refine ⟨165498497489292620490069059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110332331659528413660046039 165498497489292620490069059)
          ·
            refine ⟨248247746233938930735103589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165498497489292620490069059 248247746233938930735103589)
            ·
              refine ⟨46546452418863549512831923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248247746233938930735103589 46546452418863549512831923)
              ·
                refine ⟨69819678628295324269247885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46546452418863549512831923 69819678628295324269247885)
                ·
                  refine ⟨26182379485610746600967957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69819678628295324269247885 26182379485610746600967957)
                  ·
                    refine ⟨1227299038388003746920373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26182379485610746600967957 1227299038388003746920373)
                    ·
                      rfl

theorem cell23_7170469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_7170469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170469 prefixEnd_7170469 := by exact prefixLift 7170469
  have htrace : WordTrace (prefixWord ++ tailWord_7170469) baseStart_7170469 baseEnd_7170469 := by
    simpa [prefixWord, tailWord_7170469, baseEnd_7170469] using wordTrace_append hprefix tailTrace_7170469
  have hstable : (prefixWord ++ tailWord_7170469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170469).length < 2 ^ (prefixWord ++ tailWord_7170469).sum := by decide
  have hdescent : baseEnd_7170469 < baseStart_7170469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170487 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_7170487 : Nat := 118140960795 + 7170487 * 2 ^ 59
def prefixEnd_7170487 : Nat := 4983230072969 + 3 ^ 40 * 7170487 * 2
def baseEnd_7170487 : Nat := 3681906357815792170336037

theorem tailTrace_7170487 : CollatzResearch.WordTrace tailWord_7170487 prefixEnd_7170487 3681906357815792170336037 := by
  unfold tailWord_7170487
  simp only [CollatzResearch.WordTrace]
  refine ⟨261529146373557695527597715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174352764249038463685065143 261529146373557695527597715)
  ·
    refine ⟨392293719560336543291396573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261529146373557695527597715 392293719560336543291396573)
    ·
      refine ⟨147110144835126203734273715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392293719560336543291396573 147110144835126203734273715)
      ·
        refine ⟨220665217252689305601410573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147110144835126203734273715 220665217252689305601410573)
        ·
          refine ⟨82749456469758489600528965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220665217252689305601410573 82749456469758489600528965)
          ·
            refine ⟨15515523088079716800099181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82749456469758489600528965 15515523088079716800099181)
            ·
              refine ⟨5818321158029893800037193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15515523088079716800099181 5818321158029893800037193)
              ·
                refine ⟨4363740868522420350027895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818321158029893800037193 4363740868522420350027895)
                ·
                  refine ⟨6545611302783630525041843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363740868522420350027895 6545611302783630525041843)
                  ·
                    refine ⟨9818416954175445787562765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6545611302783630525041843 9818416954175445787562765)
                    ·
                      refine ⟨3681906357815792170336037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9818416954175445787562765 3681906357815792170336037)
                      ·
                        rfl

theorem cell23_7170487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_7170487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170487 prefixEnd_7170487 := by exact prefixLift 7170487
  have htrace : WordTrace (prefixWord ++ tailWord_7170487) baseStart_7170487 baseEnd_7170487 := by
    simpa [prefixWord, tailWord_7170487, baseEnd_7170487] using wordTrace_append hprefix tailTrace_7170487
  have hstable : (prefixWord ++ tailWord_7170487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170487).length < 2 ^ (prefixWord ++ tailWord_7170487).sum := by decide
  have hdescent : baseEnd_7170487 < baseStart_7170487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170496 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_7170496 : Nat := 118140960795 + 7170496 * 2 ^ 59
def prefixEnd_7170496 : Nat := 4983230072969 + 3 ^ 40 * 7170496 * 2
def baseEnd_7170496 : Nat := 3681910979141682635123495

theorem tailTrace_7170496 : CollatzResearch.WordTrace tailWord_7170496 prefixEnd_7170496 3681910979141682635123495 := by
  unfold tailWord_7170496
  simp only [CollatzResearch.WordTrace]
  refine ⟨130764737315262545032337671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174352983087016726709783561 130764737315262545032337671)
  ·
    refine ⟨196147105972893817548506507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130764737315262545032337671 196147105972893817548506507)
    ·
      refine ⟨294220658959340726322759761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196147105972893817548506507 294220658959340726322759761)
      ·
        refine ⟨220665494219505544742069821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294220658959340726322759761 220665494219505544742069821)
        ·
          refine ⟨82749560332314579278276183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220665494219505544742069821 82749560332314579278276183)
          ·
            refine ⟨124124340498471868917414275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82749560332314579278276183 124124340498471868917414275)
            ·
              refine ⟨186186510747707803376121413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124124340498471868917414275 186186510747707803376121413)
              ·
                refine ⟨34909970765195213133022765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186186510747707803376121413 34909970765195213133022765)
                ·
                  refine ⟨13091239036948204924883537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34909970765195213133022765 13091239036948204924883537)
                  ·
                    refine ⟨9818429277711153693662653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13091239036948204924883537 9818429277711153693662653)
                    ·
                      refine ⟨3681910979141682635123495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9818429277711153693662653 3681910979141682635123495)
                      ·
                        rfl

theorem cell23_7170496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_7170496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170496 prefixEnd_7170496 := by exact prefixLift 7170496
  have htrace : WordTrace (prefixWord ++ tailWord_7170496) baseStart_7170496 baseEnd_7170496 := by
    simpa [prefixWord, tailWord_7170496, baseEnd_7170496] using wordTrace_append hprefix tailTrace_7170496
  have hstable : (prefixWord ++ tailWord_7170496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170496).length < 2 ^ (prefixWord ++ tailWord_7170496).sum := by decide
  have hdescent : baseEnd_7170496 < baseStart_7170496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170503 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 2, 4]
def baseStart_7170503 : Nat := 118140960795 + 7170503 * 2 ^ 59
def prefixEnd_7170503 : Nat := 4983230072969 + 3 ^ 40 * 7170503 * 2
def baseEnd_7170503 : Nat := 1227304857835421369245321

theorem tailTrace_7170503 : CollatzResearch.WordTrace tailWord_7170503 prefixEnd_7170503 1227304857835421369245321 := by
  unfold tailWord_7170503
  simp only [CollatzResearch.WordTrace]
  refine ⟨261529729941499730260180163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174353153294333153506786775 261529729941499730260180163)
  ·
    refine ⟨392294594912249595390270245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261529729941499730260180163 392294594912249595390270245)
    ·
      refine ⟨73555236546046799135675671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392294594912249595390270245 73555236546046799135675671)
      ·
        refine ⟨110332854819070198703513507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73555236546046799135675671 110332854819070198703513507)
        ·
          refine ⟨165499282228605298055270261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110332854819070198703513507 165499282228605298055270261)
          ·
            refine ⟨15515557708931746692681587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165499282228605298055270261 15515557708931746692681587)
            ·
              refine ⟨23273336563397620039022381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515557708931746692681587 23273336563397620039022381)
              ·
                refine ⟨8727501211274107514633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23273336563397620039022381 8727501211274107514633393)
                ·
                  refine ⟨6545625908455580635975045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8727501211274107514633393 6545625908455580635975045)
                  ·
                    refine ⟨1227304857835421369245321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545625908455580635975045 1227304857835421369245321)
                    ·
                      rfl

theorem cell23_7170503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_7170503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170503 prefixEnd_7170503 := by exact prefixLift 7170503
  have htrace : WordTrace (prefixWord ++ tailWord_7170503) baseStart_7170503 baseEnd_7170503 := by
    simpa [prefixWord, tailWord_7170503, baseEnd_7170503] using wordTrace_append hprefix tailTrace_7170503
  have hstable : (prefixWord ++ tailWord_7170503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170503).length < 2 ^ (prefixWord ++ tailWord_7170503).sum := by decide
  have hdescent : baseEnd_7170503 < baseStart_7170503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170506 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_7170506 : Nat := 118140960795 + 7170506 * 2 ^ 59
def prefixEnd_7170506 : Nat := 4983230072969 + 3 ^ 40 * 7170506 * 2
def baseEnd_7170506 : Nat := 3681916113948227595998449

theorem tailTrace_7170506 : CollatzResearch.WordTrace tailWord_7170506 prefixEnd_7170506 3681916113948227595998449 := by
  unfold tailWord_7170506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65382459840122215443134843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174353226240325907848359581 65382459840122215443134843)
  ·
    refine ⟨98073689760183323164702265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65382459840122215443134843 98073689760183323164702265)
    ·
      refine ⟨73555267320137492373526699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98073689760183323164702265 73555267320137492373526699)
      ·
        refine ⟨110332900980206238560290049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73555267320137492373526699 110332900980206238560290049)
        ·
          refine ⟨82749675735154678920217537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110332900980206238560290049 82749675735154678920217537)
          ·
            refine ⟨62062256801366009190163153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82749675735154678920217537 62062256801366009190163153)
            ·
              refine ⟨46546692601024506892622365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62062256801366009190163153 46546692601024506892622365)
              ·
                refine ⟨17455009725384190084733387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46546692601024506892622365 17455009725384190084733387)
                ·
                  refine ⟨26182514588076285127100081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17455009725384190084733387 26182514588076285127100081)
                  ·
                    refine ⟨19636885941057213845325061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26182514588076285127100081 19636885941057213845325061)
                    ·
                      refine ⟨3681916113948227595998449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19636885941057213845325061 3681916113948227595998449)
                      ·
                        rfl

theorem cell23_7170506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_7170506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170506 prefixEnd_7170506 := by exact prefixLift 7170506
  have htrace : WordTrace (prefixWord ++ tailWord_7170506) baseStart_7170506 baseEnd_7170506 := by
    simpa [prefixWord, tailWord_7170506, baseEnd_7170506] using wordTrace_append hprefix tailTrace_7170506
  have hstable : (prefixWord ++ tailWord_7170506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170506).length < 2 ^ (prefixWord ++ tailWord_7170506).sum := by decide
  have hdescent : baseEnd_7170506 < baseStart_7170506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170516 : List Nat := [2, 4, 1, 2, 2, 1, 2, 9]
def baseStart_7170516 : Nat := 118140960795 + 7170516 * 2 ^ 59
def prefixEnd_7170516 : Nat := 4983230072969 + 3 ^ 40 * 7170516 * 2
def baseEnd_7170516 : Nat := 136367453657584168773089

theorem tailTrace_7170516 : CollatzResearch.WordTrace tailWord_7170516 prefixEnd_7170516 136367453657584168773089 := by
  unfold tailWord_7170516
  simp only [CollatzResearch.WordTrace]
  refine ⟨130765102045226316740201701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174353469393635088986935601 130765102045226316740201701)
  ·
    refine ⟨24518456633479934388787819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130765102045226316740201701 24518456633479934388787819)
    ·
      refine ⟨36777684950219901583181729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24518456633479934388787819 36777684950219901583181729)
      ·
        refine ⟨27583263712664926187386297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36777684950219901583181729 27583263712664926187386297)
        ·
          refine ⟨20687447784498694640539723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27583263712664926187386297 20687447784498694640539723)
          ·
            refine ⟨31031171676748041960809585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20687447784498694640539723 31031171676748041960809585)
            ·
              refine ⟨23273378757561031470607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31031171676748041960809585 23273378757561031470607189)
              ·
                refine ⟨136367453657584168773089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23273378757561031470607189 136367453657584168773089)
                ·
                  rfl

theorem cell23_7170516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 9].length) (baseStart_7170516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170516 prefixEnd_7170516 := by exact prefixLift 7170516
  have htrace : WordTrace (prefixWord ++ tailWord_7170516) baseStart_7170516 baseEnd_7170516 := by
    simpa [prefixWord, tailWord_7170516, baseEnd_7170516] using wordTrace_append hprefix tailTrace_7170516
  have hstable : (prefixWord ++ tailWord_7170516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170516).length < 2 ^ (prefixWord ++ tailWord_7170516).sum := by decide
  have hdescent : baseEnd_7170516 < baseStart_7170516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170553 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 3, 3, 2]
def baseStart_7170553 : Nat := 118140960795 + 7170553 * 2 ^ 59
def prefixEnd_7170553 : Nat := 4983230072969 + 3 ^ 40 * 7170553 * 2
def baseEnd_7170553 : Nat := 3681940247538988912110733

theorem tailTrace_7170553 : CollatzResearch.WordTrace tailWord_7170553 prefixEnd_7170553 3681940247538988912110733 := by
  unfold tailWord_7170553
  simp only [CollatzResearch.WordTrace]
  refine ⟨261531553591318588799500313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174354369060879059199666875 261531553591318588799500313)
  ·
    refine ⟨196148665193488941599625235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261531553591318588799500313 196148665193488941599625235)
    ·
      refine ⟨294222997790233412399437853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196148665193488941599625235 294222997790233412399437853)
      ·
        refine ⟨110333624171337529649789195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294222997790233412399437853 110333624171337529649789195)
        ·
          refine ⟨165500436257006294474683793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110333624171337529649789195 165500436257006294474683793)
          ·
            refine ⟨124125327192754720856012845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165500436257006294474683793 124125327192754720856012845)
            ·
              refine ⟨46546997697283020321004817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124125327192754720856012845 46546997697283020321004817)
              ·
                refine ⟨34910248272962265240753613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46546997697283020321004817 34910248272962265240753613)
                ·
                  refine ⟨13091343102360849465282605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34910248272962265240753613 13091343102360849465282605)
                  ·
                    refine ⟨4909253663385318549480977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13091343102360849465282605 4909253663385318549480977)
                    ·
                      refine ⟨3681940247538988912110733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909253663385318549480977 3681940247538988912110733)
                      ·
                        rfl

theorem cell23_7170553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_7170553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170553 prefixEnd_7170553 := by exact prefixLift 7170553
  have htrace : WordTrace (prefixWord ++ tailWord_7170553) baseStart_7170553 baseEnd_7170553 := by
    simpa [prefixWord, tailWord_7170553, baseEnd_7170553] using wordTrace_append hprefix tailTrace_7170553
  have hstable : (prefixWord ++ tailWord_7170553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170553).length < 2 ^ (prefixWord ++ tailWord_7170553).sum := by decide
  have hdescent : baseEnd_7170553 < baseStart_7170553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170570 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_7170570 : Nat := 118140960795 + 7170570 * 2 ^ 59
def prefixEnd_7170570 : Nat := 4983230072969 + 3 ^ 40 * 7170570 * 2
def baseEnd_7170570 : Nat := 3681948976710115345598155

theorem tailTrace_7170570 : CollatzResearch.WordTrace tailWord_7170570 prefixEnd_7170570 3681948976710115345598155 := by
  unfold tailWord_7170570
  simp only [CollatzResearch.WordTrace]
  refine ⟨65383043408064250175717291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174354782421504667135246109 65383043408064250175717291)
  ·
    refine ⟨98074565112096375263575937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65383043408064250175717291 98074565112096375263575937)
    ·
      refine ⟨73555923834072281447681953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98074565112096375263575937 73555923834072281447681953)
      ·
        refine ⟨55166942875554211085761465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73555923834072281447681953 55166942875554211085761465)
        ·
          refine ⟨41375207156665658314321099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55166942875554211085761465 41375207156665658314321099)
          ·
            refine ⟨62062810734998487471481649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41375207156665658314321099 62062810734998487471481649)
            ·
              refine ⟨46547108051248865603611237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62062810734998487471481649 46547108051248865603611237)
              ·
                refine ⟨8727582759609162300677107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46547108051248865603611237 8727582759609162300677107)
                ·
                  refine ⟨13091374139413743451015661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727582759609162300677107 13091374139413743451015661)
                  ·
                    refine ⟨4909265302280153794130873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13091374139413743451015661 4909265302280153794130873)
                    ·
                      refine ⟨3681948976710115345598155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909265302280153794130873 3681948976710115345598155)
                      ·
                        rfl

theorem cell23_7170570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_7170570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170570 prefixEnd_7170570 := by exact prefixLift 7170570
  have htrace : WordTrace (prefixWord ++ tailWord_7170570) baseStart_7170570 baseEnd_7170570 := by
    simpa [prefixWord, tailWord_7170570, baseEnd_7170570] using wordTrace_append hprefix tailTrace_7170570
  have hstable : (prefixWord ++ tailWord_7170570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170570).length < 2 ^ (prefixWord ++ tailWord_7170570).sum := by decide
  have hdescent : baseEnd_7170570 < baseStart_7170570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170586 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_7170586 : Nat := 118140960795 + 7170586 * 2 ^ 59
def prefixEnd_7170586 : Nat := 4983230072969 + 3 ^ 40 * 7170586 * 2
def baseEnd_7170586 : Nat := 3681957192400587282998081

theorem tailTrace_7170586 : CollatzResearch.WordTrace tailWord_7170586 prefixEnd_7170586 3681957192400587282998081 := by
  unfold tailWord_7170586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65383189300049758858862903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174355171466799356956967741 65383189300049758858862903)
  ·
    refine ⟨98074783950074638288294355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65383189300049758858862903 98074783950074638288294355)
    ·
      refine ⟨147112175925111957432441533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98074783950074638288294355 147112175925111957432441533)
      ·
        refine ⟨55167065971916984037165575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147112175925111957432441533 55167065971916984037165575)
        ·
          refine ⟨82750598957875476055748363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55167065971916984037165575 82750598957875476055748363)
          ·
            refine ⟨124125898436813214083622545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82750598957875476055748363 124125898436813214083622545)
            ·
              refine ⟨93094423827609910562716909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124125898436813214083622545 93094423827609910562716909)
              ·
                refine ⟨34910408935353716461018841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93094423827609910562716909 34910408935353716461018841)
                ·
                  refine ⟨26182806701515287345764131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34910408935353716461018841 26182806701515287345764131)
                  ·
                    refine ⟨39274210052272931018646197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26182806701515287345764131 39274210052272931018646197)
                    ·
                      refine ⟨3681957192400587282998081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39274210052272931018646197 3681957192400587282998081)
                      ·
                        rfl

theorem cell23_7170586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_7170586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170586 prefixEnd_7170586 := by exact prefixLift 7170586
  have htrace : WordTrace (prefixWord ++ tailWord_7170586) baseStart_7170586 baseEnd_7170586 := by
    simpa [prefixWord, tailWord_7170586, baseEnd_7170586] using wordTrace_append hprefix tailTrace_7170586
  have hstable : (prefixWord ++ tailWord_7170586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170586).length < 2 ^ (prefixWord ++ tailWord_7170586).sum := by decide
  have hdescent : baseEnd_7170586 < baseStart_7170586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170636 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_7170636 : Nat := 118140960795 + 7170636 * 2 ^ 59
def prefixEnd_7170636 : Nat := 4983230072969 + 3 ^ 40 * 7170636 * 2
def baseEnd_7170636 : Nat := 1227327622144437362457617

theorem tailTrace_7170636 : CollatzResearch.WordTrace tailWord_7170636 prefixEnd_7170636 1227327622144437362457617 := by
  unfold tailWord_7170636
  simp only [CollatzResearch.WordTrace]
  refine ⟨130767290425008946987385881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174356387233345262649847841 130767290425008946987385881)
  ·
    refine ⟨98075467818756710240539411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130767290425008946987385881 98075467818756710240539411)
    ·
      refine ⟨147113201728135065360809117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98075467818756710240539411 147113201728135065360809117)
      ·
        refine ⟨55167450648050649510303419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147113201728135065360809117 55167450648050649510303419)
        ·
          refine ⟨82751175972075974265455129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55167450648050649510303419 82751175972075974265455129)
          ·
            refine ⟨62063381979056980699091347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82751175972075974265455129 62063381979056980699091347)
            ·
              refine ⟨93095072968585471048637021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62063381979056980699091347 93095072968585471048637021)
              ·
                refine ⟨34910652363219551643238883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93095072968585471048637021 34910652363219551643238883)
                ·
                  refine ⟨52365978544829327464858325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34910652363219551643238883 52365978544829327464858325)
                  ·
                    refine ⟨1227327622144437362457617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52365978544829327464858325 1227327622144437362457617)
                    ·
                      rfl

theorem cell23_7170636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_7170636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170636 prefixEnd_7170636 := by exact prefixLift 7170636
  have htrace : WordTrace (prefixWord ++ tailWord_7170636) baseStart_7170636 baseEnd_7170636 := by
    simpa [prefixWord, tailWord_7170636, baseEnd_7170636] using wordTrace_append hprefix tailTrace_7170636
  have hstable : (prefixWord ++ tailWord_7170636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170636).length < 2 ^ (prefixWord ++ tailWord_7170636).sum := by decide
  have hdescent : baseEnd_7170636 < baseStart_7170636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170713 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 6]
def baseStart_7170713 : Nat := 118140960795 + 7170713 * 2 ^ 59
def prefixEnd_7170713 : Nat := 4983230072969 + 3 ^ 40 * 7170713 * 2
def baseEnd_7170713 : Nat := 409113600493745365123333

theorem tailTrace_7170713 : CollatzResearch.WordTrace tailWord_7170713 prefixEnd_7170713 409113600493745365123333 := by
  unfold tailWord_7170713
  simp only [CollatzResearch.WordTrace]
  refine ⟨261537389270738936125324793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174358259513825957416883195 261537389270738936125324793)
  ·
    refine ⟨196153041953054202093993595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261537389270738936125324793 196153041953054202093993595)
    ·
      refine ⟨294229562929581303140990393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196153041953054202093993595 294229562929581303140990393)
      ·
        refine ⟨220672172197185977355742795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294229562929581303140990393 220672172197185977355742795)
        ·
          refine ⟨331008258295778966033614193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220672172197185977355742795 331008258295778966033614193)
          ·
            refine ⟨248256193721834224525210645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331008258295778966033614193 248256193721834224525210645)
            ·
              refine ⟨11637009080710979274619249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248256193721834224525210645 11637009080710979274619249)
              ·
                refine ⟨8727756810533234455964437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11637009080710979274619249 8727756810533234455964437)
                ·
                  refine ⟨409113600493745365123333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8727756810533234455964437 409113600493745365123333)
                  ·
                    rfl

theorem cell23_7170713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_7170713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170713 prefixEnd_7170713 := by exact prefixLift 7170713
  have htrace : WordTrace (prefixWord ++ tailWord_7170713) baseStart_7170713 baseEnd_7170713 := by
    simpa [prefixWord, tailWord_7170713, baseEnd_7170713] using wordTrace_append hprefix tailTrace_7170713
  have hstable : (prefixWord ++ tailWord_7170713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170713).length < 2 ^ (prefixWord ++ tailWord_7170713).sum := by decide
  have hdescent : baseEnd_7170713 < baseStart_7170713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170736 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_7170736 : Nat := 118140960795 + 7170736 * 2 ^ 59
def prefixEnd_7170736 : Nat := 4983230072969 + 3 ^ 40 * 7170736 * 2
def baseEnd_7170736 : Nat := 3682034214498761696122391

theorem tailTrace_7170736 : CollatzResearch.WordTrace tailWord_7170736 prefixEnd_7170736 3682034214498761696122391 := by
  unfold tailWord_7170736
  simp only [CollatzResearch.WordTrace]
  refine ⟨130769114074827805526706031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174358818766437074035608041 130769114074827805526706031)
  ·
    refine ⟨196153671112241708290059047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130769114074827805526706031 196153671112241708290059047)
    ·
      refine ⟨294230506668362562435088571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196153671112241708290059047 294230506668362562435088571)
      ·
        refine ⟨441345760002543843652632857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294230506668362562435088571 441345760002543843652632857)
        ·
          refine ⟨331009320001907882739474643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441345760002543843652632857 331009320001907882739474643)
          ·
            refine ⟨496513980002861824109211965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331009320001907882739474643 496513980002861824109211965)
            ·
              refine ⟨186192742501073184040954487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496513980002861824109211965 186192742501073184040954487)
              ·
                refine ⟨279289113751609776061431731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186192742501073184040954487 279289113751609776061431731)
                ·
                  refine ⟨418933670627414664092147597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279289113751609776061431731 418933670627414664092147597)
                  ·
                    refine ⟨157100126485280499034555349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418933670627414664092147597 157100126485280499034555349)
                    ·
                      refine ⟨3682034214498761696122391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157100126485280499034555349 3682034214498761696122391)
                      ·
                        rfl

theorem cell23_7170736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_7170736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170736 prefixEnd_7170736 := by exact prefixLift 7170736
  have htrace : WordTrace (prefixWord ++ tailWord_7170736) baseStart_7170736 baseEnd_7170736 := by
    simpa [prefixWord, tailWord_7170736, baseEnd_7170736] using wordTrace_append hprefix tailTrace_7170736
  have hstable : (prefixWord ++ tailWord_7170736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170736).length < 2 ^ (prefixWord ++ tailWord_7170736).sum := by decide
  have hdescent : baseEnd_7170736 < baseStart_7170736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170760 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_7170760 : Nat := 118140960795 + 7170760 * 2 ^ 59
def prefixEnd_7170760 : Nat := 4983230072969 + 3 ^ 40 * 7170760 * 2
def baseEnd_7170760 : Nat := 1227348846011489867407427

theorem tailTrace_7170760 : CollatzResearch.WordTrace tailWord_7170760 prefixEnd_7170760 1227348846011489867407427 := by
  unfold tailWord_7170760
  simp only [CollatzResearch.WordTrace]
  refine ⟨130769551750784331576142867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174359402334379108768190489 130769551750784331576142867)
  ·
    refine ⟨196154327626176497364214301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130769551750784331576142867 196154327626176497364214301)
    ·
      refine ⟨73557872859816186511580363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196154327626176497364214301 73557872859816186511580363)
      ·
        refine ⟨110336809289724279767370545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73557872859816186511580363 110336809289724279767370545)
        ·
          refine ⟨82752606967293209825527909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110336809289724279767370545 82752606967293209825527909)
          ·
            refine ⟨15516113806367476842286483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82752606967293209825527909 15516113806367476842286483)
            ·
              refine ⟨23274170709551215263429725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516113806367476842286483 23274170709551215263429725)
              ·
                refine ⟨8727814016081705723786147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23274170709551215263429725 8727814016081705723786147)
                ·
                  refine ⟨13091721024122558585679221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727814016081705723786147 13091721024122558585679221)
                  ·
                    refine ⟨1227348846011489867407427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13091721024122558585679221 1227348846011489867407427)
                    ·
                      rfl

theorem cell23_7170760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_7170760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170760 prefixEnd_7170760 := by exact prefixLift 7170760
  have htrace : WordTrace (prefixWord ++ tailWord_7170760) baseStart_7170760 baseEnd_7170760 := by
    simpa [prefixWord, tailWord_7170760, baseEnd_7170760] using wordTrace_append hprefix tailTrace_7170760
  have hstable : (prefixWord ++ tailWord_7170760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170760).length < 2 ^ (prefixWord ++ tailWord_7170760).sum := by decide
  have hdescent : baseEnd_7170760 < baseStart_7170760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170783 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_7170783 : Nat := 118140960795 + 7170783 * 2 ^ 59
def prefixEnd_7170783 : Nat := 4983230072969 + 3 ^ 40 * 7170783 * 2
def baseEnd_7170783 : Nat := 3682058348089523012234675

theorem tailTrace_7170783 : CollatzResearch.WordTrace tailWord_7170783 prefixEnd_7170783 3682058348089523012234675 := by
  unfold tailWord_7170783
  simp only [CollatzResearch.WordTrace]
  refine ⟨261539942380485338080373003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174359961586990225386915335 261539942380485338080373003)
  ·
    refine ⟨392309913570728007120559505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261539942380485338080373003 392309913570728007120559505)
    ·
      refine ⟨294232435178046005340419629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392309913570728007120559505 294232435178046005340419629)
      ·
        refine ⟨110337163191767252002657361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294232435178046005340419629 110337163191767252002657361)
        ·
          refine ⟨82752872393825439001993021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110337163191767252002657361 82752872393825439001993021)
          ·
            refine ⟨31032327147684539625747383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82752872393825439001993021 31032327147684539625747383)
            ·
              refine ⟨46548490721526809438621075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31032327147684539625747383 46548490721526809438621075)
              ·
                refine ⟨69822736082290214157931613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46548490721526809438621075 69822736082290214157931613)
                ·
                  refine ⟨26183526030858830309224355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69822736082290214157931613 26183526030858830309224355)
                  ·
                    refine ⟨39275289046288245463836533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26183526030858830309224355 39275289046288245463836533)
                    ·
                      refine ⟨3682058348089523012234675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39275289046288245463836533 3682058348089523012234675)
                      ·
                        rfl

theorem cell23_7170783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_7170783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170783 prefixEnd_7170783 := by exact prefixLift 7170783
  have htrace : WordTrace (prefixWord ++ tailWord_7170783) baseStart_7170783 baseEnd_7170783 := by
    simpa [prefixWord, tailWord_7170783, baseEnd_7170783] using wordTrace_append hprefix tailTrace_7170783
  have hstable : (prefixWord ++ tailWord_7170783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170783).length < 2 ^ (prefixWord ++ tailWord_7170783).sum := by decide
  have hdescent : baseEnd_7170783 < baseStart_7170783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170797 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7170797 : Nat := 118140960795 + 7170797 * 2 ^ 59
def prefixEnd_7170797 : Nat := 4983230072969 + 3 ^ 40 * 7170797 * 2
def baseEnd_7170797 : Nat := 3682065536818685957459611

theorem tailTrace_7170797 : CollatzResearch.WordTrace tailWord_7170797 prefixEnd_7170797 3682065536818685957459611 := by
  unfold tailWord_7170797
  simp only [CollatzResearch.WordTrace]
  refine ⟨261540453002434618471382645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174360302001623078980921763 261540453002434618471382645)
  ·
    refine ⟨24519417468978245481692123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261540453002434618471382645 24519417468978245481692123)
    ·
      refine ⟨36779126203467368222538185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24519417468978245481692123 36779126203467368222538185)
      ·
        refine ⟨27584344652600526166903639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36779126203467368222538185 27584344652600526166903639)
        ·
          refine ⟨41376516978900789250355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27584344652600526166903639 41376516978900789250355459)
          ·
            refine ⟨62064775468351183875533189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41376516978900789250355459 62064775468351183875533189)
            ·
              refine ⟨11637145400315846976662473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62064775468351183875533189 11637145400315846976662473)
              ·
                refine ⟨8727859050236885232496855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11637145400315846976662473 8727859050236885232496855)
                ·
                  refine ⟨13091788575355327848745283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727859050236885232496855 13091788575355327848745283)
                  ·
                    refine ⟨19637682863032991773117925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13091788575355327848745283 19637682863032991773117925)
                    ·
                      refine ⟨3682065536818685957459611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19637682863032991773117925 3682065536818685957459611)
                      ·
                        rfl

theorem cell23_7170797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7170797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170797 prefixEnd_7170797 := by exact prefixLift 7170797
  have htrace : WordTrace (prefixWord ++ tailWord_7170797) baseStart_7170797 baseEnd_7170797 := by
    simpa [prefixWord, tailWord_7170797, baseEnd_7170797] using wordTrace_append hprefix tailTrace_7170797
  have hstable : (prefixWord ++ tailWord_7170797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170797).length < 2 ^ (prefixWord ++ tailWord_7170797).sum := by decide
  have hdescent : baseEnd_7170797 < baseStart_7170797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170831 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 1, 2, 2]
def baseStart_7170831 : Nat := 118140960795 + 7170831 * 2 ^ 59
def prefixEnd_7170831 : Nat := 4983230072969 + 3 ^ 40 * 7170831 * 2
def baseEnd_7170831 : Nat := 3682082995160938824434455

theorem tailTrace_7170831 : CollatzResearch.WordTrace tailWord_7170831 prefixEnd_7170831 3682082995160938824434455 := by
  unfold tailWord_7170831
  simp only [CollatzResearch.WordTrace]
  refine ⟨261541693084311442278120347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174361128722874294852080231 261541693084311442278120347)
  ·
    refine ⟨392312539626467163417180521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261541693084311442278120347 392312539626467163417180521)
    ·
      refine ⟨294234404719850372562885391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392312539626467163417180521 294234404719850372562885391)
      ·
        refine ⟨441351607079775558844328087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294234404719850372562885391 441351607079775558844328087)
        ·
          refine ⟨662027410619663338266492131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441351607079775558844328087 662027410619663338266492131)
          ·
            refine ⟨993041115929495007399738197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662027410619663338266492131 993041115929495007399738197)
            ·
              refine ⟨5818600288649384808982841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 993041115929495007399738197 5818600288649384808982841)
              ·
                refine ⟨4363950216487038606737131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818600288649384808982841 4363950216487038606737131)
                ·
                  refine ⟨6545925324730557910105697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363950216487038606737131 6545925324730557910105697)
                  ·
                    refine ⟨4909443993547918432579273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545925324730557910105697 4909443993547918432579273)
                    ·
                      refine ⟨3682082995160938824434455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909443993547918432579273 3682082995160938824434455)
                      ·
                        rfl

theorem cell23_7170831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 2, 2].length) (baseStart_7170831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170831 prefixEnd_7170831 := by exact prefixLift 7170831
  have htrace : WordTrace (prefixWord ++ tailWord_7170831) baseStart_7170831 baseEnd_7170831 := by
    simpa [prefixWord, tailWord_7170831, baseEnd_7170831] using wordTrace_append hprefix tailTrace_7170831
  have hstable : (prefixWord ++ tailWord_7170831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170831).length < 2 ^ (prefixWord ++ tailWord_7170831).sum := by decide
  have hdescent : baseEnd_7170831 < baseStart_7170831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170840 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7170840 : Nat := 118140960795 + 7170840 * 2 ^ 59
def prefixEnd_7170840 : Nat := 4983230072969 + 3 ^ 40 * 7170840 * 2
def baseEnd_7170840 : Nat := 3682087616486829289221913

theorem tailTrace_7170840 : CollatzResearch.WordTrace tailWord_7170840 prefixEnd_7170840 3682087616486829289221913 := by
  unfold tailWord_7170840
  simp only [CollatzResearch.WordTrace]
  refine ⟨130771010670639418407598987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174361347560852557876798649 130771010670639418407598987)
  ·
    refine ⟨196156516005959127611398481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130771010670639418407598987 196156516005959127611398481)
    ·
      refine ⟨147117387004469345708548861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196156516005959127611398481 147117387004469345708548861)
      ·
        refine ⟨55169020126676004640705823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147117387004469345708548861 55169020126676004640705823)
        ·
          refine ⟨82753530190014006961058735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55169020126676004640705823 82753530190014006961058735)
          ·
            refine ⟨124130295285021010441588103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82753530190014006961058735 124130295285021010441588103)
            ·
              refine ⟨186195442927531515662382155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124130295285021010441588103 186195442927531515662382155)
              ·
                refine ⟨279293164391297273493573233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186195442927531515662382155 279293164391297273493573233)
                ·
                  refine ⟨209469873293472955120179925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279293164391297273493573233 209469873293472955120179925)
                  ·
                    refine ⟨4909450155315772385629217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209469873293472955120179925 4909450155315772385629217)
                    ·
                      refine ⟨3682087616486829289221913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909450155315772385629217 3682087616486829289221913)
                      ·
                        rfl

theorem cell23_7170840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7170840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170840 prefixEnd_7170840 := by exact prefixLift 7170840
  have htrace : WordTrace (prefixWord ++ tailWord_7170840) baseStart_7170840 baseEnd_7170840 := by
    simpa [prefixWord, tailWord_7170840, baseEnd_7170840] using wordTrace_append hprefix tailTrace_7170840
  have hstable : (prefixWord ++ tailWord_7170840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170840).length < 2 ^ (prefixWord ++ tailWord_7170840).sum := by decide
  have hdescent : baseEnd_7170840 < baseStart_7170840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170940 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_7170940 : Nat := 118140960795 + 7170940 * 2 ^ 59
def prefixEnd_7170940 : Nat := 4983230072969 + 3 ^ 40 * 7170940 * 2
def baseEnd_7170940 : Nat := 1227379654850759632657151

theorem tailTrace_7170940 : CollatzResearch.WordTrace tailWord_7170940 prefixEnd_7170940 1227379654850759632657151 := by
  unfold tailWord_7170940
  simp only [CollatzResearch.WordTrace]
  refine ⟨130772834320458276946919137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174363779093944369262558849 130772834320458276946919137)
  ·
    refine ⟨98079625740343707710189353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130772834320458276946919137 98079625740343707710189353)
    ·
      refine ⟨73559719305257780782642015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98079625740343707710189353 73559719305257780782642015)
      ·
        refine ⟨110339578957886671173963023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73559719305257780782642015 110339578957886671173963023)
        ·
          refine ⟨165509368436830006760944535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110339578957886671173963023 165509368436830006760944535)
          ·
            refine ⟨248264052655245010141416803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165509368436830006760944535 248264052655245010141416803)
            ·
              refine ⟨372396078982867515212125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248264052655245010141416803 372396078982867515212125205)
              ·
                refine ⟨17456066202321914775568369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372396078982867515212125205 17456066202321914775568369)
                ·
                  refine ⟨13092049651741436081676277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17456066202321914775568369 13092049651741436081676277)
                  ·
                    refine ⟨1227379654850759632657151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13092049651741436081676277 1227379654850759632657151)
                    ·
                      rfl

theorem cell23_7170940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_7170940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170940 prefixEnd_7170940 := by exact prefixLift 7170940
  have htrace : WordTrace (prefixWord ++ tailWord_7170940) baseStart_7170940 baseEnd_7170940 := by
    simpa [prefixWord, tailWord_7170940, baseEnd_7170940] using wordTrace_append hprefix tailTrace_7170940
  have hstable : (prefixWord ++ tailWord_7170940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170940).length < 2 ^ (prefixWord ++ tailWord_7170940).sum := by decide
  have hdescent : baseEnd_7170940 < baseStart_7170940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170977 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7170977 : Nat := 118140960795 + 7170977 * 2 ^ 59
def prefixEnd_7170977 : Nat := 4983230072969 + 3 ^ 40 * 7170977 * 2
def baseEnd_7170977 : Nat := 3682157963336495253208783

theorem tailTrace_7170977 : CollatzResearch.WordTrace tailWord_7170977 prefixEnd_7170977 3682157963336495253208783 := by
  unfold tailWord_7170977
  simp only [CollatzResearch.WordTrace]
  refine ⟨261547018141782509212935185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174364678761188339475290123 261547018141782509212935185)
  ·
    refine ⟨196160263606336881909701389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261547018141782509212935185 196160263606336881909701389)
    ·
      refine ⟨73560098852376330716138021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196160263606336881909701389 73560098852376330716138021)
      ·
        refine ⟨13792518534820562009275879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73560098852376330716138021 13792518534820562009275879)
        ·
          refine ⟨20688777802230843013913819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13792518534820562009275879 20688777802230843013913819)
          ·
            refine ⟨31033166703346264520870729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20688777802230843013913819 31033166703346264520870729)
            ·
              refine ⟨23274875027509698390653047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31033166703346264520870729 23274875027509698390653047)
              ·
                refine ⟨34912312541264547585979571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23274875027509698390653047 34912312541264547585979571)
                ·
                  refine ⟨52368468811896821378969357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34912312541264547585979571 52368468811896821378969357)
                  ·
                    refine ⟨19638175804461308017113509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52368468811896821378969357 19638175804461308017113509)
                    ·
                      refine ⟨3682157963336495253208783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19638175804461308017113509 3682157963336495253208783)
                      ·
                        rfl

theorem cell23_7170977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7170977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7170977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7170977 prefixEnd_7170977 := by exact prefixLift 7170977
  have htrace : WordTrace (prefixWord ++ tailWord_7170977) baseStart_7170977 baseEnd_7170977 := by
    simpa [prefixWord, tailWord_7170977, baseEnd_7170977] using wordTrace_append hprefix tailTrace_7170977
  have hstable : (prefixWord ++ tailWord_7170977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170977).length < 2 ^ (prefixWord ++ tailWord_7170977).sum := by decide
  have hdescent : baseEnd_7170977 < baseStart_7170977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171000 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 8]
def baseStart_7171000 : Nat := 118140960795 + 7171000 * 2 ^ 59
def prefixEnd_7171000 : Nat := 4983230072969 + 3 ^ 40 * 7171000 * 2
def baseEnd_7171000 : Nat := 409129974821283184802353

theorem tailTrace_7171000 : CollatzResearch.WordTrace tailWord_7171000 prefixEnd_7171000 409129974821283184802353 := by
  unfold tailWord_7171000
  simp only [CollatzResearch.WordTrace]
  refine ⟨130773928510349592070511227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174365238013799456094014969 130773928510349592070511227)
  ·
    refine ⟨196160892765524388105766841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130773928510349592070511227 196160892765524388105766841)
    ·
      refine ⟨147120669574143291079325131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196160892765524388105766841 147120669574143291079325131)
      ·
        refine ⟨220681004361214936618987697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147120669574143291079325131 220681004361214936618987697)
        ·
          refine ⟨165510753270911202464240773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220681004361214936618987697 165510753270911202464240773)
          ·
            refine ⟨31033266238295850462045145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165510753270911202464240773 31033266238295850462045145)
            ·
              refine ⟨23274949678721887846533859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31033266238295850462045145 23274949678721887846533859)
              ·
                refine ⟨34912424518082831769800789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23274949678721887846533859 34912424518082831769800789)
                ·
                  refine ⟨409129974821283184802353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34912424518082831769800789 409129974821283184802353)
                  ·
                    rfl

theorem cell23_7171000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_7171000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171000 prefixEnd_7171000 := by exact prefixLift 7171000
  have htrace : WordTrace (prefixWord ++ tailWord_7171000) baseStart_7171000 baseEnd_7171000 := by
    simpa [prefixWord, tailWord_7171000, baseEnd_7171000] using wordTrace_append hprefix tailTrace_7171000
  have hstable : (prefixWord ++ tailWord_7171000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171000).length < 2 ^ (prefixWord ++ tailWord_7171000).sum := by decide
  have hdescent : baseEnd_7171000 < baseStart_7171000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171067 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 6, 2]
def baseStart_7171067 : Nat := 118140960795 + 7171067 * 2 ^ 59
def prefixEnd_7171067 : Nat := 4983230072969 + 3 ^ 40 * 7171067 * 2
def baseEnd_7171067 : Nat := 3682204176595399901083369

theorem tailTrace_7171067 : CollatzResearch.WordTrace tailWord_7171067 prefixEnd_7171067 3682204176595399901083369 := by
  unfold tailWord_7171067
  simp only [CollatzResearch.WordTrace]
  refine ⟨261550300711456454583711455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174366867140970969722474303 261550300711456454583711455)
  ·
    refine ⟨392325451067184681875567183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261550300711456454583711455 392325451067184681875567183)
    ·
      refine ⟨588488176600777022813350775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392325451067184681875567183 588488176600777022813350775)
      ·
        refine ⟨882732264901165534220026163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588488176600777022813350775 882732264901165534220026163)
        ·
          refine ⟨1324098397351748301330039245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882732264901165534220026163 1324098397351748301330039245)
          ·
            refine ⟨496536899006905612998764717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324098397351748301330039245 496536899006905612998764717)
            ·
              refine ⟨186201337127589604874536769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496536899006905612998764717 186201337127589604874536769)
              ·
                refine ⟨139651002845692203655902577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186201337127589604874536769 139651002845692203655902577)
                ·
                  refine ⟨104738252134269152741926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139651002845692203655902577 104738252134269152741926933)
                  ·
                    refine ⟨4909605568793866534777825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104738252134269152741926933 4909605568793866534777825)
                    ·
                      refine ⟨3682204176595399901083369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909605568793866534777825 3682204176595399901083369)
                      ·
                        rfl

theorem cell23_7171067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6, 2].length) (baseStart_7171067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171067 prefixEnd_7171067 := by exact prefixLift 7171067
  have htrace : WordTrace (prefixWord ++ tailWord_7171067) baseStart_7171067 baseEnd_7171067 := by
    simpa [prefixWord, tailWord_7171067, baseEnd_7171067] using wordTrace_append hprefix tailTrace_7171067
  have hstable : (prefixWord ++ tailWord_7171067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171067).length < 2 ^ (prefixWord ++ tailWord_7171067).sum := by decide
  have hdescent : baseEnd_7171067 < baseStart_7171067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171077 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_7171077 : Nat := 118140960795 + 7171077 * 2 ^ 59
def prefixEnd_7171077 : Nat := 4983230072969 + 3 ^ 40 * 7171077 * 2
def baseEnd_7171077 : Nat := 1227403103800648287319441

theorem tailTrace_7171077 : CollatzResearch.WordTrace tailWord_7171077 prefixEnd_7171077 1227403103800648287319441 := by
  unfold tailWord_7171077
  simp only [CollatzResearch.WordTrace]
  refine ⟨261550665441420226291575485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174367110294280150861050323 261550665441420226291575485)
  ·
    refine ⟨98081499540532584859340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261550665441420226291575485 98081499540532584859340807)
    ·
      refine ⟨147122249310798877289011211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98081499540532584859340807 147122249310798877289011211)
      ·
        refine ⟨220683373966198315933516817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147122249310798877289011211 220683373966198315933516817)
        ·
          refine ⟨165512530474648736950137613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220683373966198315933516817 165512530474648736950137613)
          ·
            refine ⟨62067198927993276356301605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165512530474648736950137613 62067198927993276356301605)
            ·
              refine ⟨11637599798998739316806551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62067198927993276356301605 11637599798998739316806551)
              ·
                refine ⟨17456399698498108975209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11637599798998739316806551 17456399698498108975209827)
                ·
                  refine ⟨26184599547747163462814741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17456399698498108975209827 26184599547747163462814741)
                  ·
                    refine ⟨1227403103800648287319441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26184599547747163462814741 1227403103800648287319441)
                    ·
                      rfl

theorem cell23_7171077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_7171077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171077 prefixEnd_7171077 := by exact prefixLift 7171077
  have htrace : WordTrace (prefixWord ++ tailWord_7171077) baseStart_7171077 baseEnd_7171077 := by
    simpa [prefixWord, tailWord_7171077, baseEnd_7171077] using wordTrace_append hprefix tailTrace_7171077
  have hstable : (prefixWord ++ tailWord_7171077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171077).length < 2 ^ (prefixWord ++ tailWord_7171077).sum := by decide
  have hdescent : baseEnd_7171077 < baseStart_7171077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171097 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_7171097 : Nat := 118140960795 + 7171097 * 2 ^ 59
def prefixEnd_7171097 : Nat := 4983230072969 + 3 ^ 40 * 7171097 * 2
def baseEnd_7171097 : Nat := 3682219581015034783708231

theorem tailTrace_7171097 : CollatzResearch.WordTrace tailWord_7171097 prefixEnd_7171097 3682219581015034783708231 := by
  unfold tailWord_7171097
  simp only [CollatzResearch.WordTrace]
  refine ⟨261551394901347769707303545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174367596600898513138202363 261551394901347769707303545)
  ·
    refine ⟨196163546176010827280477659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261551394901347769707303545 196163546176010827280477659)
    ·
      refine ⟨294245319264016240920716489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196163546176010827280477659 294245319264016240920716489)
      ·
        refine ⟨220683989448012180690537367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294245319264016240920716489 220683989448012180690537367)
        ·
          refine ⟨331025984172018271035806051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220683989448012180690537367 331025984172018271035806051)
          ·
            refine ⟨496538976258027406553709077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331025984172018271035806051 496538976258027406553709077)
            ·
              refine ⟨23275264512095034682205113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496538976258027406553709077 23275264512095034682205113)
              ·
                refine ⟨17456448384071276011653835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23275264512095034682205113 17456448384071276011653835)
                ·
                  refine ⟨26184672576106914017480753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17456448384071276011653835 26184672576106914017480753)
                  ·
                    refine ⟨19638504432080185513110565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26184672576106914017480753 19638504432080185513110565)
                    ·
                      refine ⟨3682219581015034783708231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19638504432080185513110565 3682219581015034783708231)
                      ·
                        rfl

theorem cell23_7171097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_7171097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171097 prefixEnd_7171097 := by exact prefixLift 7171097
  have htrace : WordTrace (prefixWord ++ tailWord_7171097) baseStart_7171097 baseEnd_7171097 := by
    simpa [prefixWord, tailWord_7171097, baseEnd_7171097] using wordTrace_append hprefix tailTrace_7171097
  have hstable : (prefixWord ++ tailWord_7171097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171097).length < 2 ^ (prefixWord ++ tailWord_7171097).sum := by decide
  have hdescent : baseEnd_7171097 < baseStart_7171097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171101 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7171101 : Nat := 118140960795 + 7171101 * 2 ^ 59
def prefixEnd_7171101 : Nat := 4983230072969 + 3 ^ 40 * 7171101 * 2
def baseEnd_7171101 : Nat := 3682221634937652768058213

theorem tailTrace_7171101 : CollatzResearch.WordTrace tailWord_7171101 prefixEnd_7171101 3682221634937652768058213 := by
  unfold tailWord_7171101
  simp only [CollatzResearch.WordTrace]
  refine ⟨261551540793333278390449157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174367693862222185593632771 261551540793333278390449157)
  ·
    refine ⟨49040913898749989698209217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261551540793333278390449157 49040913898749989698209217)
    ·
      refine ⟨36780685424062492273656913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49040913898749989698209217 36780685424062492273656913)
      ·
        refine ⟨27585514068046869205242685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36780685424062492273656913 27585514068046869205242685)
        ·
          refine ⟨10344567775517575951966007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27585514068046869205242685 10344567775517575951966007)
          ·
            refine ⟨15516851663276363927949011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344567775517575951966007 15516851663276363927949011)
            ·
              refine ⟨23275277494914545891923517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516851663276363927949011 23275277494914545891923517)
              ·
                refine ⟨8728229060592954709471319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23275277494914545891923517 8728229060592954709471319)
                ·
                  refine ⟨13092343590889432064206979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8728229060592954709471319 13092343590889432064206979)
                  ·
                    refine ⟨19638515386334148096310469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13092343590889432064206979 19638515386334148096310469)
                    ·
                      refine ⟨3682221634937652768058213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19638515386334148096310469 3682221634937652768058213)
                      ·
                        rfl

theorem cell23_7171101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7171101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171101 prefixEnd_7171101 := by exact prefixLift 7171101
  have htrace : WordTrace (prefixWord ++ tailWord_7171101) baseStart_7171101 baseEnd_7171101 := by
    simpa [prefixWord, tailWord_7171101, baseEnd_7171101] using wordTrace_append hprefix tailTrace_7171101
  have hstable : (prefixWord ++ tailWord_7171101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171101).length < 2 ^ (prefixWord ++ tailWord_7171101).sum := by decide
  have hdescent : baseEnd_7171101 < baseStart_7171101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171111 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7171111 : Nat := 118140960795 + 7171111 * 2 ^ 59
def prefixEnd_7171111 : Nat := 4983230072969 + 3 ^ 40 * 7171111 * 2
def baseEnd_7171111 : Nat := 1227408923248065909644389

theorem tailTrace_7171111 : CollatzResearch.WordTrace tailWord_7171111 prefixEnd_7171111 1227408923248065909644389 := by
  unfold tailWord_7171111
  simp only [CollatzResearch.WordTrace]
  refine ⟨261551905523297050098313187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174367937015531366732208791 261551905523297050098313187)
  ·
    refine ⟨392327858284945575147469781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261551905523297050098313187 392327858284945575147469781)
    ·
      refine ⟨9195184178553411917518823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 392327858284945575147469781 9195184178553411917518823)
      ·
        refine ⟨13792776267830117876278235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195184178553411917518823 13792776267830117876278235)
        ·
          refine ⟨20689164401745176814417353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13792776267830117876278235 20689164401745176814417353)
          ·
            refine ⟨15516873301308882610813015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20689164401745176814417353 15516873301308882610813015)
            ·
              refine ⟨23275309951963323916219523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516873301308882610813015 23275309951963323916219523)
              ·
                refine ⟨34912964927944985874329285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23275309951963323916219523 34912964927944985874329285)
                ·
                  refine ⟨6546180923989684851436741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34912964927944985874329285 6546180923989684851436741)
                  ·
                    refine ⟨1227408923248065909644389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546180923989684851436741 1227408923248065909644389)
                    ·
                      rfl

theorem cell23_7171111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7171111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171111 prefixEnd_7171111 := by exact prefixLift 7171111
  have htrace : WordTrace (prefixWord ++ tailWord_7171111) baseStart_7171111 baseEnd_7171111 := by
    simpa [prefixWord, tailWord_7171111, baseEnd_7171111] using wordTrace_append hprefix tailTrace_7171111
  have hstable : (prefixWord ++ tailWord_7171111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171111).length < 2 ^ (prefixWord ++ tailWord_7171111).sum := by decide
  have hdescent : baseEnd_7171111 < baseStart_7171111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171118 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7171118 : Nat := 118140960795 + 7171118 * 2 ^ 59
def prefixEnd_7171118 : Nat := 4983230072969 + 3 ^ 40 * 7171118 * 2
def baseEnd_7171118 : Nat := 3682230364108779201545635

theorem tailTrace_7171118 : CollatzResearch.WordTrace tailWord_7171118 prefixEnd_7171118 3682230364108779201545635 := by
  unfold tailWord_7171118
  simp only [CollatzResearch.WordTrace]
  refine ⟨32694020104283961286727251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174368107222847793529212005 32694020104283961286727251)
  ·
    refine ⟨49041030156425941930090877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32694020104283961286727251 49041030156425941930090877)
    ·
      refine ⟨18390386308659728223784079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49041030156425941930090877 18390386308659728223784079)
      ·
        refine ⟨27585579462989592335676119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18390386308659728223784079 27585579462989592335676119)
        ·
          refine ⟨41378369194484388503514179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27585579462989592335676119 41378369194484388503514179)
          ·
            refine ⟨62067553791726582755271269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41378369194484388503514179 62067553791726582755271269)
            ·
              refine ⟨11637666335948734266613363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62067553791726582755271269 11637666335948734266613363)
              ·
                refine ⟨17456499503923101399920045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11637666335948734266613363 17456499503923101399920045)
                ·
                  refine ⟨6546187313971163024970017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17456499503923101399920045 6546187313971163024970017)
                  ·
                    refine ⟨4909640485478372268727513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6546187313971163024970017 4909640485478372268727513)
                    ·
                      refine ⟨3682230364108779201545635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909640485478372268727513 3682230364108779201545635)
                      ·
                        rfl

theorem cell23_7171118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7171118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171118 prefixEnd_7171118 := by exact prefixLift 7171118
  have htrace : WordTrace (prefixWord ++ tailWord_7171118) baseStart_7171118 baseEnd_7171118 := by
    simpa [prefixWord, tailWord_7171118, baseEnd_7171118] using wordTrace_append hprefix tailTrace_7171118
  have hstable : (prefixWord ++ tailWord_7171118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171118).length < 2 ^ (prefixWord ++ tailWord_7171118).sum := by decide
  have hdescent : baseEnd_7171118 < baseStart_7171118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171158 : List Nat := [5, 2, 2, 1, 3, 1, 9]
def baseStart_7171158 : Nat := 118140960795 + 7171158 * 2 ^ 59
def prefixEnd_7171158 : Nat := 4983230072969 + 3 ^ 40 * 7171158 * 2
def baseEnd_7171158 : Nat := 45459887695493321543771

theorem tailTrace_7171158 : CollatzResearch.WordTrace tailWord_7171158 prefixEnd_7171158 45459887695493321543771 := by
  unfold tailWord_7171158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347101234632923570329633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174369079836084518083516085 16347101234632923570329633)
  ·
    refine ⟨12260325925974692677747225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16347101234632923570329633 12260325925974692677747225)
    ·
      refine ⟨9195244444481019508310419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12260325925974692677747225 9195244444481019508310419)
      ·
        refine ⟨13792866666721529262465629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195244444481019508310419 13792866666721529262465629)
        ·
          refine ⟨5172325000020573473424611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13792866666721529262465629 5172325000020573473424611)
          ·
            refine ⟨7758487500030860210136917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172325000020573473424611 7758487500030860210136917)
            ·
              refine ⟨45459887695493321543771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7758487500030860210136917 45459887695493321543771)
              ·
                rfl

theorem cell23_7171158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 9].length) (baseStart_7171158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171158 prefixEnd_7171158 := by exact prefixLift 7171158
  have htrace : WordTrace (prefixWord ++ tailWord_7171158) baseStart_7171158 baseEnd_7171158 := by
    simpa [prefixWord, tailWord_7171158, baseEnd_7171158] using wordTrace_append hprefix tailTrace_7171158
  have hstable : (prefixWord ++ tailWord_7171158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171158).length < 2 ^ (prefixWord ++ tailWord_7171158).sum := by decide
  have hdescent : baseEnd_7171158 < baseStart_7171158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171197 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 9]
def baseStart_7171197 : Nat := 118140960795 + 7171197 * 2 ^ 59
def prefixEnd_7171197 : Nat := 4983230072969 + 3 ^ 40 * 7171197 * 2
def baseEnd_7171197 : Nat := 409141214342276043606419

theorem tailTrace_7171197 : CollatzResearch.WordTrace tailWord_7171197 prefixEnd_7171197 409141214342276043606419 := by
  unfold tailWord_7171197
  simp only [CollatzResearch.WordTrace]
  refine ⟨261555042200985486785943845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174370028133990324523962563 261555042200985486785943845)
  ·
    refine ⟨49041570412684778772364471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261555042200985486785943845 49041570412684778772364471)
    ·
      refine ⟨73562355619027168158546707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49041570412684778772364471 73562355619027168158546707)
      ·
        refine ⟨110343533428540752237820061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73562355619027168158546707 110343533428540752237820061)
        ·
          refine ⟨41378825035702782089182523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110343533428540752237820061 41378825035702782089182523)
          ·
            refine ⟨62068237553554173133773785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41378825035702782089182523 62068237553554173133773785)
            ·
              refine ⟨46551178165165629850330339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62068237553554173133773785 46551178165165629850330339)
              ·
                refine ⟨69826767247748444775495509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46551178165165629850330339 69826767247748444775495509)
                ·
                  refine ⟨409141214342276043606419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69826767247748444775495509 409141214342276043606419)
                  ·
                    rfl

theorem cell23_7171197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_7171197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171197 prefixEnd_7171197 := by exact prefixLift 7171197
  have htrace : WordTrace (prefixWord ++ tailWord_7171197) baseStart_7171197 baseEnd_7171197 := by
    simpa [prefixWord, tailWord_7171197, baseEnd_7171197] using wordTrace_append hprefix tailTrace_7171197
  have hstable : (prefixWord ++ tailWord_7171197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171197).length < 2 ^ (prefixWord ++ tailWord_7171197).sum := by decide
  have hdescent : baseEnd_7171197 < baseStart_7171197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171208 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7171208 : Nat := 118140960795 + 7171208 * 2 ^ 59
def prefixEnd_7171208 : Nat := 4983230072969 + 3 ^ 40 * 7171208 * 2
def baseEnd_7171208 : Nat := 3682276577367683849420221

theorem tailTrace_7171208 : CollatzResearch.WordTrace tailWord_7171208 prefixEnd_7171208 3682276577367683849420221 := by
  unfold tailWord_7171208
  simp only [CollatzResearch.WordTrace]
  refine ⟨130777721701972817832297139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174370295602630423776396185 130777721701972817832297139)
  ·
    refine ⟨196166582552959226748445709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130777721701972817832297139 196166582552959226748445709)
    ·
      refine ⟨73562468457359710030667141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196166582552959226748445709 73562468457359710030667141)
      ·
        refine ⟨13792962835754945630750089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73562468457359710030667141 13792962835754945630750089)
        ·
          refine ⟨10344722126816209223062567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13792962835754945630750089 10344722126816209223062567)
          ·
            refine ⟨15517083190224313834593851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344722126816209223062567 15517083190224313834593851)
            ·
              refine ⟨23275624785336470751890777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15517083190224313834593851 23275624785336470751890777)
              ·
                refine ⟨17456718589002353063918083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23275624785336470751890777 17456718589002353063918083)
                ·
                  refine ⟨26185077883503529595877125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17456718589002353063918083 26185077883503529595877125)
                  ·
                    refine ⟨4909702103156911799226961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26185077883503529595877125 4909702103156911799226961)
                    ·
                      refine ⟨3682276577367683849420221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909702103156911799226961 3682276577367683849420221)
                      ·
                        rfl

theorem cell23_7171208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7171208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171208 prefixEnd_7171208 := by exact prefixLift 7171208
  have htrace : WordTrace (prefixWord ++ tailWord_7171208) baseStart_7171208 baseEnd_7171208 := by
    simpa [prefixWord, tailWord_7171208, baseEnd_7171208] using wordTrace_append hprefix tailTrace_7171208
  have hstable : (prefixWord ++ tailWord_7171208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171208).length < 2 ^ (prefixWord ++ tailWord_7171208).sum := by decide
  have hdescent : baseEnd_7171208 < baseStart_7171208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171267 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_7171267 : Nat := 118140960795 + 7171267 * 2 ^ 59
def prefixEnd_7171267 : Nat := 4983230072969 + 3 ^ 40 * 7171267 * 2
def baseEnd_7171267 : Nat := 3682306872726299118582449

theorem tailTrace_7171267 : CollatzResearch.WordTrace tailWord_7171267 prefixEnd_7171267 3682306872726299118582449 := by
  unfold tailWord_7171267
  simp only [CollatzResearch.WordTrace]
  refine ⟨261557595310731888740992055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174371730207154592493994703 261557595310731888740992055)
  ·
    refine ⟨392336392966097833111488083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261557595310731888740992055 392336392966097833111488083)
    ·
      refine ⟨588504589449146749667232125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392336392966097833111488083 588504589449146749667232125)
      ·
        refine ⟨220689221043430031125212047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588504589449146749667232125 220689221043430031125212047)
        ·
          refine ⟨331033831565145046687818071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220689221043430031125212047 331033831565145046687818071)
          ·
            refine ⟨496550747347717570031727107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331033831565145046687818071 496550747347717570031727107)
            ·
              refine ⟨744826121021576355047590661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496550747347717570031727107 744826121021576355047590661)
              ·
                refine ⟨139654897691545566571423249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744826121021576355047590661 139654897691545566571423249)
                ·
                  refine ⟨104741173268659174928567437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139654897691545566571423249 104741173268659174928567437)
                  ·
                    refine ⟨39277939975747190598212789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104741173268659174928567437 39277939975747190598212789)
                    ·
                      refine ⟨3682306872726299118582449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39277939975747190598212789 3682306872726299118582449)
                      ·
                        rfl

theorem cell23_7171267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_7171267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171267 prefixEnd_7171267 := by exact prefixLift 7171267
  have htrace : WordTrace (prefixWord ++ tailWord_7171267) baseStart_7171267 baseEnd_7171267 := by
    simpa [prefixWord, tailWord_7171267, baseEnd_7171267] using wordTrace_append hprefix tailTrace_7171267
  have hstable : (prefixWord ++ tailWord_7171267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171267).length < 2 ^ (prefixWord ++ tailWord_7171267).sum := by decide
  have hdescent : baseEnd_7171267 < baseStart_7171267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171368 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7171368 : Nat := 118140960795 + 7171368 * 2 ^ 59
def prefixEnd_7171368 : Nat := 4983230072969 + 3 ^ 40 * 7171368 * 2
def baseEnd_7171368 : Nat := 1227452911424134407806495

theorem tailTrace_7171368 : CollatzResearch.WordTrace tailWord_7171368 prefixEnd_7171368 1227452911424134407806495 := by
  unfold tailWord_7171368
  simp only [CollatzResearch.WordTrace]
  refine ⟨130780639541682991495209379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174374186055577321993612505 130780639541682991495209379)
  ·
    refine ⟨196170959312524487242814069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130780639541682991495209379 196170959312524487242814069)
    ·
      refine ⟨18391027435549170679013819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196170959312524487242814069 18391027435549170679013819)
      ·
        refine ⟨27586541153323756018520729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18391027435549170679013819 27586541153323756018520729)
        ·
          refine ⟨20689905864992817013890547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27586541153323756018520729 20689905864992817013890547)
          ·
            refine ⟨31034858797489225520835821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20689905864992817013890547 31034858797489225520835821)
            ·
              refine ⟨11638072049058459570313433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31034858797489225520835821 11638072049058459570313433)
              ·
                refine ⟨8728554036793844677735075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11638072049058459570313433 8728554036793844677735075)
                ·
                  refine ⟨13092831055190767016602613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8728554036793844677735075 13092831055190767016602613)
                  ·
                    refine ⟨1227452911424134407806495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13092831055190767016602613 1227452911424134407806495)
                    ·
                      rfl

theorem cell23_7171368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7171368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171368 prefixEnd_7171368 := by exact prefixLift 7171368
  have htrace : WordTrace (prefixWord ++ tailWord_7171368) baseStart_7171368 baseEnd_7171368 := by
    simpa [prefixWord, tailWord_7171368, baseEnd_7171368] using wordTrace_append hprefix tailTrace_7171368
  have hstable : (prefixWord ++ tailWord_7171368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171368).length < 2 ^ (prefixWord ++ tailWord_7171368).sum := by decide
  have hdescent : baseEnd_7171368 < baseStart_7171368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171381 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7171381 : Nat := 118140960795 + 7171381 * 2 ^ 59
def prefixEnd_7171381 : Nat := 4983230072969 + 3 ^ 40 * 7171381 * 2
def baseEnd_7171381 : Nat := 1227455136506970557518975

theorem tailTrace_7171381 : CollatzResearch.WordTrace tailWord_7171381 prefixEnd_7171381 1227455136506970557518975 := by
  unfold tailWord_7171381
  simp only [CollatzResearch.WordTrace]
  refine ⟨261561753232318886210641997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174374502154879257473761331 261561753232318886210641997)
  ·
    refine ⟨98085657462119582328990749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261561753232318886210641997 98085657462119582328990749)
    ·
      refine ⟨36782121548294843373371531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98085657462119582328990749 36782121548294843373371531)
      ·
        refine ⟨55173182322442265060057297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36782121548294843373371531 55173182322442265060057297)
        ·
          refine ⟨41379886741831698795042973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55173182322442265060057297 41379886741831698795042973)
          ·
            refine ⟨15517457528186887048141115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41379886741831698795042973 15517457528186887048141115)
            ·
              refine ⟨23276186292280330572211673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15517457528186887048141115 23276186292280330572211673)
              ·
                refine ⟨17457139719210247929158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23276186292280330572211673 17457139719210247929158755)
                ·
                  refine ⟨26185709578815371893738133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17457139719210247929158755 26185709578815371893738133)
                  ·
                    refine ⟨1227455136506970557518975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26185709578815371893738133 1227455136506970557518975)
                    ·
                      rfl

theorem cell23_7171381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7171381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171381 prefixEnd_7171381 := by exact prefixLift 7171381
  have htrace : WordTrace (prefixWord ++ tailWord_7171381) baseStart_7171381 baseEnd_7171381 := by
    simpa [prefixWord, tailWord_7171381, baseEnd_7171381] using wordTrace_append hprefix tailTrace_7171381
  have hstable : (prefixWord ++ tailWord_7171381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171381).length < 2 ^ (prefixWord ++ tailWord_7171381).sum := by decide
  have hdescent : baseEnd_7171381 < baseStart_7171381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171385 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_7171385 : Nat := 118140960795 + 7171385 * 2 ^ 59
def prefixEnd_7171385 : Nat := 4983230072969 + 3 ^ 40 * 7171385 * 2
def baseEnd_7171385 : Nat := 1227455821147843218968969

theorem tailTrace_7171385 : CollatzResearch.WordTrace tailWord_7171385 prefixEnd_7171385 1227455821147843218968969 := by
  unfold tailWord_7171385
  simp only [CollatzResearch.WordTrace]
  refine ⟨261561899124304394893787609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174374599416202929929191739 261561899124304394893787609)
  ·
    refine ⟨196171424343228296170340707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261561899124304394893787609 196171424343228296170340707)
    ·
      refine ⟨294257136514842444255511061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196171424343228296170340707 294257136514842444255511061)
      ·
        refine ⟨13793303274133239574477081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294257136514842444255511061 13793303274133239574477081)
        ·
          refine ⟨10344977455599929680857811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13793303274133239574477081 10344977455599929680857811)
          ·
            refine ⟨15517466183399894521286717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344977455599929680857811 15517466183399894521286717)
            ·
              refine ⟨5819049818774960445482519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15517466183399894521286717 5819049818774960445482519)
              ·
                refine ⟨8728574728162440668223779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819049818774960445482519 8728574728162440668223779)
                ·
                  refine ⟨13092862092243661002335669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8728574728162440668223779 13092862092243661002335669)
                  ·
                    refine ⟨1227455821147843218968969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13092862092243661002335669 1227455821147843218968969)
                    ·
                      rfl

theorem cell23_7171385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_7171385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171385 prefixEnd_7171385 := by exact prefixLift 7171385
  have htrace : WordTrace (prefixWord ++ tailWord_7171385) baseStart_7171385 baseEnd_7171385 := by
    simpa [prefixWord, tailWord_7171385, baseEnd_7171385] using wordTrace_append hprefix tailTrace_7171385
  have hstable : (prefixWord ++ tailWord_7171385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171385).length < 2 ^ (prefixWord ++ tailWord_7171385).sum := by decide
  have hdescent : baseEnd_7171385 < baseStart_7171385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171391 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_7171391 : Nat := 118140960795 + 7171391 * 2 ^ 59
def prefixEnd_7171391 : Nat := 4983230072969 + 3 ^ 40 * 7171391 * 2
def baseEnd_7171391 : Nat := 3682370544327456633431879

theorem tailTrace_7171391 : CollatzResearch.WordTrace tailWord_7171391 prefixEnd_7171391 3682370544327456633431879 := by
  unfold tailWord_7171391
  simp only [CollatzResearch.WordTrace]
  refine ⟨261562117962282657918506027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174374745308188438612337351 261562117962282657918506027)
  ·
    refine ⟨392343176943423986877759041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261562117962282657918506027 392343176943423986877759041)
    ·
      refine ⟨294257382707567990158319281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392343176943423986877759041 294257382707567990158319281)
      ·
        refine ⟨220693037030675992618739461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294257382707567990158319281 220693037030675992618739461)
        ·
          refine ⟨41379944443251748616013649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220693037030675992618739461 41379944443251748616013649)
          ·
            refine ⟨31034958332438811462010237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41379944443251748616013649 31034958332438811462010237)
            ·
              refine ⟨11638109374664554298253839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31034958332438811462010237 11638109374664554298253839)
              ·
                refine ⟨17457164061996831447380759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11638109374664554298253839 17457164061996831447380759)
                ·
                  refine ⟨26185746092995247171071139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17457164061996831447380759 26185746092995247171071139)
                  ·
                    refine ⟨39278619139492870756606709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26185746092995247171071139 39278619139492870756606709)
                    ·
                      refine ⟨3682370544327456633431879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39278619139492870756606709 3682370544327456633431879)
                      ·
                        rfl

theorem cell23_7171391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_7171391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171391 prefixEnd_7171391 := by exact prefixLift 7171391
  have htrace : WordTrace (prefixWord ++ tailWord_7171391) baseStart_7171391 baseEnd_7171391 := by
    simpa [prefixWord, tailWord_7171391, baseEnd_7171391] using wordTrace_append hprefix tailTrace_7171391
  have hstable : (prefixWord ++ tailWord_7171391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171391).length < 2 ^ (prefixWord ++ tailWord_7171391).sum := by decide
  have hdescent : baseEnd_7171391 < baseStart_7171391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171495 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_7171495 : Nat := 118140960795 + 7171495 * 2 ^ 59
def prefixEnd_7171495 : Nat := 4983230072969 + 3 ^ 40 * 7171495 * 2
def baseEnd_7171495 : Nat := 3682423946315524226531401

theorem tailTrace_7171495 : CollatzResearch.WordTrace tailWord_7171495 prefixEnd_7171495 3682423946315524226531401 := by
  unfold tailWord_7171495
  simp only [CollatzResearch.WordTrace]
  refine ⟨261565911153905883680291939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174377274102603922453527959 261565911153905883680291939)
  ·
    refine ⟨392348866730858825520437909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261565911153905883680291939 392348866730858825520437909)
    ·
      refine ⟨18391353128009007446270527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 392348866730858825520437909 18391353128009007446270527)
      ·
        refine ⟨27587029692013511169405791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18391353128009007446270527 27587029692013511169405791)
        ·
          refine ⟨41380544538020266754108687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27587029692013511169405791 41380544538020266754108687)
          ·
            refine ⟨62070816807030400131163031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41380544538020266754108687 62070816807030400131163031)
            ·
              refine ⟨93106225210545600196744547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62070816807030400131163031 93106225210545600196744547)
              ·
                refine ⟨139659337815818400295116821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93106225210545600196744547 139659337815818400295116821)
                ·
                  refine ⟨6546531460116487513833601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139659337815818400295116821 6546531460116487513833601)
                  ·
                    refine ⟨4909898595087365635375201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6546531460116487513833601 4909898595087365635375201)
                    ·
                      refine ⟨3682423946315524226531401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4909898595087365635375201 3682423946315524226531401)
                      ·
                        rfl

theorem cell23_7171495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_7171495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171495 prefixEnd_7171495 := by exact prefixLift 7171495
  have htrace : WordTrace (prefixWord ++ tailWord_7171495) baseStart_7171495 baseEnd_7171495 := by
    simpa [prefixWord, tailWord_7171495, baseEnd_7171495] using wordTrace_append hprefix tailTrace_7171495
  have hstable : (prefixWord ++ tailWord_7171495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171495).length < 2 ^ (prefixWord ++ tailWord_7171495).sum := by decide
  have hdescent : baseEnd_7171495 < baseStart_7171495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171541 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7171541 : Nat := 118140960795 + 7171541 * 2 ^ 59
def prefixEnd_7171541 : Nat := 4983230072969 + 3 ^ 40 * 7171541 * 2
def baseEnd_7171541 : Nat := 3682447566425631046556189

theorem tailTrace_7171541 : CollatzResearch.WordTrace tailWord_7171541 prefixEnd_7171541 3682447566425631046556189 := by
  unfold tailWord_7171541
  simp only [CollatzResearch.WordTrace]
  refine ⟨261567588911739233536466477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174378392607826155690977651 261567588911739233536466477)
  ·
    refine ⟨98087845841902212576174929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261567588911739233536466477 98087845841902212576174929)
    ·
      refine ⟨73565884381426659432131197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98087845841902212576174929 73565884381426659432131197)
      ·
        refine ⟨27587206643034997287049199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73565884381426659432131197 27587206643034997287049199)
        ·
          refine ⟨41380809964552495930573799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27587206643034997287049199 41380809964552495930573799)
          ·
            refine ⟨62071214946828743895860699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41380809964552495930573799 62071214946828743895860699)
            ·
              refine ⟨93106822420243115843791049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62071214946828743895860699 93106822420243115843791049)
              ·
                refine ⟨69830116815182336882843287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93106822420243115843791049 69830116815182336882843287)
                ·
                  refine ⟨104745175222773505324264931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69830116815182336882843287 104745175222773505324264931)
                  ·
                    refine ⟨157117762834160257986397397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104745175222773505324264931 157117762834160257986397397)
                    ·
                      refine ⟨3682447566425631046556189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157117762834160257986397397 3682447566425631046556189)
                      ·
                        rfl

theorem cell23_7171541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7171541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171541 prefixEnd_7171541 := by exact prefixLift 7171541
  have htrace : WordTrace (prefixWord ++ tailWord_7171541) baseStart_7171541 baseEnd_7171541 := by
    simpa [prefixWord, tailWord_7171541, baseEnd_7171541] using wordTrace_append hprefix tailTrace_7171541
  have hstable : (prefixWord ++ tailWord_7171541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171541).length < 2 ^ (prefixWord ++ tailWord_7171541).sum := by decide
  have hdescent : baseEnd_7171541 < baseStart_7171541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171568 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_7171568 : Nat := 118140960795 + 7171568 * 2 ^ 59
def prefixEnd_7171568 : Nat := 4983230072969 + 3 ^ 40 * 7171568 * 2
def baseEnd_7171568 : Nat := 3682461430403302440918565

theorem tailTrace_7171568 : CollatzResearch.WordTrace tailWord_7171568 prefixEnd_7171568 3682461430403302440918565 := by
  unfold tailWord_7171568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130784286841320708573849679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174379049121760944765132905 130784286841320708573849679)
  ·
    refine ⟨196176430261981062860774519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130784286841320708573849679 196176430261981062860774519)
    ·
      refine ⟨294264645392971594291161779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196176430261981062860774519 294264645392971594291161779)
      ·
        refine ⟨441396968089457391436742669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294264645392971594291161779 441396968089457391436742669)
        ·
          refine ⟨165523863033546521788778501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441396968089457391436742669 165523863033546521788778501)
          ·
            refine ⟨31035724318789972835395969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165523863033546521788778501 31035724318789972835395969)
            ·
              refine ⟨23276793239092479626546977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31035724318789972835395969 23276793239092479626546977)
              ·
                refine ⟨17457594929319359719910233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23276793239092479626546977 17457594929319359719910233)
                ·
                  refine ⟨13093196196989519789932675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17457594929319359719910233 13093196196989519789932675)
                  ·
                    refine ⟨19639794295484279684899013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13093196196989519789932675 19639794295484279684899013)
                    ·
                      refine ⟨3682461430403302440918565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19639794295484279684899013 3682461430403302440918565)
                      ·
                        rfl

theorem cell23_7171568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_7171568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171568 prefixEnd_7171568 := by exact prefixLift 7171568
  have htrace : WordTrace (prefixWord ++ tailWord_7171568) baseStart_7171568 baseEnd_7171568 := by
    simpa [prefixWord, tailWord_7171568, baseEnd_7171568] using wordTrace_append hprefix tailTrace_7171568
  have hstable : (prefixWord ++ tailWord_7171568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171568).length < 2 ^ (prefixWord ++ tailWord_7171568).sum := by decide
  have hdescent : baseEnd_7171568 < baseStart_7171568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171578 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_7171578 : Nat := 118140960795 + 7171578 * 2 ^ 59
def prefixEnd_7171578 : Nat := 4983230072969 + 3 ^ 40 * 7171578 * 2
def baseEnd_7171578 : Nat := 1227488855069949133931173

theorem tailTrace_7171578 : CollatzResearch.WordTrace tailWord_7171578 prefixEnd_7171578 1227488855069949133931173 := by
  unfold tailWord_7171578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65392234603151297213890847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174379292275070125903708925 65392234603151297213890847)
  ·
    refine ⟨98088351904726945820836271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65392234603151297213890847 98088351904726945820836271)
    ·
      refine ⟨147132527857090418731254407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98088351904726945820836271 147132527857090418731254407)
      ·
        refine ⟨220698791785635628096881611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147132527857090418731254407 220698791785635628096881611)
        ·
          refine ⟨331048187678453442145322417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220698791785635628096881611 331048187678453442145322417)
          ·
            refine ⟨248286140758840081608991813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331048187678453442145322417 248286140758840081608991813)
            ·
              refine ⟨46553651392282515301685965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248286140758840081608991813 46553651392282515301685965)
              ·
                refine ⟨17457619272105943238132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46553651392282515301685965 17457619272105943238132237)
                ·
                  refine ⟨6546607227039728714299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17457619272105943238132237 6546607227039728714299589)
                  ·
                    refine ⟨1227488855069949133931173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546607227039728714299589 1227488855069949133931173)
                    ·
                      rfl

theorem cell23_7171578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_7171578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171578 prefixEnd_7171578 := by exact prefixLift 7171578
  have htrace : WordTrace (prefixWord ++ tailWord_7171578) baseStart_7171578 baseEnd_7171578 := by
    simpa [prefixWord, tailWord_7171578, baseEnd_7171578] using wordTrace_append hprefix tailTrace_7171578
  have hstable : (prefixWord ++ tailWord_7171578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171578).length < 2 ^ (prefixWord ++ tailWord_7171578).sum := by decide
  have hdescent : baseEnd_7171578 < baseStart_7171578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171595 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 3, 4]
def baseStart_7171595 : Nat := 118140960795 + 7171595 * 2 ^ 59
def prefixEnd_7171595 : Nat := 4983230072969 + 3 ^ 40 * 7171595 * 2
def baseEnd_7171595 : Nat := 1227491764793657945093647

theorem tailTrace_7171595 : CollatzResearch.WordTrace tailWord_7171595 prefixEnd_7171595 1227491764793657945093647 := by
  unfold tailWord_7171595
  simp only [CollatzResearch.WordTrace]
  refine ⟨261569558453543600758932239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174379705635695733839288159 261569558453543600758932239)
  ·
    refine ⟨392354337680315401138398359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261569558453543600758932239 392354337680315401138398359)
    ·
      refine ⟨588531506520473101707597539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392354337680315401138398359 588531506520473101707597539)
      ·
        refine ⟨882797259780709652561396309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588531506520473101707597539 882797259780709652561396309)
        ·
          refine ⟨10345280388055191240953863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 882797259780709652561396309 10345280388055191240953863)
          ·
            refine ⟨15517920582082786861430795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345280388055191240953863 15517920582082786861430795)
            ·
              refine ⟨23276880873124180292146193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15517920582082786861430795 23276880873124180292146193)
              ·
                refine ⟨17457660654843135219109645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23276880873124180292146193 17457660654843135219109645)
                ·
                  refine ⟨6546622745566175707166117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17457660654843135219109645 6546622745566175707166117)
                  ·
                    refine ⟨1227491764793657945093647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546622745566175707166117 1227491764793657945093647)
                    ·
                      rfl

theorem cell23_7171595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 4].length) (baseStart_7171595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171595 prefixEnd_7171595 := by exact prefixLift 7171595
  have htrace : WordTrace (prefixWord ++ tailWord_7171595) baseStart_7171595 baseEnd_7171595 := by
    simpa [prefixWord, tailWord_7171595, baseEnd_7171595] using wordTrace_append hprefix tailTrace_7171595
  have hstable : (prefixWord ++ tailWord_7171595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171595).length < 2 ^ (prefixWord ++ tailWord_7171595).sum := by decide
  have hdescent : baseEnd_7171595 < baseStart_7171595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171605 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_7171605 : Nat := 118140960795 + 7171605 * 2 ^ 59
def prefixEnd_7171605 : Nat := 4983230072969 + 3 ^ 40 * 7171605 * 2
def baseEnd_7171605 : Nat := 3682480429187518796155895

theorem tailTrace_7171605 : CollatzResearch.WordTrace tailWord_7171605 prefixEnd_7171605 3682480429187518796155895 := by
  unfold tailWord_7171605
  simp only [CollatzResearch.WordTrace]
  refine ⟨261569923183507372466796269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174379948789004914977864179 261569923183507372466796269)
  ·
    refine ⟨98088721193815264675048601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261569923183507372466796269 98088721193815264675048601)
    ·
      refine ⟨73566540895361448506286451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98088721193815264675048601 73566540895361448506286451)
      ·
        refine ⟨110349811343042172759429677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73566540895361448506286451 110349811343042172759429677)
        ·
          refine ⟨41381179253640814784786129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110349811343042172759429677 41381179253640814784786129)
          ·
            refine ⟨31035884440230611088589597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41381179253640814784786129 31035884440230611088589597)
            ·
              refine ⟨11638456665086479158221099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31035884440230611088589597 11638456665086479158221099)
              ·
                refine ⟨17457684997629718737331649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11638456665086479158221099 17457684997629718737331649)
                ·
                  refine ⟨13093263748222289052998737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17457684997629718737331649 13093263748222289052998737)
                  ·
                    refine ⟨9819947811166716789749053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13093263748222289052998737 9819947811166716789749053)
                    ·
                      refine ⟨3682480429187518796155895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9819947811166716789749053 3682480429187518796155895)
                      ·
                        rfl

theorem cell23_7171605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_7171605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171605 prefixEnd_7171605 := by exact prefixLift 7171605
  have htrace : WordTrace (prefixWord ++ tailWord_7171605) baseStart_7171605 baseEnd_7171605 := by
    simpa [prefixWord, tailWord_7171605, baseEnd_7171605] using wordTrace_append hprefix tailTrace_7171605
  have hstable : (prefixWord ++ tailWord_7171605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171605).length < 2 ^ (prefixWord ++ tailWord_7171605).sum := by decide
  have hdescent : baseEnd_7171605 < baseStart_7171605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171612 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_7171612 : Nat := 118140960795 + 7171612 * 2 ^ 59
def prefixEnd_7171612 : Nat := 4983230072969 + 3 ^ 40 * 7171612 * 2
def baseEnd_7171612 : Nat := 1227494674517366756256121

theorem tailTrace_7171612 : CollatzResearch.WordTrace tailWord_7171612 prefixEnd_7171612 1227494674517366756256121 := by
  unfold tailWord_7171612
  simp only [CollatzResearch.WordTrace]
  refine ⟨130785089247241006331150545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174380118996321341774867393 130785089247241006331150545)
  ·
    refine ⟨98088816935430754748362909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130785089247241006331150545 98088816935430754748362909)
    ·
      refine ⟨36783306350786533030636091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98088816935430754748362909 36783306350786533030636091)
      ·
        refine ⟨55174959526179799545954137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36783306350786533030636091 55174959526179799545954137)
        ·
          refine ⟨41381219644634849659465603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55174959526179799545954137 41381219644634849659465603)
          ·
            refine ⟨62071829466952274489198405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41381219644634849659465603 62071829466952274489198405)
            ·
              refine ⟨11638468025053551466724701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62071829466952274489198405 11638468025053551466724701)
              ·
                refine ⟨4364425509395081800021763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11638468025053551466724701 4364425509395081800021763)
                ·
                  refine ⟨6546638264092622700032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364425509395081800021763 6546638264092622700032645)
                  ·
                    refine ⟨1227494674517366756256121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546638264092622700032645 1227494674517366756256121)
                    ·
                      rfl

theorem cell23_7171612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_7171612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171612 prefixEnd_7171612 := by exact prefixLift 7171612
  have htrace : WordTrace (prefixWord ++ tailWord_7171612) baseStart_7171612 baseEnd_7171612 := by
    simpa [prefixWord, tailWord_7171612, baseEnd_7171612] using wordTrace_append hprefix tailTrace_7171612
  have hstable : (prefixWord ++ tailWord_7171612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171612).length < 2 ^ (prefixWord ++ tailWord_7171612).sum := by decide
  have hdescent : baseEnd_7171612 < baseStart_7171612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171635 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 3]
def baseStart_7171635 : Nat := 118140960795 + 7171635 * 2 ^ 59
def prefixEnd_7171635 : Nat := 4983230072969 + 3 ^ 40 * 7171635 * 2
def baseEnd_7171635 : Nat := 3682495833607153678780757

theorem tailTrace_7171635 : CollatzResearch.WordTrace tailWord_7171635 prefixEnd_7171635 3682495833607153678780757 := by
  unfold tailWord_7171635
  simp only [CollatzResearch.WordTrace]
  refine ⟨261571017373398687590388359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174380678248932458393592239 261571017373398687590388359)
  ·
    refine ⟨392356526060098031385582539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261571017373398687590388359 392356526060098031385582539)
    ·
      refine ⟨588534789090147047078373809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392356526060098031385582539 588534789090147047078373809)
      ·
        refine ⟨441401091817610285308780357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588534789090147047078373809 441401091817610285308780357)
        ·
          refine ⟨82762704715801928495396317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441401091817610285308780357 82762704715801928495396317)
          ·
            refine ⟨31036014268425723185773619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82762704715801928495396317 31036014268425723185773619)
            ·
              refine ⟨46554021402638584778660429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31036014268425723185773619 46554021402638584778660429)
              ·
                refine ⟨17457758025989469291997661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46554021402638584778660429 17457758025989469291997661)
                ·
                  refine ⟨6546659259746050984499123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17457758025989469291997661 6546659259746050984499123)
                  ·
                    refine ⟨9819988889619076476748685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6546659259746050984499123 9819988889619076476748685)
                    ·
                      refine ⟨3682495833607153678780757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9819988889619076476748685 3682495833607153678780757)
                      ·
                        rfl

theorem cell23_7171635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_7171635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171635 prefixEnd_7171635 := by exact prefixLift 7171635
  have htrace : WordTrace (prefixWord ++ tailWord_7171635) baseStart_7171635 baseEnd_7171635 := by
    simpa [prefixWord, tailWord_7171635, baseEnd_7171635] using wordTrace_append hprefix tailTrace_7171635
  have hstable : (prefixWord ++ tailWord_7171635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171635).length < 2 ^ (prefixWord ++ tailWord_7171635).sum := by decide
  have hdescent : baseEnd_7171635 < baseStart_7171635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171668 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7171668 : Nat := 118140960795 + 7171668 * 2 ^ 59
def prefixEnd_7171668 : Nat := 4983230072969 + 3 ^ 40 * 7171668 * 2
def baseEnd_7171668 : Nat := 1227504259489584016556035

theorem tailTrace_7171668 : CollatzResearch.WordTrace tailWord_7171668 prefixEnd_7171668 1227504259489584016556035 := by
  unfold tailWord_7171668
  simp only [CollatzResearch.WordTrace]
  refine ⟨130786110491139567113169829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174381480654852756150893105 130786110491139567113169829)
  ·
    refine ⟨24522395717088668833719343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130786110491139567113169829 24522395717088668833719343)
    ·
      refine ⟨36783593575633003250579015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24522395717088668833719343 36783593575633003250579015)
      ·
        refine ⟨55175390363449504875868523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36783593575633003250579015 55175390363449504875868523)
        ·
          refine ⟨82763085545174257313802785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55175390363449504875868523 82763085545174257313802785)
          ·
            refine ⟨62072314158880692985352089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82763085545174257313802785 62072314158880692985352089)
            ·
              refine ⟨46554235619160519739014067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62072314158880692985352089 46554235619160519739014067)
              ·
                refine ⟨69831353428740779608521101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46554235619160519739014067 69831353428740779608521101)
                ·
                  refine ⟨26186757535777792353195413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69831353428740779608521101 26186757535777792353195413)
                  ·
                    refine ⟨1227504259489584016556035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26186757535777792353195413 1227504259489584016556035)
                    ·
                      rfl

theorem cell23_7171668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7171668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171668 prefixEnd_7171668 := by exact prefixLift 7171668
  have htrace : WordTrace (prefixWord ++ tailWord_7171668) baseStart_7171668 baseEnd_7171668 := by
    simpa [prefixWord, tailWord_7171668, baseEnd_7171668] using wordTrace_append hprefix tailTrace_7171668
  have hstable : (prefixWord ++ tailWord_7171668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171668).length < 2 ^ (prefixWord ++ tailWord_7171668).sum := by decide
  have hdescent : baseEnd_7171668 < baseStart_7171668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171685 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_7171685 : Nat := 118140960795 + 7171685 * 2 ^ 59
def prefixEnd_7171685 : Nat := 4983230072969 + 3 ^ 40 * 7171685 * 2
def baseEnd_7171685 : Nat := 1227507169213292827718509

theorem tailTrace_7171685 : CollatzResearch.WordTrace tailWord_7171685 prefixEnd_7171685 1227507169213292827718509 := by
  unfold tailWord_7171685
  simp only [CollatzResearch.WordTrace]
  refine ⟨261572841023217546129708509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174381894015478364086472339 261572841023217546129708509)
  ·
    refine ⟨98089815383706579798640691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261572841023217546129708509 98089815383706579798640691)
    ·
      refine ⟨147134723075559869697961037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98089815383706579798640691 147134723075559869697961037)
      ·
        refine ⟨55175521153334951136735389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147134723075559869697961037 55175521153334951136735389)
        ·
          refine ⟨20690820432500606676275771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55175521153334951136735389 20690820432500606676275771)
          ·
            refine ⟨31036230648750910014413657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690820432500606676275771 31036230648750910014413657)
            ·
              refine ⟨23277172986563182510810243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31036230648750910014413657 23277172986563182510810243)
              ·
                refine ⟨34915759479844773766215365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23277172986563182510810243 34915759479844773766215365)
                ·
                  refine ⟨6546704902470895081165381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34915759479844773766215365 6546704902470895081165381)
                  ·
                    refine ⟨1227507169213292827718509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546704902470895081165381 1227507169213292827718509)
                    ·
                      rfl

theorem cell23_7171685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_7171685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171685 prefixEnd_7171685 := by exact prefixLift 7171685
  have htrace : WordTrace (prefixWord ++ tailWord_7171685) baseStart_7171685 baseEnd_7171685 := by
    simpa [prefixWord, tailWord_7171685, baseEnd_7171685] using wordTrace_append hprefix tailTrace_7171685
  have hstable : (prefixWord ++ tailWord_7171685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171685).length < 2 ^ (prefixWord ++ tailWord_7171685).sum := by decide
  have hdescent : baseEnd_7171685 < baseStart_7171685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171698 : List Nat := [3, 2, 1, 2, 3, 1, 1, 10]
def baseStart_7171698 : Nat := 118140960795 + 7171698 * 2 ^ 59
def prefixEnd_7171698 : Nat := 4983230072969 + 3 ^ 40 * 7171698 * 2
def baseEnd_7171698 : Nat := 136389932699569886381221

theorem tailTrace_7171698 : CollatzResearch.WordTrace tailWord_7171698 prefixEnd_7171698 136389932699569886381221 := by
  unfold tailWord_7171698
  simp only [CollatzResearch.WordTrace]
  refine ⟨65393328793042612337482937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174382210114780299566621165 65393328793042612337482937)
  ·
    refine ⟨49044996594781959253112203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65393328793042612337482937 49044996594781959253112203)
    ·
      refine ⟨73567494892172938879668305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49044996594781959253112203 73567494892172938879668305)
      ·
        refine ⟨55175621169129704159751229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73567494892172938879668305 55175621169129704159751229)
        ·
          refine ⟨20690857938423639059906711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55175621169129704159751229 20690857938423639059906711)
          ·
            refine ⟨31036286907635458589860067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690857938423639059906711 31036286907635458589860067)
            ·
              refine ⟨46554430361453187884790101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31036286907635458589860067 46554430361453187884790101)
              ·
                refine ⟨136389932699569886381221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46554430361453187884790101 136389932699569886381221)
                ·
                  rfl

theorem cell23_7171698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_7171698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171698 prefixEnd_7171698 := by exact prefixLift 7171698
  have htrace : WordTrace (prefixWord ++ tailWord_7171698) baseStart_7171698 baseEnd_7171698 := by
    simpa [prefixWord, tailWord_7171698, baseEnd_7171698] using wordTrace_append hprefix tailTrace_7171698
  have hstable : (prefixWord ++ tailWord_7171698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171698).length < 2 ^ (prefixWord ++ tailWord_7171698).sum := by decide
  have hdescent : baseEnd_7171698 < baseStart_7171698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171743 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7171743 : Nat := 118140960795 + 7171743 * 2 ^ 59
def prefixEnd_7171743 : Nat := 4983230072969 + 3 ^ 40 * 7171743 * 2
def baseEnd_7171743 : Nat := 3682551289517839256230261

theorem tailTrace_7171743 : CollatzResearch.WordTrace tailWord_7171743 prefixEnd_7171743 3682551289517839256230261 := by
  unfold tailWord_7171743
  simp only [CollatzResearch.WordTrace]
  refine ⟨261574956457007422035319883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174383304304671614690213255 261574956457007422035319883)
  ·
    refine ⟨392362434685511133052979825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261574956457007422035319883 392362434685511133052979825)
    ·
      refine ⟨294271826014133349789734869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392362434685511133052979825 294271826014133349789734869)
      ·
        refine ⟨6896995922206250385696911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 294271826014133349789734869 6896995922206250385696911)
        ·
          refine ⟨10345493883309375578545367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896995922206250385696911 10345493883309375578545367)
          ·
            refine ⟨15518240824964063367818051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345493883309375578545367 15518240824964063367818051)
            ·
              refine ⟨23277361237446095051727077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15518240824964063367818051 23277361237446095051727077)
              ·
                refine ⟨4364505232021142822198827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23277361237446095051727077 4364505232021142822198827)
                ·
                  refine ⟨6546757848031714233298241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364505232021142822198827 6546757848031714233298241)
                  ·
                    refine ⟨4910068386023785674973681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6546757848031714233298241 4910068386023785674973681)
                    ·
                      refine ⟨3682551289517839256230261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910068386023785674973681 3682551289517839256230261)
                      ·
                        rfl

theorem cell23_7171743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7171743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171743 prefixEnd_7171743 := by exact prefixLift 7171743
  have htrace : WordTrace (prefixWord ++ tailWord_7171743) baseStart_7171743 baseEnd_7171743 := by
    simpa [prefixWord, tailWord_7171743, baseEnd_7171743] using wordTrace_append hprefix tailTrace_7171743
  have hstable : (prefixWord ++ tailWord_7171743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171743).length < 2 ^ (prefixWord ++ tailWord_7171743).sum := by decide
  have hdescent : baseEnd_7171743 < baseStart_7171743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171768 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_7171768 : Nat := 118140960795 + 7171768 * 2 ^ 59
def prefixEnd_7171768 : Nat := 4983230072969 + 3 ^ 40 * 7171768 * 2
def baseEnd_7171768 : Nat := 3682564126534201658417645

theorem tailTrace_7171768 : CollatzResearch.WordTrace tailWord_7171768 prefixEnd_7171768 3682564126534201658417645 := by
  unfold tailWord_7171768
  simp only [CollatzResearch.WordTrace]
  refine ⟨130787934140958425652489979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174383912187944567536653305 130787934140958425652489979)
  ·
    refine ⟨196181901211437638478734969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130787934140958425652489979 196181901211437638478734969)
    ·
      refine ⟨147136425908578228859051227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196181901211437638478734969 147136425908578228859051227)
      ·
        refine ⟨220704638862867343288576841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147136425908578228859051227 220704638862867343288576841)
        ·
          refine ⟨165528479147150507466432631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220704638862867343288576841 165528479147150507466432631)
          ·
            refine ⟨248292718720725761199648947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165528479147150507466432631 248292718720725761199648947)
            ·
              refine ⟨372439078081088641799473421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248292718720725761199648947 372439078081088641799473421)
              ·
                refine ⟨139664654280408240674802533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372439078081088641799473421 139664654280408240674802533)
                ·
                  refine ⟨26187122677576545126525475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139664654280408240674802533 26187122677576545126525475)
                  ·
                    refine ⟨39280684016364817689788213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26187122677576545126525475 39280684016364817689788213)
                    ·
                      refine ⟨3682564126534201658417645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39280684016364817689788213 3682564126534201658417645)
                      ·
                        rfl

theorem cell23_7171768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_7171768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171768 prefixEnd_7171768 := by exact prefixLift 7171768
  have htrace : WordTrace (prefixWord ++ tailWord_7171768) baseStart_7171768 baseEnd_7171768 := by
    simpa [prefixWord, tailWord_7171768, baseEnd_7171768] using wordTrace_append hprefix tailTrace_7171768
  have hstable : (prefixWord ++ tailWord_7171768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171768).length < 2 ^ (prefixWord ++ tailWord_7171768).sum := by decide
  have hdescent : baseEnd_7171768 < baseStart_7171768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171872 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7171872 : Nat := 118140960795 + 7171872 * 2 ^ 59
def prefixEnd_7171872 : Nat := 4983230072969 + 3 ^ 40 * 7171872 * 2
def baseEnd_7171872 : Nat := 3682617528522269251517167

theorem tailTrace_7171872 : CollatzResearch.WordTrace tailWord_7171872 prefixEnd_7171872 3682617528522269251517167 := by
  unfold tailWord_7171872
  simp only [CollatzResearch.WordTrace]
  refine ⟨130789830736770038533382935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174386440982360051377843913 130789830736770038533382935)
  ·
    refine ⟨196184746105155057800074403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130789830736770038533382935 196184746105155057800074403)
    ·
      refine ⟨294277119157732586700111605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196184746105155057800074403 294277119157732586700111605)
      ·
        refine ⟨27588479921037430003135463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294277119157732586700111605 27588479921037430003135463)
        ·
          refine ⟨41382719881556145004703195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27588479921037430003135463 41382719881556145004703195)
          ·
            refine ⟨62074079822334217507054793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41382719881556145004703195 62074079822334217507054793)
            ·
              refine ⟨46555559866750663130291095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62074079822334217507054793 46555559866750663130291095)
              ·
                refine ⟨69833339800125994695436643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46555559866750663130291095 69833339800125994695436643)
                ·
                  refine ⟨104750009700188992043154965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69833339800125994695436643 104750009700188992043154965)
                  ·
                    refine ⟨4910156704696359002022889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104750009700188992043154965 4910156704696359002022889)
                    ·
                      refine ⟨3682617528522269251517167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910156704696359002022889 3682617528522269251517167)
                      ·
                        rfl

theorem cell23_7171872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7171872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171872 prefixEnd_7171872 := by exact prefixLift 7171872
  have htrace : WordTrace (prefixWord ++ tailWord_7171872) baseStart_7171872 baseEnd_7171872 := by
    simpa [prefixWord, tailWord_7171872, baseEnd_7171872] using wordTrace_append hprefix tailTrace_7171872
  have hstable : (prefixWord ++ tailWord_7171872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171872).length < 2 ^ (prefixWord ++ tailWord_7171872).sum := by decide
  have hdescent : baseEnd_7171872 < baseStart_7171872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171875 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3]
def baseStart_7171875 : Nat := 118140960795 + 7171875 * 2 ^ 59
def prefixEnd_7171875 : Nat := 4983230072969 + 3 ^ 40 * 7171875 * 2
def baseEnd_7171875 : Nat := 3682619068964232739779653

theorem tailTrace_7171875 : CollatzResearch.WordTrace tailWord_7171875 prefixEnd_7171875 3682619068964232739779653 := by
  unfold tailWord_7171875
  simp only [CollatzResearch.WordTrace]
  refine ⟨261579770892529208579125079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174386513928352805719416719 261579770892529208579125079)
  ·
    refine ⟨392369656338793812868687619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261579770892529208579125079 392369656338793812868687619)
    ·
      refine ⟨588554484508190719303031429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392369656338793812868687619 588554484508190719303031429)
      ·
        refine ⟨110353965845285759869318393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588554484508190719303031429 110353965845285759869318393)
        ·
          refine ⟨82765474383964319901988795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110353965845285759869318393 82765474383964319901988795)
          ·
            refine ⟨124148211575946479852983193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82765474383964319901988795 124148211575946479852983193)
            ·
              refine ⟨93111158681959859889737395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124148211575946479852983193 93111158681959859889737395)
              ·
                refine ⟨139666738022939789834606093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93111158681959859889737395 139666738022939789834606093)
                ·
                  refine ⟨52375026758602421187977285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139666738022939789834606093 52375026758602421187977285)
                  ·
                    refine ⟨9820317517237953972745741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52375026758602421187977285 9820317517237953972745741)
                    ·
                      refine ⟨3682619068964232739779653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9820317517237953972745741 3682619068964232739779653)
                      ·
                        rfl

theorem cell23_7171875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_7171875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171875 prefixEnd_7171875 := by exact prefixLift 7171875
  have htrace : WordTrace (prefixWord ++ tailWord_7171875) baseStart_7171875 baseEnd_7171875 := by
    simpa [prefixWord, tailWord_7171875, baseEnd_7171875] using wordTrace_append hprefix tailTrace_7171875
  have hstable : (prefixWord ++ tailWord_7171875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171875).length < 2 ^ (prefixWord ++ tailWord_7171875).sum := by decide
  have hdescent : baseEnd_7171875 < baseStart_7171875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171912 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 6]
def baseStart_7171912 : Nat := 118140960795 + 7171912 * 2 ^ 59
def prefixEnd_7171912 : Nat := 4983230072969 + 3 ^ 40 * 7171912 * 2
def baseEnd_7171912 : Nat := 409182007527605455001887

theorem tailTrace_7171912 : CollatzResearch.WordTrace tailWord_7171912 prefixEnd_7171912 409182007527605455001887 := by
  unfold tailWord_7171912
  simp only [CollatzResearch.WordTrace]
  refine ⟨130790560196697581949110995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174387413595596775932147993 130790560196697581949110995)
  ·
    refine ⟨196185840295046372923666493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130790560196697581949110995 196185840295046372923666493)
    ·
      refine ⟨73569690110642389846374935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196185840295046372923666493 73569690110642389846374935)
      ·
        refine ⟨110354535165963584769562403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73569690110642389846374935 110354535165963584769562403)
        ·
          refine ⟨165531802748945377154343605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110354535165963584769562403 165531802748945377154343605)
          ·
            refine ⟨15518606507713629108219713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165531802748945377154343605 15518606507713629108219713)
            ·
              refine ⟨11638954880785221831164785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15518606507713629108219713 11638954880785221831164785)
              ·
                refine ⟨8729216160588916373373589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11638954880785221831164785 8729216160588916373373589)
                ·
                  refine ⟨409182007527605455001887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8729216160588916373373589 409182007527605455001887)
                  ·
                    rfl

theorem cell23_7171912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_7171912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171912 prefixEnd_7171912 := by exact prefixLift 7171912
  have htrace : WordTrace (prefixWord ++ tailWord_7171912) baseStart_7171912 baseEnd_7171912 := by
    simpa [prefixWord, tailWord_7171912, baseEnd_7171912] using wordTrace_append hprefix tailTrace_7171912
  have hstable : (prefixWord ++ tailWord_7171912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171912).length < 2 ^ (prefixWord ++ tailWord_7171912).sum := by decide
  have hdescent : baseEnd_7171912 < baseStart_7171912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171916 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_7171916 : Nat := 118140960795 + 7171916 * 2 ^ 59
def prefixEnd_7171916 : Nat := 4983230072969 + 3 ^ 40 * 7171916 * 2
def baseEnd_7171916 : Nat := 1227546707223689026455655

theorem tailTrace_7171916 : CollatzResearch.WordTrace tailWord_7171916 prefixEnd_7171916 1227546707223689026455655 := by
  unfold tailWord_7171916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130790633142690336290683801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174387510856920448387578401 130790633142690336290683801)
  ·
    refine ⟨98092974857017752218012851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130790633142690336290683801 98092974857017752218012851)
    ·
      refine ⟨147139462285526628327019277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98092974857017752218012851 147139462285526628327019277)
      ·
        refine ⟨55177298357072485622632229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147139462285526628327019277 55177298357072485622632229)
        ·
          refine ⟨10345743441951091054243543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55177298357072485622632229 10345743441951091054243543)
          ·
            refine ⟨15518615162926636581365315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345743441951091054243543 15518615162926636581365315)
            ·
              refine ⟨23277922744389954872047973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15518615162926636581365315 23277922744389954872047973)
              ·
                refine ⟨4364610514573116538508995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23277922744389954872047973 4364610514573116538508995)
                ·
                  refine ⟨6546915771859674807763493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364610514573116538508995 6546915771859674807763493)
                  ·
                    refine ⟨1227546707223689026455655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546915771859674807763493 1227546707223689026455655)
                    ·
                      rfl

theorem cell23_7171916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_7171916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171916 prefixEnd_7171916 := by exact prefixLift 7171916
  have htrace : WordTrace (prefixWord ++ tailWord_7171916) baseStart_7171916 baseEnd_7171916 := by
    simpa [prefixWord, tailWord_7171916, baseEnd_7171916] using wordTrace_append hprefix tailTrace_7171916
  have hstable : (prefixWord ++ tailWord_7171916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171916).length < 2 ^ (prefixWord ++ tailWord_7171916).sum := by decide
  have hdescent : baseEnd_7171916 < baseStart_7171916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7171996 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7171996 : Nat := 118140960795 + 7171996 * 2 ^ 59
def prefixEnd_7171996 : Nat := 4983230072969 + 3 ^ 40 * 7171996 * 2
def baseEnd_7171996 : Nat := 3682681200123426766366597

theorem tailTrace_7171996 : CollatzResearch.WordTrace tailWord_7171996 prefixEnd_7171996 3682681200123426766366597 := by
  unfold tailWord_7171996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130792092062545423122139921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174389456083393897496186561 130792092062545423122139921)
  ·
    refine ⟨98094069046909067341604941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130792092062545423122139921 98094069046909067341604941)
    ·
      refine ⟨36785275892590900253101853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98094069046909067341604941 36785275892590900253101853)
      ·
        refine ⟨13794478459721587594913195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36785275892590900253101853 13794478459721587594913195)
        ·
          refine ⟨20691717689582381392369793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13794478459721587594913195 20691717689582381392369793)
          ·
            refine ⟨15518788267186786044277345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20691717689582381392369793 15518788267186786044277345)
            ·
              refine ⟨11639091200390089533208009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15518788267186786044277345 11639091200390089533208009)
              ·
                refine ⟨8729318400292567149906007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639091200390089533208009 8729318400292567149906007)
                ·
                  refine ⟨13093977600438850724859011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729318400292567149906007 13093977600438850724859011)
                  ·
                    refine ⟨19640966400658276087288517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13093977600438850724859011 19640966400658276087288517)
                    ·
                      refine ⟨3682681200123426766366597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19640966400658276087288517 3682681200123426766366597)
                      ·
                        rfl

theorem cell23_7171996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7171996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7171996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7171996 prefixEnd_7171996 := by exact prefixLift 7171996
  have htrace : WordTrace (prefixWord ++ tailWord_7171996) baseStart_7171996 baseEnd_7171996 := by
    simpa [prefixWord, tailWord_7171996, baseEnd_7171996] using wordTrace_append hprefix tailTrace_7171996
  have hstable : (prefixWord ++ tailWord_7171996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7171996).length < 2 ^ (prefixWord ++ tailWord_7171996).sum := by decide
  have hdescent : baseEnd_7171996 < baseStart_7171996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7171996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_7172005 : Nat := 118140960795 + 7172005 * 2 ^ 59
def prefixEnd_7172005 : Nat := 4983230072969 + 3 ^ 40 * 7172005 * 2
def baseEnd_7172005 : Nat := 3682685821449317231154055

theorem tailTrace_7172005 : CollatzResearch.WordTrace tailWord_7172005 prefixEnd_7172005 3682685821449317231154055 := by
  unfold tailWord_7172005
  simp only [CollatzResearch.WordTrace]
  refine ⟨261584512382058240781357469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174389674921372160520904979 261584512382058240781357469)
  ·
    refine ⟨98094192143271840293009051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261584512382058240781357469 98094192143271840293009051)
    ·
      refine ⟨147141288214907760439513577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98094192143271840293009051 147141288214907760439513577)
      ·
        refine ⟨110355966161180820329635183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147141288214907760439513577 110355966161180820329635183)
        ·
          refine ⟨165533949241771230494452775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110355966161180820329635183 165533949241771230494452775)
          ·
            refine ⟨248300923862656845741679163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165533949241771230494452775 248300923862656845741679163)
            ·
              refine ⟨372451385793985268612518745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248300923862656845741679163 372451385793985268612518745)
              ·
                refine ⟨279338539345488951459389059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372451385793985268612518745 279338539345488951459389059)
                ·
                  refine ⟨419007809018233427189083589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279338539345488951459389059 419007809018233427189083589)
                  ·
                    refine ⟨78563964190918767597953173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419007809018233427189083589 78563964190918767597953173)
                    ·
                      refine ⟨3682685821449317231154055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78563964190918767597953173 3682685821449317231154055)
                      ·
                        rfl

theorem cell23_7172005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_7172005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172005 prefixEnd_7172005 := by exact prefixLift 7172005
  have htrace : WordTrace (prefixWord ++ tailWord_7172005) baseStart_7172005 baseEnd_7172005 := by
    simpa [prefixWord, tailWord_7172005, baseEnd_7172005] using wordTrace_append hprefix tailTrace_7172005
  have hstable : (prefixWord ++ tailWord_7172005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172005).length < 2 ^ (prefixWord ++ tailWord_7172005).sum := by decide
  have hdescent : baseEnd_7172005 < baseStart_7172005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172039 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_7172039 : Nat := 118140960795 + 7172039 * 2 ^ 59
def prefixEnd_7172039 : Nat := 4983230072969 + 3 ^ 40 * 7172039 * 2
def baseEnd_7172039 : Nat := 3682703279791570098128899

theorem tailTrace_7172039 : CollatzResearch.WordTrace tailWord_7172039 prefixEnd_7172039 3682703279791570098128899 := by
  unfold tailWord_7172039
  simp only [CollatzResearch.WordTrace]
  refine ⟨261585752463935064588095171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174390501642623376392063447 261585752463935064588095171)
  ·
    refine ⟨392378628695902596882142757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261585752463935064588095171 392378628695902596882142757)
    ·
      refine ⟨73570992880481736915401767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392378628695902596882142757 73570992880481736915401767)
      ·
        refine ⟨110356489320722605373102651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73570992880481736915401767 110356489320722605373102651)
        ·
          refine ⟨165534733981083908059653977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110356489320722605373102651 165534733981083908059653977)
          ·
            refine ⟨124151050485812931044740483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165534733981083908059653977 124151050485812931044740483)
            ·
              refine ⟨186226575728719396567110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124151050485812931044740483 186226575728719396567110725)
              ·
                refine ⟨34917482949134886856333261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186226575728719396567110725 34917482949134886856333261)
                ·
                  refine ⟨13094056105925582571124973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34917482949134886856333261 13094056105925582571124973)
                  ·
                    refine ⟨4910271039722093464171865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13094056105925582571124973 4910271039722093464171865)
                    ·
                      refine ⟨3682703279791570098128899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910271039722093464171865 3682703279791570098128899)
                      ·
                        rfl

theorem cell23_7172039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_7172039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172039 prefixEnd_7172039 := by exact prefixLift 7172039
  have htrace : WordTrace (prefixWord ++ tailWord_7172039) baseStart_7172039 baseEnd_7172039 := by
    simpa [prefixWord, tailWord_7172039, baseEnd_7172039] using wordTrace_append hprefix tailTrace_7172039
  have hstable : (prefixWord ++ tailWord_7172039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172039).length < 2 ^ (prefixWord ++ tailWord_7172039).sum := by decide
  have hdescent : baseEnd_7172039 < baseStart_7172039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172046 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_7172046 : Nat := 118140960795 + 7172046 * 2 ^ 59
def prefixEnd_7172046 : Nat := 4983230072969 + 3 ^ 40 * 7172046 * 2
def baseEnd_7172046 : Nat := 3682706874156151570741367

theorem tailTrace_7172046 : CollatzResearch.WordTrace tailWord_7172046 prefixEnd_7172046 3682706874156151570741367 := by
  unfold tailWord_7172046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698250971863713097949999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174390671849939803189066661 32698250971863713097949999)
  ·
    refine ⟨49047376457795569646924999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32698250971863713097949999 49047376457795569646924999)
    ·
      refine ⟨73571064686693354470387499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49047376457795569646924999 73571064686693354470387499)
      ·
        refine ⟨110356597030040031705581249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73571064686693354470387499 110356597030040031705581249)
        ·
          refine ⟨82767447772530023779185937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110356597030040031705581249 82767447772530023779185937)
          ·
            refine ⟨62075585829397517834389453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82767447772530023779185937 62075585829397517834389453)
            ·
              refine ⟨23278344686024069187896045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62075585829397517834389453 23278344686024069187896045)
              ·
                refine ⟨8729379257259025945461017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23278344686024069187896045 8729379257259025945461017)
                ·
                  refine ⟨6547034442944269459095763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8729379257259025945461017 6547034442944269459095763)
                  ·
                    refine ⟨9820551664416404188643645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6547034442944269459095763 9820551664416404188643645)
                    ·
                      refine ⟨3682706874156151570741367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9820551664416404188643645 3682706874156151570741367)
                      ·
                        rfl

theorem cell23_7172046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_7172046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172046 prefixEnd_7172046 := by exact prefixLift 7172046
  have htrace : WordTrace (prefixWord ++ tailWord_7172046) baseStart_7172046 baseEnd_7172046 := by
    simpa [prefixWord, tailWord_7172046, baseEnd_7172046] using wordTrace_append hprefix tailTrace_7172046
  have hstable : (prefixWord ++ tailWord_7172046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172046).length < 2 ^ (prefixWord ++ tailWord_7172046).sum := by decide
  have hdescent : baseEnd_7172046 < baseStart_7172046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172050 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7172050 : Nat := 118140960795 + 7172050 * 2 ^ 59
def prefixEnd_7172050 : Nat := 4983230072969 + 3 ^ 40 * 7172050 * 2
def baseEnd_7172050 : Nat := 3682708928078769555091349

theorem tailTrace_7172050 : CollatzResearch.WordTrace tailWord_7172050 prefixEnd_7172050 3682708928078769555091349 := by
  unfold tailWord_7172050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65396538416723803366686401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174390769111263475644497069 65396538416723803366686401)
  ·
    refine ⟨49047403812542852525014801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65396538416723803366686401 49047403812542852525014801)
    ·
      refine ⟨36785552859407139393761101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49047403812542852525014801 36785552859407139393761101)
      ·
        refine ⟨13794582322277677272660413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36785552859407139393761101 13794582322277677272660413)
        ·
          refine ⟨5172968370854128977247655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13794582322277677272660413 5172968370854128977247655)
          ·
            refine ⟨7759452556281193465871483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172968370854128977247655 7759452556281193465871483)
            ·
              refine ⟨11639178834421790198807225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759452556281193465871483 11639178834421790198807225)
              ·
                refine ⟨8729384125816342649105419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639178834421790198807225 8729384125816342649105419)
                ·
                  refine ⟨13094076188724513973658129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729384125816342649105419 13094076188724513973658129)
                  ·
                    refine ⟨9820557141543385480243597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13094076188724513973658129 9820557141543385480243597)
                    ·
                      refine ⟨3682708928078769555091349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9820557141543385480243597 3682708928078769555091349)
                      ·
                        rfl

theorem cell23_7172050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7172050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172050 prefixEnd_7172050 := by exact prefixLift 7172050
  have htrace : WordTrace (prefixWord ++ tailWord_7172050) baseStart_7172050 baseEnd_7172050 := by
    simpa [prefixWord, tailWord_7172050, baseEnd_7172050] using wordTrace_append hprefix tailTrace_7172050
  have hstable : (prefixWord ++ tailWord_7172050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172050).length < 2 ^ (prefixWord ++ tailWord_7172050).sum := by decide
  have hdescent : baseEnd_7172050 < baseStart_7172050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172092 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 7]
def baseStart_7172092 : Nat := 118140960795 + 7172092 * 2 ^ 59
def prefixEnd_7172092 : Nat := 4983230072969 + 3 ^ 40 * 7172092 * 2
def baseEnd_7172092 : Nat := 409192277140695376751795

theorem tailTrace_7172092 : CollatzResearch.WordTrace tailWord_7172092 prefixEnd_7172092 409192277140695376751795 := by
  unfold tailWord_7172092
  simp only [CollatzResearch.WordTrace]
  refine ⟨130793842766371527319887265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174391790355162036426516353 130793842766371527319887265)
  ·
    refine ⟨98095382074778645489915449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130793842766371527319887265 98095382074778645489915449)
    ·
      refine ⟨73571536556083984117436587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98095382074778645489915449 73571536556083984117436587)
      ·
        refine ⟨110357304834125976176154881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73571536556083984117436587 110357304834125976176154881)
        ·
          refine ⟨82767978625594482132116161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110357304834125976176154881 82767978625594482132116161)
          ·
            refine ⟨62075983969195861599087121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82767978625594482132116161 62075983969195861599087121)
            ·
              refine ⟨46556987976896896199315341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62075983969195861599087121 46556987976896896199315341)
              ·
                refine ⟨17458870491336336074743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46556987976896896199315341 17458870491336336074743253)
                ·
                  refine ⟨409192277140695376751795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17458870491336336074743253 409192277140695376751795)
                  ·
                    rfl

theorem cell23_7172092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_7172092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172092 prefixEnd_7172092 := by exact prefixLift 7172092
  have htrace : WordTrace (prefixWord ++ tailWord_7172092) baseStart_7172092 baseEnd_7172092 := by
    simpa [prefixWord, tailWord_7172092, baseEnd_7172092] using wordTrace_append hprefix tailTrace_7172092
  have hstable : (prefixWord ++ tailWord_7172092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172092).length < 2 ^ (prefixWord ++ tailWord_7172092).sum := by decide
  have hdescent : baseEnd_7172092 < baseStart_7172092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172103 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7172103 : Nat := 118140960795 + 7172103 * 2 ^ 59
def prefixEnd_7172103 : Nat := 4983230072969 + 3 ^ 40 * 7172103 * 2
def baseEnd_7172103 : Nat := 3682736142553457847728605

theorem tailTrace_7172103 : CollatzResearch.WordTrace tailWord_7172103 prefixEnd_7172103 3682736142553457847728605 := by
  unfold tailWord_7172103
  simp only [CollatzResearch.WordTrace]
  refine ⟨261588086735703203518424963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174392057823802135678949975 261588086735703203518424963)
  ·
    refine ⟨392382130103554805277637445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261588086735703203518424963 392382130103554805277637445)
    ·
      refine ⟨73571649394416525989557021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392382130103554805277637445 73571649394416525989557021)
      ·
        refine ⟨27589368522906197246083883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73571649394416525989557021 27589368522906197246083883)
        ·
          refine ⟨41384052784359295869125825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27589368522906197246083883 41384052784359295869125825)
          ·
            refine ⟨31038039588269471901844369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41384052784359295869125825 31038039588269471901844369)
            ·
              refine ⟨23278529691202103926383277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31038039588269471901844369 23278529691202103926383277)
              ·
                refine ⟨8729448634200788972393729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23278529691202103926383277 8729448634200788972393729)
                ·
                  refine ⟨6547086475650591729295297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8729448634200788972393729 6547086475650591729295297)
                  ·
                    refine ⟨4910314856737943796971473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547086475650591729295297 4910314856737943796971473)
                    ·
                      refine ⟨3682736142553457847728605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910314856737943796971473 3682736142553457847728605)
                      ·
                        rfl

theorem cell23_7172103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7172103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172103 prefixEnd_7172103 := by exact prefixLift 7172103
  have htrace : WordTrace (prefixWord ++ tailWord_7172103) baseStart_7172103 baseEnd_7172103 := by
    simpa [prefixWord, tailWord_7172103, baseEnd_7172103] using wordTrace_append hprefix tailTrace_7172103
  have hstable : (prefixWord ++ tailWord_7172103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172103).length < 2 ^ (prefixWord ++ tailWord_7172103).sum := by decide
  have hdescent : baseEnd_7172103 < baseStart_7172103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172169 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_7172169 : Nat := 118140960795 + 7172169 * 2 ^ 59
def prefixEnd_7172169 : Nat := 4983230072969 + 3 ^ 40 * 7172169 * 2
def baseEnd_7172169 : Nat := 1227590010758884863167767

theorem tailTrace_7172169 : CollatzResearch.WordTrace tailWord_7172169 prefixEnd_7172169 1227590010758884863167767 := by
  unfold tailWord_7172169
  simp only [CollatzResearch.WordTrace]
  refine ⟨261590493953464096790327561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174393662635642731193551707 261590493953464096790327561)
  ·
    refine ⟨196192870465098072592745671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261590493953464096790327561 196192870465098072592745671)
    ·
      refine ⟨294289305697647108889118507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196192870465098072592745671 294289305697647108889118507)
      ·
        refine ⟨441433958546470663333677761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294289305697647108889118507 441433958546470663333677761)
        ·
          refine ⟨331075468909852997500258321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441433958546470663333677761 331075468909852997500258321)
          ·
            refine ⟨248306601682389748125193741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331075468909852997500258321 248306601682389748125193741)
            ·
              refine ⟨93114975630896155546947653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248306601682389748125193741 93114975630896155546947653)
              ·
                refine ⟨17459057930793029165052685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93114975630896155546947653 17459057930793029165052685)
                ·
                  refine ⟨6547146724047385936894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17459057930793029165052685 6547146724047385936894757)
                  ·
                    refine ⟨1227590010758884863167767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547146724047385936894757 1227590010758884863167767)
                    ·
                      rfl

theorem cell23_7172169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_7172169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172169 prefixEnd_7172169 := by exact prefixLift 7172169
  have htrace : WordTrace (prefixWord ++ tailWord_7172169) baseStart_7172169 baseEnd_7172169 := by
    simpa [prefixWord, tailWord_7172169, baseEnd_7172169] using wordTrace_append hprefix tailTrace_7172169
  have hstable : (prefixWord ++ tailWord_7172169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172169).length < 2 ^ (prefixWord ++ tailWord_7172169).sum := by decide
  have hdescent : baseEnd_7172169 < baseStart_7172169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172190 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7172190 : Nat := 118140960795 + 7172190 * 2 ^ 59
def prefixEnd_7172190 : Nat := 4983230072969 + 3 ^ 40 * 7172190 * 2
def baseEnd_7172190 : Nat := 1227593605123466335780235

theorem tailTrace_7172190 : CollatzResearch.WordTrace tailWord_7172190 prefixEnd_7172190 1227593605123466335780235 := by
  unfold tailWord_7172190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698907485798502172105253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174394173257592011584561349 32698907485798502172105253)
  ·
    refine ⟨6131045153587219157269735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32698907485798502172105253 6131045153587219157269735)
    ·
      refine ⟨9196567730380828735904603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131045153587219157269735 9196567730380828735904603)
      ·
        refine ⟨13794851595571243103856905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9196567730380828735904603 13794851595571243103856905)
        ·
          refine ⟨10346138696678432327892679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13794851595571243103856905 10346138696678432327892679)
          ·
            refine ⟨15519208045017648491839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346138696678432327892679 15519208045017648491839019)
            ·
              refine ⟨23278812067526472737758529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15519208045017648491839019 23278812067526472737758529)
              ·
                refine ⟨17459109050644854553318897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23278812067526472737758529 17459109050644854553318897)
                ·
                  refine ⟨13094331787983640914989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17459109050644854553318897 13094331787983640914989173)
                  ·
                    refine ⟨1227593605123466335780235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13094331787983640914989173 1227593605123466335780235)
                    ·
                      rfl

theorem cell23_7172190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7172190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172190 prefixEnd_7172190 := by exact prefixLift 7172190
  have htrace : WordTrace (prefixWord ++ tailWord_7172190) baseStart_7172190 baseEnd_7172190 := by
    simpa [prefixWord, tailWord_7172190, baseEnd_7172190] using wordTrace_append hprefix tailTrace_7172190
  have hstable : (prefixWord ++ tailWord_7172190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172190).length < 2 ^ (prefixWord ++ tailWord_7172190).sum := by decide
  have hdescent : baseEnd_7172190 < baseStart_7172190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172199 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 6]
def baseStart_7172199 : Nat := 118140960795 + 7172199 * 2 ^ 59
def prefixEnd_7172199 : Nat := 4983230072969 + 3 ^ 40 * 7172199 * 2
def baseEnd_7172199 : Nat := 409198381855143274680907

theorem tailTrace_7172199 : CollatzResearch.WordTrace tailWord_7172199 prefixEnd_7172199 409198381855143274680907 := by
  unfold tailWord_7172199
  simp only [CollatzResearch.WordTrace]
  refine ⟨261591588143355411913919651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174394392095570274609279767 261591588143355411913919651)
  ·
    refine ⟨392387382215033117870879477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261591588143355411913919651 392387382215033117870879477)
    ·
      refine ⟨36786317082659354800394951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392387382215033117870879477 36786317082659354800394951)
      ·
        refine ⟨55179475623989032200592427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36786317082659354800394951 55179475623989032200592427)
        ·
          refine ⟨82769213435983548300888641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55179475623989032200592427 82769213435983548300888641)
          ·
            refine ⟨62076910076987661225666481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82769213435983548300888641 62076910076987661225666481)
            ·
              refine ⟨46557682557740745919249861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62076910076987661225666481 46557682557740745919249861)
              ·
                refine ⟨8729565479576389859859349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46557682557740745919249861 8729565479576389859859349)
                ·
                  refine ⟨409198381855143274680907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8729565479576389859859349 409198381855143274680907)
                  ·
                    rfl

theorem cell23_7172199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 6].length) (baseStart_7172199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172199 prefixEnd_7172199 := by exact prefixLift 7172199
  have htrace : WordTrace (prefixWord ++ tailWord_7172199) baseStart_7172199 baseEnd_7172199 := by
    simpa [prefixWord, tailWord_7172199, baseEnd_7172199] using wordTrace_append hprefix tailTrace_7172199
  have hstable : (prefixWord ++ tailWord_7172199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172199).length < 2 ^ (prefixWord ++ tailWord_7172199).sum := by decide
  have hdescent : baseEnd_7172199 < baseStart_7172199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 1, 1, 3]
def baseStart_7172243 : Nat := 118140960795 + 7172243 * 2 ^ 59
def prefixEnd_7172243 : Nat := 4983230072969 + 3 ^ 40 * 7172243 * 2
def baseEnd_7172243 : Nat := 3682808029845087299977961

theorem tailTrace_7172243 : CollatzResearch.WordTrace tailWord_7172243 prefixEnd_7172243 3682808029845087299977961 := by
  unfold tailWord_7172243
  simp only [CollatzResearch.WordTrace]
  refine ⟨261593192955196007428521383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174395461970130671619014255 261593192955196007428521383)
  ·
    refine ⟨392389789432794011142782075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261593192955196007428521383 392389789432794011142782075)
    ·
      refine ⟨588584684149191016714173113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392389789432794011142782075 588584684149191016714173113)
      ·
        refine ⟨441438513111893262535629835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588584684149191016714173113 441438513111893262535629835)
        ·
          refine ⟨662157769667839893803444753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441438513111893262535629835 662157769667839893803444753)
          ·
            refine ⟨496618327250879920352583565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662157769667839893803444753 496618327250879920352583565)
            ·
              refine ⟨186231872719079970132218837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496618327250879920352583565 186231872719079970132218837)
              ·
                refine ⟨4364809516853436799973879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186231872719079970132218837 4364809516853436799973879)
                ·
                  refine ⟨6547214275280155199960819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364809516853436799973879 6547214275280155199960819)
                  ·
                    refine ⟨9820821412920232799941229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6547214275280155199960819 9820821412920232799941229)
                    ·
                      refine ⟨3682808029845087299977961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9820821412920232799941229 3682808029845087299977961)
                      ·
                        rfl

theorem cell23_7172243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 1, 3].length) (baseStart_7172243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172243 prefixEnd_7172243 := by exact prefixLift 7172243
  have htrace : WordTrace (prefixWord ++ tailWord_7172243) baseStart_7172243 baseEnd_7172243 := by
    simpa [prefixWord, tailWord_7172243, baseEnd_7172243] using wordTrace_append hprefix tailTrace_7172243
  have hstable : (prefixWord ++ tailWord_7172243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172243).length < 2 ^ (prefixWord ++ tailWord_7172243).sum := by decide
  have hdescent : baseEnd_7172243 < baseStart_7172243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172253 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_7172253 : Nat := 118140960795 + 7172253 * 2 ^ 59
def prefixEnd_7172253 : Nat := 4983230072969 + 3 ^ 40 * 7172253 * 2
def baseEnd_7172253 : Nat := 3682813164651632260852915

theorem tailTrace_7172253 : CollatzResearch.WordTrace tailWord_7172253 prefixEnd_7172253 3682813164651632260852915 := by
  unfold tailWord_7172253
  simp only [CollatzResearch.WordTrace]
  refine ⟨261593557685159779136385413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174395705123439852757590275 261593557685159779136385413)
  ·
    refine ⟨49048792065967458588072265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261593557685159779136385413 49048792065967458588072265)
    ·
      refine ⟨36786594049475593941054199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49048792065967458588072265 36786594049475593941054199)
      ·
        refine ⟨55179891074213390911581299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36786594049475593941054199 55179891074213390911581299)
        ·
          refine ⟨82769836611320086367371949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55179891074213390911581299 82769836611320086367371949)
          ·
            refine ⟨31038688729245032387764481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82769836611320086367371949 31038688729245032387764481)
            ·
              refine ⟨23279016546933774290823361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31038688729245032387764481 23279016546933774290823361)
              ·
                refine ⟨17459262410200330718117521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23279016546933774290823361 17459262410200330718117521)
                ·
                  refine ⟨13094446807650248038588141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17459262410200330718117521 13094446807650248038588141)
                  ·
                    refine ⟨4910417552868843014470553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13094446807650248038588141 4910417552868843014470553)
                    ·
                      refine ⟨3682813164651632260852915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910417552868843014470553 3682813164651632260852915)
                      ·
                        rfl

theorem cell23_7172253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_7172253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172253 prefixEnd_7172253 := by exact prefixLift 7172253
  have htrace : WordTrace (prefixWord ++ tailWord_7172253) baseStart_7172253 baseEnd_7172253 := by
    simpa [prefixWord, tailWord_7172253, baseEnd_7172253] using wordTrace_append hprefix tailTrace_7172253
  have hstable : (prefixWord ++ tailWord_7172253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172253).length < 2 ^ (prefixWord ++ tailWord_7172253).sum := by decide
  have hdescent : baseEnd_7172253 < baseStart_7172253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172254 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7172254 : Nat := 118140960795 + 7172254 * 2 ^ 59
def prefixEnd_7172254 : Nat := 4983230072969 + 3 ^ 40 * 7172254 * 2
def baseEnd_7172254 : Nat := 1227604559377428918980137

theorem tailTrace_7172254 : CollatzResearch.WordTrace tailWord_7172254 prefixEnd_7172254 1227604559377428918980137 := by
  unfold tailWord_7172254
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699199269769519538396477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174395729438770770871447877 32699199269769519538396477)
  ·
    refine ⟨12262199726163569826898679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32699199269769519538396477 12262199726163569826898679)
    ·
      refine ⟨18393299589245354740348019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262199726163569826898679 18393299589245354740348019)
      ·
        refine ⟨27589949383868032110522029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18393299589245354740348019 27589949383868032110522029)
        ·
          refine ⟨10346231018950512041445761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27589949383868032110522029 10346231018950512041445761)
          ·
            refine ⟨7759673264212884031084321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346231018950512041445761 7759673264212884031084321)
            ·
              refine ⟨5819754948159663023313241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759673264212884031084321 5819754948159663023313241)
              ·
                refine ⟨4364816211119747267484931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819754948159663023313241 4364816211119747267484931)
                ·
                  refine ⟨6547224316679620901227397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364816211119747267484931 6547224316679620901227397)
                  ·
                    refine ⟨1227604559377428918980137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547224316679620901227397 1227604559377428918980137)
                    ·
                      rfl

theorem cell23_7172254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7172254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172254 prefixEnd_7172254 := by exact prefixLift 7172254
  have htrace : WordTrace (prefixWord ++ tailWord_7172254) baseStart_7172254 baseEnd_7172254 := by
    simpa [prefixWord, tailWord_7172254, baseEnd_7172254] using wordTrace_append hprefix tailTrace_7172254
  have hstable : (prefixWord ++ tailWord_7172254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172254).length < 2 ^ (prefixWord ++ tailWord_7172254).sum := by decide
  have hdescent : baseEnd_7172254 < baseStart_7172254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172283 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 3, 2, 2]
def baseStart_7172283 : Nat := 118140960795 + 7172283 * 2 ^ 59
def prefixEnd_7172283 : Nat := 4983230072969 + 3 ^ 40 * 7172283 * 2
def baseEnd_7172283 : Nat := 3682828569071267143477777

theorem tailTrace_7172283 : CollatzResearch.WordTrace tailWord_7172283 prefixEnd_7172283 3682828569071267143477777 := by
  unfold tailWord_7172283
  simp only [CollatzResearch.WordTrace]
  refine ⟨261594651875051094259977503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174396434583367396173318335 261594651875051094259977503)
  ·
    refine ⟨392391977812576641389966255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261594651875051094259977503 392391977812576641389966255)
    ·
      refine ⟨588587966718864962084949383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392391977812576641389966255 588587966718864962084949383)
      ·
        refine ⟨882881950078297443127424075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588587966718864962084949383 882881950078297443127424075)
        ·
          refine ⟨1324322925117446164691136113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882881950078297443127424075 1324322925117446164691136113)
          ·
            refine ⟨993242193838084623518352085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324322925117446164691136113 993242193838084623518352085)
            ·
              refine ⟨23279113918080108363711377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 993242193838084623518352085 23279113918080108363711377)
              ·
                refine ⟨17459335438560081272783533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23279113918080108363711377 17459335438560081272783533)
                ·
                  refine ⟨6547250789460030477293825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17459335438560081272783533 6547250789460030477293825)
                  ·
                    refine ⟨4910438092095022857970369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547250789460030477293825 4910438092095022857970369)
                    ·
                      refine ⟨3682828569071267143477777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910438092095022857970369 3682828569071267143477777)
                      ·
                        rfl

theorem cell23_7172283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2, 2].length) (baseStart_7172283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172283 prefixEnd_7172283 := by exact prefixLift 7172283
  have htrace : WordTrace (prefixWord ++ tailWord_7172283) baseStart_7172283 baseEnd_7172283 := by
    simpa [prefixWord, tailWord_7172283, baseEnd_7172283] using wordTrace_append hprefix tailTrace_7172283
  have hstable : (prefixWord ++ tailWord_7172283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172283).length < 2 ^ (prefixWord ++ tailWord_7172283).sum := by decide
  have hdescent : baseEnd_7172283 < baseStart_7172283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172300 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7172300 : Nat := 118140960795 + 7172300 * 2 ^ 59
def prefixEnd_7172300 : Nat := 4983230072969 + 3 ^ 40 * 7172300 * 2
def baseEnd_7172300 : Nat := 3682837298242393576965199

theorem tailTrace_7172300 : CollatzResearch.WordTrace tailWord_7172300 prefixEnd_7172300 3682837298242393576965199 := by
  unfold tailWord_7172300
  simp only [CollatzResearch.WordTrace]
  refine ⟨130797635957994753081673177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174396847943993004108897569 130797635957994753081673177)
  ·
    refine ⟨98098226968496064811254883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130797635957994753081673177 98098226968496064811254883)
    ·
      refine ⟨147147340452744097216882325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98098226968496064811254883 147147340452744097216882325)
      ·
        refine ⟨6897531583722379557041359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147147340452744097216882325 6897531583722379557041359)
        ·
          refine ⟨10346297375583569335562039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897531583722379557041359 10346297375583569335562039)
          ·
            refine ⟨15519446063375354003343059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346297375583569335562039 15519446063375354003343059)
            ·
              refine ⟨23279169095063031005014589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15519446063375354003343059 23279169095063031005014589)
              ·
                refine ⟨8729688410648636626880471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23279169095063031005014589 8729688410648636626880471)
                ·
                  refine ⟨13094532615972954940320707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729688410648636626880471 13094532615972954940320707)
                  ·
                    refine ⟨19641798923959432410481061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13094532615972954940320707 19641798923959432410481061)
                    ·
                      refine ⟨3682837298242393576965199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19641798923959432410481061 3682837298242393576965199)
                      ·
                        rfl

theorem cell23_7172300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7172300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172300 prefixEnd_7172300 := by exact prefixLift 7172300
  have htrace : WordTrace (prefixWord ++ tailWord_7172300) baseStart_7172300 baseEnd_7172300 := by
    simpa [prefixWord, tailWord_7172300, baseEnd_7172300] using wordTrace_append hprefix tailTrace_7172300
  have hstable : (prefixWord ++ tailWord_7172300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172300).length < 2 ^ (prefixWord ++ tailWord_7172300).sum := by decide
  have hdescent : baseEnd_7172300 < baseStart_7172300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172310 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7172310 : Nat := 118140960795 + 7172310 * 2 ^ 59
def prefixEnd_7172310 : Nat := 4983230072969 + 3 ^ 40 * 7172310 * 2
def baseEnd_7172310 : Nat := 1227614144349646179280051

theorem tailTrace_7172310 : CollatzResearch.WordTrace tailWord_7172310 prefixEnd_7172310 1227614144349646179280051 := by
  unfold tailWord_7172310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349727290372079866950649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174397091097302185247473589 16349727290372079866950649)
  ·
    refine ⟨12262295467779059900212987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16349727290372079866950649 12262295467779059900212987)
    ·
      refine ⟨18393443201668589850319481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262295467779059900212987 18393443201668589850319481)
      ·
        refine ⟨13795082401251442387739611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18393443201668589850319481 13795082401251442387739611)
        ·
          refine ⟨20692623601877163581609417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795082401251442387739611 20692623601877163581609417)
          ·
            refine ⟨15519467701407872686207063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20692623601877163581609417 15519467701407872686207063)
            ·
              refine ⟨23279201552111809029310595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15519467701407872686207063 23279201552111809029310595)
              ·
                refine ⟨34918802328167713543965893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23279201552111809029310595 34918802328167713543965893)
                ·
                  refine ⟨6547275436531446289493605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34918802328167713543965893 6547275436531446289493605)
                  ·
                    refine ⟨1227614144349646179280051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547275436531446289493605 1227614144349646179280051)
                    ·
                      rfl

theorem cell23_7172310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7172310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172310 prefixEnd_7172310 := by exact prefixLift 7172310
  have htrace : WordTrace (prefixWord ++ tailWord_7172310) baseStart_7172310 baseEnd_7172310 := by
    simpa [prefixWord, tailWord_7172310, baseEnd_7172310] using wordTrace_append hprefix tailTrace_7172310
  have hstable : (prefixWord ++ tailWord_7172310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172310).length < 2 ^ (prefixWord ++ tailWord_7172310).sum := by decide
  have hdescent : baseEnd_7172310 < baseStart_7172310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172317 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7172317 : Nat := 118140960795 + 7172317 * 2 ^ 59
def prefixEnd_7172317 : Nat := 4983230072969 + 3 ^ 40 * 7172317 * 2
def baseEnd_7172317 : Nat := 3682846027413520010452621

theorem tailTrace_7172317 : CollatzResearch.WordTrace tailWord_7172317 prefixEnd_7172317 3682846027413520010452621 := by
  unfold tailWord_7172317
  simp only [CollatzResearch.WordTrace]
  refine ⟨261595891956927918066715205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174397261304618612044476803 261595891956927918066715205)
  ·
    refine ⟨49049229741923984637509101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261595891956927918066715205 49049229741923984637509101)
    ·
      refine ⟨18393461153221494239065913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49049229741923984637509101 18393461153221494239065913)
      ·
        refine ⟨13795095864916120679299435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18393461153221494239065913 13795095864916120679299435)
        ·
          refine ⟨20692643797374181018949153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795095864916120679299435 20692643797374181018949153)
          ·
            refine ⟨15519482848030635764211865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20692643797374181018949153 15519482848030635764211865)
            ·
              refine ⟨11639612136022976823158899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15519482848030635764211865 11639612136022976823158899)
              ·
                refine ⟨17459418204034465234738349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639612136022976823158899 17459418204034465234738349)
                ·
                  refine ⟨6547281826512924463026881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17459418204034465234738349 6547281826512924463026881)
                  ·
                    refine ⟨4910461369884693347270161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547281826512924463026881 4910461369884693347270161)
                    ·
                      refine ⟨3682846027413520010452621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910461369884693347270161 3682846027413520010452621)
                      ·
                        rfl

theorem cell23_7172317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7172317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172317 prefixEnd_7172317 := by exact prefixLift 7172317
  have htrace : WordTrace (prefixWord ++ tailWord_7172317) baseStart_7172317 baseEnd_7172317 := by
    simpa [prefixWord, tailWord_7172317, baseEnd_7172317] using wordTrace_append hprefix tailTrace_7172317
  have hstable : (prefixWord ++ tailWord_7172317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172317).length < 2 ^ (prefixWord ++ tailWord_7172317).sum := by decide
  have hdescent : baseEnd_7172317 < baseStart_7172317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172349 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_7172349 : Nat := 118140960795 + 7172349 * 2 ^ 59
def prefixEnd_7172349 : Nat := 4983230072969 + 3 ^ 40 * 7172349 * 2
def baseEnd_7172349 : Nat := 1227620819598154628417491

theorem tailTrace_7172349 : CollatzResearch.WordTrace tailWord_7172349 prefixEnd_7172349 1227620819598154628417491 := by
  unfold tailWord_7172349
  simp only [CollatzResearch.WordTrace]
  refine ⟨261597059092811987531880101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174398039395207991687920067 261597059092811987531880101)
  ·
    refine ⟨49049448579902247662227519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261597059092811987531880101 49049448579902247662227519)
    ·
      refine ⟨73574172869853371493341279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49049448579902247662227519 73574172869853371493341279)
      ·
        refine ⟨110361259304780057240011919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73574172869853371493341279 110361259304780057240011919)
        ·
          refine ⟨165541888957170085860017879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110361259304780057240011919 165541888957170085860017879)
          ·
            refine ⟨248312833435755128790026819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165541888957170085860017879 248312833435755128790026819)
            ·
              refine ⟨372469250153632693185040229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248312833435755128790026819 372469250153632693185040229)
              ·
                refine ⟨69837984403806129972195043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372469250153632693185040229 69837984403806129972195043)
                ·
                  refine ⟨104756976605709194958292565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69837984403806129972195043 104756976605709194958292565)
                  ·
                    refine ⟨1227620819598154628417491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104756976605709194958292565 1227620819598154628417491)
                    ·
                      rfl

theorem cell23_7172349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_7172349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172349 prefixEnd_7172349 := by exact prefixLift 7172349
  have htrace : WordTrace (prefixWord ++ tailWord_7172349) baseStart_7172349 baseEnd_7172349 := by
    simpa [prefixWord, tailWord_7172349, baseEnd_7172349] using wordTrace_append hprefix tailTrace_7172349
  have hstable : (prefixWord ++ tailWord_7172349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172349).length < 2 ^ (prefixWord ++ tailWord_7172349).sum := by decide
  have hdescent : baseEnd_7172349 < baseStart_7172349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172360 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_7172360 : Nat := 118140960795 + 7172360 * 2 ^ 59
def prefixEnd_7172360 : Nat := 4983230072969 + 3 ^ 40 * 7172360 * 2
def baseEnd_7172360 : Nat := 3682868107081663342214923

theorem tailTrace_7172360 : CollatzResearch.WordTrace tailWord_7172360 prefixEnd_7172360 3682868107081663342214923 := by
  unfold tailWord_7172360
  simp only [CollatzResearch.WordTrace]
  refine ⟨130798730147886068205265267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174398306863848090940353689 130798730147886068205265267)
  ·
    refine ⟨196198095221829102307897901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130798730147886068205265267 196198095221829102307897901)
    ·
      refine ⟨73574285708185913365461713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196198095221829102307897901 73574285708185913365461713)
      ·
        refine ⟨55180714281139435024096285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73574285708185913365461713 55180714281139435024096285)
        ·
          refine ⟨20692767855427288134036107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55180714281139435024096285 20692767855427288134036107)
          ·
            refine ⟨31039151783140932201054161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20692767855427288134036107 31039151783140932201054161)
            ·
              refine ⟨23279363837355699150790621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31039151783140932201054161 23279363837355699150790621)
              ·
                refine ⟨8729761439008387181546483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23279363837355699150790621 8729761439008387181546483)
                ·
                  refine ⟨13094642158512580772319725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729761439008387181546483 13094642158512580772319725)
                  ·
                    refine ⟨4910490809442217789619897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13094642158512580772319725 4910490809442217789619897)
                    ·
                      refine ⟨3682868107081663342214923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910490809442217789619897 3682868107081663342214923)
                      ·
                        rfl

theorem cell23_7172360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_7172360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172360 prefixEnd_7172360 := by exact prefixLift 7172360
  have htrace : WordTrace (prefixWord ++ tailWord_7172360) baseStart_7172360 baseEnd_7172360 := by
    simpa [prefixWord, tailWord_7172360, baseEnd_7172360] using wordTrace_append hprefix tailTrace_7172360
  have hstable : (prefixWord ++ tailWord_7172360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172360).length < 2 ^ (prefixWord ++ tailWord_7172360).sum := by decide
  have hdescent : baseEnd_7172360 < baseStart_7172360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172376 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7172376 : Nat := 118140960795 + 7172376 * 2 ^ 59
def prefixEnd_7172376 : Nat := 4983230072969 + 3 ^ 40 * 7172376 * 2
def baseEnd_7172376 : Nat := 3682876322772135279614849

theorem tailTrace_7172376 : CollatzResearch.WordTrace tailWord_7172376 prefixEnd_7172376 3682876322772135279614849 := by
  unfold tailWord_7172376
  simp only [CollatzResearch.WordTrace]
  refine ⟨130799021931857085571556491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174398695909142780762075321 130799021931857085571556491)
  ·
    refine ⟨196198532897785628357334737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130799021931857085571556491 196198532897785628357334737)
    ·
      refine ⟨147148899673339221268001053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196198532897785628357334737 147148899673339221268001053)
      ·
        refine ⟨55180837377502207975500395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147148899673339221268001053 55180837377502207975500395)
        ·
          refine ⟨82771256066253311963250593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55180837377502207975500395 82771256066253311963250593)
          ·
            refine ⟨62078442049689983972437945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82771256066253311963250593 62078442049689983972437945)
            ·
              refine ⟨46558831537267487979328459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62078442049689983972437945 46558831537267487979328459)
              ·
                refine ⟨69838247305901231968992689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46558831537267487979328459 69838247305901231968992689)
                ·
                  refine ⟨52378685479425923976744517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69838247305901231968992689 52378685479425923976744517)
                  ·
                    refine ⟨9821003527392360745639597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52378685479425923976744517 9821003527392360745639597)
                    ·
                      refine ⟨3682876322772135279614849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821003527392360745639597 3682876322772135279614849)
                      ·
                        rfl

theorem cell23_7172376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7172376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172376 prefixEnd_7172376 := by exact prefixLift 7172376
  have htrace : WordTrace (prefixWord ++ tailWord_7172376) baseStart_7172376 baseEnd_7172376 := by
    simpa [prefixWord, tailWord_7172376, baseEnd_7172376] using wordTrace_append hprefix tailTrace_7172376
  have hstable : (prefixWord ++ tailWord_7172376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172376).length < 2 ^ (prefixWord ++ tailWord_7172376).sum := by decide
  have hdescent : baseEnd_7172376 < baseStart_7172376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172394 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7172394 : Nat := 118140960795 + 7172394 * 2 ^ 59
def prefixEnd_7172394 : Nat := 4983230072969 + 3 ^ 40 * 7172394 * 2
def baseEnd_7172394 : Nat := 3682885565423916209189767

theorem tailTrace_7172394 : CollatzResearch.WordTrace tailWord_7172394 prefixEnd_7172394 3682885565423916209189767 := by
  unfold tailWord_7172394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65399675094412240054317059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174399133585099306811512157 65399675094412240054317059)
  ·
    refine ⟨98099512641618360081475589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65399675094412240054317059 98099512641618360081475589)
    ·
      refine ⟨18393658620303442515276673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98099512641618360081475589 18393658620303442515276673)
      ·
        refine ⟨13795243965227581886457505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18393658620303442515276673 13795243965227581886457505)
        ·
          refine ⟨10346432973920686414843129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13795243965227581886457505 10346432973920686414843129)
          ·
            refine ⟨7759824730440514811132347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346432973920686414843129 7759824730440514811132347)
            ·
              refine ⟨11639737095660772216698521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759824730440514811132347 11639737095660772216698521)
              ·
                refine ⟨8729802821745579162523891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639737095660772216698521 8729802821745579162523891)
                ·
                  refine ⟨13094704232618368743785837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729802821745579162523891 13094704232618368743785837)
                  ·
                    refine ⟨4910514087231888278919689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13094704232618368743785837 4910514087231888278919689)
                    ·
                      refine ⟨3682885565423916209189767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910514087231888278919689 3682885565423916209189767)
                      ·
                        rfl

theorem cell23_7172394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7172394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172394 prefixEnd_7172394 := by exact prefixLift 7172394
  have htrace : WordTrace (prefixWord ++ tailWord_7172394) baseStart_7172394 baseEnd_7172394 := by
    simpa [prefixWord, tailWord_7172394, baseEnd_7172394] using wordTrace_append hprefix tailTrace_7172394
  have hstable : (prefixWord ++ tailWord_7172394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172394).length < 2 ^ (prefixWord ++ tailWord_7172394).sum := by decide
  have hdescent : baseEnd_7172394 < baseStart_7172394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172433 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_7172433 : Nat := 118140960795 + 7172433 * 2 ^ 59
def prefixEnd_7172433 : Nat := 4983230072969 + 3 ^ 40 * 7172433 * 2
def baseEnd_7172433 : Nat := 3682905591169441556602087

theorem tailTrace_7172433 : CollatzResearch.WordTrace tailWord_7172433 prefixEnd_7172433 3682905591169441556602087 := by
  unfold tailWord_7172433
  simp only [CollatzResearch.WordTrace]
  refine ⟨261600122824507669877937953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174400081883005113251958635 261600122824507669877937953)
  ·
    refine ⟨196200092118380752408453465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261600122824507669877937953 196200092118380752408453465)
    ·
      refine ⟨147150069088785564306340099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196200092118380752408453465 147150069088785564306340099)
      ·
        refine ⟨220725103633178346459510149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147150069088785564306340099 220725103633178346459510149)
        ·
          refine ⟨41385956931220939961158153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220725103633178346459510149 41385956931220939961158153)
          ·
            refine ⟨31039467698415704970868615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41385956931220939961158153 31039467698415704970868615)
            ·
              refine ⟨46559201547623557456302923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31039467698415704970868615 46559201547623557456302923)
              ·
                refine ⟨69838802321435336184454385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46559201547623557456302923 69838802321435336184454385)
                ·
                  refine ⟨52379101741076502138340789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69838802321435336184454385 52379101741076502138340789)
                  ·
                    refine ⟨4910540788225922075469449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52379101741076502138340789 4910540788225922075469449)
                    ·
                      refine ⟨3682905591169441556602087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910540788225922075469449 3682905591169441556602087)
                      ·
                        rfl

theorem cell23_7172433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_7172433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172433 prefixEnd_7172433 := by exact prefixLift 7172433
  have htrace : WordTrace (prefixWord ++ tailWord_7172433) baseStart_7172433 baseEnd_7172433 := by
    simpa [prefixWord, tailWord_7172433, baseEnd_7172433] using wordTrace_append hprefix tailTrace_7172433
  have hstable : (prefixWord ++ tailWord_7172433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172433).length < 2 ^ (prefixWord ++ tailWord_7172433).sum := by decide
  have hdescent : baseEnd_7172433 < baseStart_7172433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172460 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_7172460 : Nat := 118140960795 + 7172460 * 2 ^ 59
def prefixEnd_7172460 : Nat := 4983230072969 + 3 ^ 40 * 7172460 * 2
def baseEnd_7172460 : Nat := 1227639818382370983654821

theorem tailTrace_7172460 : CollatzResearch.WordTrace tailWord_7172460 prefixEnd_7172460 1227639818382370983654821 := by
  unfold tailWord_7172460
  simp only [CollatzResearch.WordTrace]
  refine ⟨130800553797704926744585417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174400738396939902326113889 130800553797704926744585417)
  ·
    refine ⟨98100415348278695058439063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130800553797704926744585417 98100415348278695058439063)
    ·
      refine ⟨147150623022418042587658595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98100415348278695058439063 147150623022418042587658595)
      ·
        refine ⟨220725934533627063881487893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147150623022418042587658595 220725934533627063881487893)
        ·
          refine ⟨10346528181263768619444745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220725934533627063881487893 10346528181263768619444745)
          ·
            refine ⟨7759896135947826464583559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346528181263768619444745 7759896135947826464583559)
            ·
              refine ⟨11639844203921739696875339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759896135947826464583559 11639844203921739696875339)
              ·
                refine ⟨17459766305882609545313009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639844203921739696875339 17459766305882609545313009)
                ·
                  refine ⟨13094824729411957158984757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17459766305882609545313009 13094824729411957158984757)
                  ·
                    refine ⟨1227639818382370983654821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13094824729411957158984757 1227639818382370983654821)
                    ·
                      rfl

theorem cell23_7172460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_7172460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172460 prefixEnd_7172460 := by exact prefixLift 7172460
  have htrace : WordTrace (prefixWord ++ tailWord_7172460) baseStart_7172460 baseEnd_7172460 := by
    simpa [prefixWord, tailWord_7172460, baseEnd_7172460] using wordTrace_append hprefix tailTrace_7172460
  have hstable : (prefixWord ++ tailWord_7172460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172460).length < 2 ^ (prefixWord ++ tailWord_7172460).sum := by decide
  have hdescent : baseEnd_7172460 < baseStart_7172460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172576 : List Nat := [2, 1, 1, 3, 1, 1, 3, 11]
def baseStart_7172576 : Nat := 118140960795 + 7172576 * 2 ^ 59
def prefixEnd_7172576 : Nat := 4983230072969 + 3 ^ 40 * 7172576 * 2
def baseEnd_7172576 : Nat := 136406630329742018411627

theorem tailTrace_7172576 : CollatzResearch.WordTrace tailWord_7172576 prefixEnd_7172576 136406630329742018411627 := by
  unfold tailWord_7172576
  simp only [CollatzResearch.WordTrace]
  refine ⟨130802669231494802650196791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174403558975326403533595721 130802669231494802650196791)
  ·
    refine ⟨196204003847242203975295187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130802669231494802650196791 196204003847242203975295187)
    ·
      refine ⟨294306005770863305962942781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196204003847242203975295187 294306005770863305962942781)
      ·
        refine ⟨110364752164073739736103543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294306005770863305962942781 110364752164073739736103543)
        ·
          refine ⟨165547128246110609604155315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110364752164073739736103543 165547128246110609604155315)
          ·
            refine ⟨248320692369165914406232973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165547128246110609604155315 248320692369165914406232973)
            ·
              refine ⟨93120259638437217902337365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248320692369165914406232973 93120259638437217902337365)
              ·
                refine ⟨136406630329742018411627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93120259638437217902337365 136406630329742018411627)
                ·
                  rfl

theorem cell23_7172576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_7172576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172576 prefixEnd_7172576 := by exact prefixLift 7172576
  have htrace : WordTrace (prefixWord ++ tailWord_7172576) baseStart_7172576 baseEnd_7172576 := by
    simpa [prefixWord, tailWord_7172576, baseEnd_7172576] using wordTrace_append hprefix tailTrace_7172576
  have hstable : (prefixWord ++ tailWord_7172576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172576).length < 2 ^ (prefixWord ++ tailWord_7172576).sum := by decide
  have hdescent : baseEnd_7172576 < baseStart_7172576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172590 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_7172590 : Nat := 118140960795 + 7172590 * 2 ^ 59
def prefixEnd_7172590 : Nat := 4983230072969 + 3 ^ 40 * 7172590 * 2
def baseEnd_7172590 : Nat := 3682986207632197442338865

theorem tailTrace_7172590 : CollatzResearch.WordTrace tailWord_7172590 prefixEnd_7172590 3682986207632197442338865 := by
  unfold tailWord_7172590
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700731135617360711425403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174403899389959257127602149 32700731135617360711425403)
  ·
    refine ⟨49051096703426041067138105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32700731135617360711425403 49051096703426041067138105)
    ·
      refine ⟨36788322527569530800353579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49051096703426041067138105 36788322527569530800353579)
      ·
        refine ⟨55182483791354296200530369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36788322527569530800353579 55182483791354296200530369)
        ·
          refine ⟨41386862843515722150397777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55182483791354296200530369 41386862843515722150397777)
          ·
            refine ⟨31040147132636791612798333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41386862843515722150397777 31040147132636791612798333)
            ·
              refine ⟨11640055174738796854799375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31040147132636791612798333 11640055174738796854799375)
              ·
                refine ⟨17460082762108195282199063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640055174738796854799375 17460082762108195282199063)
                ·
                  refine ⟨26190124143162292923298595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460082762108195282199063 26190124143162292923298595)
                  ·
                    refine ⟨39285186214743439384947893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26190124143162292923298595 39285186214743439384947893)
                    ·
                      refine ⟨3682986207632197442338865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39285186214743439384947893 3682986207632197442338865)
                      ·
                        rfl

theorem cell23_7172590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_7172590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172590 prefixEnd_7172590 := by exact prefixLift 7172590
  have htrace : WordTrace (prefixWord ++ tailWord_7172590) baseStart_7172590 baseEnd_7172590 := by
    simpa [prefixWord, tailWord_7172590, baseEnd_7172590] using wordTrace_append hprefix tailTrace_7172590
  have hstable : (prefixWord ++ tailWord_7172590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172590).length < 2 ^ (prefixWord ++ tailWord_7172590).sum := by decide
  have hdescent : baseEnd_7172590 < baseStart_7172590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172614 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7172614 : Nat := 118140960795 + 7172614 * 2 ^ 59
def prefixEnd_7172614 : Nat := 4983230072969 + 3 ^ 40 * 7172614 * 2
def baseEnd_7172614 : Nat := 1227666177055968449479585

theorem tailTrace_7172614 : CollatzResearch.WordTrace tailWord_7172614 prefixEnd_7172614 1227666177055968449479585 := by
  unfold tailWord_7172614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175210138651623055946153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174404482957901291860184597 8175210138651623055946153)
  ·
    refine ⟨6131407603988717291959615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8175210138651623055946153 6131407603988717291959615)
    ·
      refine ⟨9197111405983075937939423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131407603988717291959615 9197111405983075937939423)
      ·
        refine ⟨13795667108974613906909135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197111405983075937939423 13795667108974613906909135)
        ·
          refine ⟨20693500663461920860363703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795667108974613906909135 20693500663461920860363703)
          ·
            refine ⟨31040250995192881290545555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20693500663461920860363703 31040250995192881290545555)
            ·
              refine ⟨46560376492789321935818333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31040250995192881290545555 46560376492789321935818333)
              ·
                refine ⟨17460141184795995725931875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46560376492789321935818333 17460141184795995725931875)
                ·
                  refine ⟨26190211777193993588897813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460141184795995725931875 26190211777193993588897813)
                  ·
                    refine ⟨1227666177055968449479585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26190211777193993588897813 1227666177055968449479585)
                    ·
                      rfl

theorem cell23_7172614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7172614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172614 prefixEnd_7172614 := by exact prefixLift 7172614
  have htrace : WordTrace (prefixWord ++ tailWord_7172614) baseStart_7172614 baseEnd_7172614 := by
    simpa [prefixWord, tailWord_7172614, baseEnd_7172614] using wordTrace_append hprefix tailTrace_7172614
  have hstable : (prefixWord ++ tailWord_7172614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172614).length < 2 ^ (prefixWord ++ tailWord_7172614).sum := by decide
  have hdescent : baseEnd_7172614 < baseStart_7172614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172620 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_7172620 : Nat := 118140960795 + 7172620 * 2 ^ 59
def prefixEnd_7172620 : Nat := 4983230072969 + 3 ^ 40 * 7172620 * 2
def baseEnd_7172620 : Nat := 3683001612051832324963727

theorem tailTrace_7172620 : CollatzResearch.WordTrace tailWord_7172620 prefixEnd_7172620 3683001612051832324963727 := by
  unfold tailWord_7172620
  simp only [CollatzResearch.WordTrace]
  refine ⟨130803471637415100407497657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174404628849886800543330209 130803471637415100407497657)
  ·
    refine ⟨98102603728061325305623243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130803471637415100407497657 98102603728061325305623243)
    ·
      refine ⟨147153905592091987958434865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98102603728061325305623243 147153905592091987958434865)
      ·
        refine ⟨110365429194068990968826149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147153905592091987958434865 110365429194068990968826149)
        ·
          refine ⟨20693517973887935806654903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110365429194068990968826149 20693517973887935806654903)
          ·
            refine ⟨31040276960831903709982355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20693517973887935806654903 31040276960831903709982355)
            ·
              refine ⟨46560415441247855564973533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31040276960831903709982355 46560415441247855564973533)
              ·
                refine ⟨17460155790467945836865075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46560415441247855564973533 17460155790467945836865075)
                ·
                  refine ⟨26190233685701918755297613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460155790467945836865075 26190233685701918755297613)
                  ·
                    refine ⟨9821337632138219533236605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26190233685701918755297613 9821337632138219533236605)
                    ·
                      refine ⟨3683001612051832324963727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821337632138219533236605 3683001612051832324963727)
                      ·
                        rfl

theorem cell23_7172620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_7172620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172620 prefixEnd_7172620 := by exact prefixLift 7172620
  have htrace : WordTrace (prefixWord ++ tailWord_7172620) baseStart_7172620 baseEnd_7172620 := by
    simpa [prefixWord, tailWord_7172620, baseEnd_7172620] using wordTrace_append hprefix tailTrace_7172620
  have hstable : (prefixWord ++ tailWord_7172620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172620).length < 2 ^ (prefixWord ++ tailWord_7172620).sum := by decide
  have hdescent : baseEnd_7172620 < baseStart_7172620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172621 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7172621 : Nat := 118140960795 + 7172621 * 2 ^ 59
def prefixEnd_7172621 : Nat := 4983230072969 + 3 ^ 40 * 7172621 * 2
def baseEnd_7172621 : Nat := 3683002125532486821051223

theorem tailTrace_7172621 : CollatzResearch.WordTrace tailWord_7172621 prefixEnd_7172621 3683002125532486821051223 := by
  unfold tailWord_7172621
  simp only [CollatzResearch.WordTrace]
  refine ⟨261606979747826577985781717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174404653165217718657187811 261606979747826577985781717)
  ·
    refine ⟨6131413587839685421541759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 261606979747826577985781717 6131413587839685421541759)
    ·
      refine ⟨9197120381759528132312639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131413587839685421541759 9197120381759528132312639)
      ·
        refine ⟨13795680572639292198468959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197120381759528132312639 13795680572639292198468959)
        ·
          refine ⟨20693520858958938297703439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795680572639292198468959 20693520858958938297703439)
          ·
            refine ⟨31040281288438407446555159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20693520858958938297703439 31040281288438407446555159)
            ·
              refine ⟨46560421932657611169832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31040281288438407446555159 46560421932657611169832739)
              ·
                refine ⟨69840632898986416754749109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46560421932657611169832739 69840632898986416754749109)
                ·
                  refine ⟨6547559334279976570757729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69840632898986416754749109 6547559334279976570757729)
                  ·
                    refine ⟨4910669500709982428068297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547559334279976570757729 4910669500709982428068297)
                    ·
                      refine ⟨3683002125532486821051223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910669500709982428068297 3683002125532486821051223)
                      ·
                        rfl

theorem cell23_7172621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7172621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172621 prefixEnd_7172621 := by exact prefixLift 7172621
  have htrace : WordTrace (prefixWord ++ tailWord_7172621) baseStart_7172621 baseEnd_7172621 := by
    simpa [prefixWord, tailWord_7172621, baseEnd_7172621] using wordTrace_append hprefix tailTrace_7172621
  have hstable : (prefixWord ++ tailWord_7172621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172621).length < 2 ^ (prefixWord ++ tailWord_7172621).sum := by decide
  have hdescent : baseEnd_7172621 < baseStart_7172621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172654 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7172654 : Nat := 118140960795 + 7172654 * 2 ^ 59
def prefixEnd_7172654 : Nat := 4983230072969 + 3 ^ 40 * 7172654 * 2
def baseEnd_7172654 : Nat := 3683019070394085191938571

theorem tailTrace_7172654 : CollatzResearch.WordTrace tailWord_7172654 prefixEnd_7172654 3683019070394085191938571 := by
  unfold tailWord_7172654
  simp only [CollatzResearch.WordTrace]
  refine ⟨32701022919588378077716627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174405455571138016414488677 32701022919588378077716627)
  ·
    refine ⟨49051534379382567116574941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32701022919588378077716627 49051534379382567116574941)
    ·
      refine ⟨18394325392268462668715603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49051534379382567116574941 18394325392268462668715603)
      ·
        refine ⟨27591488088402694003073405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394325392268462668715603 27591488088402694003073405)
        ·
          refine ⟨10346808033151010251152527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27591488088402694003073405 10346808033151010251152527)
          ·
            refine ⟨15520212049726515376728791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346808033151010251152527 15520212049726515376728791)
            ·
              refine ⟨23280318074589773065093187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15520212049726515376728791 23280318074589773065093187)
              ·
                refine ⟨34920477111884659597639781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23280318074589773065093187 34920477111884659597639781)
                ·
                  refine ⟨6547589458478373674557459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34920477111884659597639781 6547589458478373674557459)
                  ·
                    refine ⟨9821384187717560511836189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6547589458478373674557459 9821384187717560511836189)
                    ·
                      refine ⟨3683019070394085191938571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821384187717560511836189 3683019070394085191938571)
                      ·
                        rfl

theorem cell23_7172654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7172654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172654 prefixEnd_7172654 := by exact prefixLift 7172654
  have htrace : WordTrace (prefixWord ++ tailWord_7172654) baseStart_7172654 baseEnd_7172654 := by
    simpa [prefixWord, tailWord_7172654, baseEnd_7172654] using wordTrace_append hprefix tailTrace_7172654
  have hstable : (prefixWord ++ tailWord_7172654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172654).length < 2 ^ (prefixWord ++ tailWord_7172654).sum := by decide
  have hdescent : baseEnd_7172654 < baseStart_7172654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172677 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_7172677 : Nat := 118140960795 + 7172677 * 2 ^ 59
def prefixEnd_7172677 : Nat := 4983230072969 + 3 ^ 40 * 7172677 * 2
def baseEnd_7172677 : Nat := 3683030880449138601950965

theorem tailTrace_7172677 : CollatzResearch.WordTrace tailWord_7172677 prefixEnd_7172677 3683030880449138601950965 := by
  unfold tailWord_7172677
  simp only [CollatzResearch.WordTrace]
  refine ⟨261609022235623699549820285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174406014823749133033213523 261609022235623699549820285)
  ·
    refine ⟨98103383338358887331182607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261609022235623699549820285 98103383338358887331182607)
    ·
      refine ⟨147155075007538330996773911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98103383338358887331182607 147155075007538330996773911)
      ·
        refine ⟨220732612511307496495160867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147155075007538330996773911 220732612511307496495160867)
        ·
          refine ⟨331098918766961244742741301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220732612511307496495160867 331098918766961244742741301)
          ·
            refine ⟨31040523634402616694631997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331098918766961244742741301 31040523634402616694631997)
            ·
              refine ⟨11640196362900981260486999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31040523634402616694631997 11640196362900981260486999)
              ·
                refine ⟨17460294544351471890730499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640196362900981260486999 17460294544351471890730499)
                ·
                  refine ⟨26190441816527207836095749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460294544351471890730499 26190441816527207836095749)
                  ·
                    refine ⟨4910707840598851469267953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26190441816527207836095749 4910707840598851469267953)
                    ·
                      refine ⟨3683030880449138601950965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910707840598851469267953 3683030880449138601950965)
                      ·
                        rfl

theorem cell23_7172677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_7172677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172677 prefixEnd_7172677 := by exact prefixLift 7172677
  have htrace : WordTrace (prefixWord ++ tailWord_7172677) baseStart_7172677 baseEnd_7172677 := by
    simpa [prefixWord, tailWord_7172677, baseEnd_7172677] using wordTrace_append hprefix tailTrace_7172677
  have hstable : (prefixWord ++ tailWord_7172677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172677).length < 2 ^ (prefixWord ++ tailWord_7172677).sum := by decide
  have hdescent : baseEnd_7172677 < baseStart_7172677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172683 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 7]
def baseStart_7172683 : Nat := 118140960795 + 7172683 * 2 ^ 59
def prefixEnd_7172683 : Nat := 4983230072969 + 3 ^ 40 * 7172683 * 2
def baseEnd_7172683 : Nat := 409225995703673953163993

theorem tailTrace_7172683 : CollatzResearch.WordTrace tailWord_7172683 prefixEnd_7172683 409225995703673953163993 := by
  unfold tailWord_7172683
  simp only [CollatzResearch.WordTrace]
  refine ⟨261609241073601962574538703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174406160715734641716359135 261609241073601962574538703)
  ·
    refine ⟨392413861610402943861808055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261609241073601962574538703 392413861610402943861808055)
    ·
      refine ⟨588620792415604415792712083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392413861610402943861808055 588620792415604415792712083)
      ·
        refine ⟨882931188623406623689068125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588620792415604415792712083 882931188623406623689068125)
        ·
          refine ⟨331099195733777483883400547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 882931188623406623689068125 331099195733777483883400547)
          ·
            refine ⟨496648793600666225825100821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331099195733777483883400547 496648793600666225825100821)
            ·
              refine ⟨23280412200031229335551601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496648793600666225825100821 23280412200031229335551601)
              ·
                refine ⟨17460309150023422001663701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23280412200031229335551601 17460309150023422001663701)
                ·
                  refine ⟨409225995703673953163993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17460309150023422001663701 409225995703673953163993)
                  ·
                    rfl

theorem cell23_7172683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 7].length) (baseStart_7172683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172683 prefixEnd_7172683 := by exact prefixLift 7172683
  have htrace : WordTrace (prefixWord ++ tailWord_7172683) baseStart_7172683 baseEnd_7172683 := by
    simpa [prefixWord, tailWord_7172683, baseEnd_7172683] using wordTrace_append hprefix tailTrace_7172683
  have hstable : (prefixWord ++ tailWord_7172683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172683).length < 2 ^ (prefixWord ++ tailWord_7172683).sum := by decide
  have hdescent : baseEnd_7172683 < baseStart_7172683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172717 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 7]
def baseStart_7172717 : Nat := 118140960795 + 7172717 * 2 ^ 59
def prefixEnd_7172717 : Nat := 4983230072969 + 3 ^ 40 * 7172717 * 2
def baseEnd_7172717 : Nat := 409227935519479827272309

theorem tailTrace_7172717 : CollatzResearch.WordTrace tailWord_7172717 prefixEnd_7172717 409227935519479827272309 := by
  unfold tailWord_7172717
  simp only [CollatzResearch.WordTrace]
  refine ⟨261610481155478786381276405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174406987436985857587517603 261610481155478786381276405)
  ·
    refine ⟨24525982608326136223244663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261610481155478786381276405 24525982608326136223244663)
    ·
      refine ⟨36788973912489204334866995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525982608326136223244663 36788973912489204334866995)
      ·
        refine ⟨55183460868733806502300493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36788973912489204334866995 55183460868733806502300493)
        ·
          refine ⟨20693797825775177438362685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55183460868733806502300493 20693797825775177438362685)
          ·
            refine ⟨7760174184665691539386007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20693797825775177438362685 7760174184665691539386007)
            ·
              refine ⟨11640261276998537309079011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760174184665691539386007 11640261276998537309079011)
              ·
                refine ⟨17460391915497805963618517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640261276998537309079011 17460391915497805963618517)
                ·
                  refine ⟨409227935519479827272309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17460391915497805963618517 409227935519479827272309)
                  ·
                    rfl

theorem cell23_7172717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_7172717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172717 prefixEnd_7172717 := by exact prefixLift 7172717
  have htrace : WordTrace (prefixWord ++ tailWord_7172717) baseStart_7172717 baseEnd_7172717 := by
    simpa [prefixWord, tailWord_7172717, baseEnd_7172717] using wordTrace_append hprefix tailTrace_7172717
  have hstable : (prefixWord ++ tailWord_7172717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172717).length < 2 ^ (prefixWord ++ tailWord_7172717).sum := by decide
  have hdescent : baseEnd_7172717 < baseStart_7172717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172763 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_7172763 : Nat := 118140960795 + 7172763 * 2 ^ 59
def prefixEnd_7172763 : Nat := 4983230072969 + 3 ^ 40 * 7172763 * 2
def baseEnd_7172763 : Nat := 3683075039785425265475569

theorem tailTrace_7172763 : CollatzResearch.WordTrace tailWord_7172763 prefixEnd_7172763 3683075039785425265475569 := by
  unfold tailWord_7172763
  simp only [CollatzResearch.WordTrace]
  refine ⟨261612158913312136237450943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174408105942208090824967295 261612158913312136237450943)
  ·
    refine ⟨392418238369968204356176415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261612158913312136237450943 392418238369968204356176415)
    ·
      refine ⟨588627357554952306534264623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392418238369968204356176415 588627357554952306534264623)
      ·
        refine ⟨882941036332428459801396935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588627357554952306534264623 882941036332428459801396935)
        ·
          refine ⟨1324411554498642689702095403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882941036332428459801396935 1324411554498642689702095403)
          ·
            refine ⟨1986617331747964034553143105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324411554498642689702095403 1986617331747964034553143105)
            ·
              refine ⟨1489962998810973025914857329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986617331747964034553143105 1489962998810973025914857329)
              ·
                refine ⟨1117472249108229769436142997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489962998810973025914857329 1117472249108229769436142997)
                ·
                  refine ⟨52381511676948270442319203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1117472249108229769436142997 52381511676948270442319203)
                  ·
                    refine ⟨78572267515422405663478805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52381511676948270442319203 78572267515422405663478805)
                    ·
                      refine ⟨3683075039785425265475569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78572267515422405663478805 3683075039785425265475569)
                      ·
                        rfl

theorem cell23_7172763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_7172763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172763 prefixEnd_7172763 := by exact prefixLift 7172763
  have htrace : WordTrace (prefixWord ++ tailWord_7172763) baseStart_7172763 baseEnd_7172763 := by
    simpa [prefixWord, tailWord_7172763, baseEnd_7172763] using wordTrace_append hprefix tailTrace_7172763
  have hstable : (prefixWord ++ tailWord_7172763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172763).length < 2 ^ (prefixWord ++ tailWord_7172763).sum := by decide
  have hdescent : baseEnd_7172763 < baseStart_7172763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172804 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7172804 : Nat := 118140960795 + 7172804 * 2 ^ 59
def prefixEnd_7172804 : Nat := 4983230072969 + 3 ^ 40 * 7172804 * 2
def baseEnd_7172804 : Nat := 3683096092492259605062881

theorem tailTrace_7172804 : CollatzResearch.WordTrace tailWord_7172804 prefixEnd_7172804 3683096092492259605062881 := by
  unfold tailWord_7172804
  simp only [CollatzResearch.WordTrace]
  refine ⟨130806827153081800119846733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174409102870775733493128977 130806827153081800119846733)
  ·
    refine ⟨49052560182405675044942525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130806827153081800119846733 49052560182405675044942525)
    ·
      refine ⟨18394710068402128141853447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49052560182405675044942525 18394710068402128141853447)
      ·
        refine ⟨27592065102603192212780171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394710068402128141853447 27592065102603192212780171)
        ·
          refine ⟨41388097653904788319170257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27592065102603192212780171 41388097653904788319170257)
          ·
            refine ⟨31041073240428591239377693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41388097653904788319170257 31041073240428591239377693)
            ·
              refine ⟨11640402465160721714766635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31041073240428591239377693 11640402465160721714766635)
              ·
                refine ⟨17460603697741082572149953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640402465160721714766635 17460603697741082572149953)
                ·
                  refine ⟨13095452773305811929112465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17460603697741082572149953 13095452773305811929112465)
                  ·
                    refine ⟨9821589579979358946834349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13095452773305811929112465 9821589579979358946834349)
                    ·
                      refine ⟨3683096092492259605062881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821589579979358946834349 3683096092492259605062881)
                      ·
                        rfl

theorem cell23_7172804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7172804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172804 prefixEnd_7172804 := by exact prefixLift 7172804
  have htrace : WordTrace (prefixWord ++ tailWord_7172804) baseStart_7172804 baseEnd_7172804 := by
    simpa [prefixWord, tailWord_7172804, baseEnd_7172804] using wordTrace_append hprefix tailTrace_7172804
  have hstable : (prefixWord ++ tailWord_7172804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172804).length < 2 ^ (prefixWord ++ tailWord_7172804).sum := by decide
  have hdescent : baseEnd_7172804 < baseStart_7172804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172817 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_7172817 : Nat := 118140960795 + 7172817 * 2 ^ 59
def prefixEnd_7172817 : Nat := 4983230072969 + 3 ^ 40 * 7172817 * 2
def baseEnd_7172817 : Nat := 3683102767740768054200321

theorem tailTrace_7172817 : CollatzResearch.WordTrace tailWord_7172817 prefixEnd_7172817 3683102767740768054200321 := by
  unfold tailWord_7172817
  simp only [CollatzResearch.WordTrace]
  refine ⟨261614128455116503459916705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174409418970077668973277803 261614128455116503459916705)
  ·
    refine ⟨196210596341337377594937529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261614128455116503459916705 196210596341337377594937529)
    ·
      refine ⟨147157947256003033196203147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196210596341337377594937529 147157947256003033196203147)
      ·
        refine ⟨220736920884004549794304721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147157947256003033196203147 220736920884004549794304721)
        ·
          refine ⟨165552690663003412345728541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220736920884004549794304721 165552690663003412345728541)
          ·
            refine ⟨62082258998626279629648203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165552690663003412345728541 62082258998626279629648203)
            ·
              refine ⟨93123388497939419444472305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62082258998626279629648203 93123388497939419444472305)
              ·
                refine ⟨69842541373454564583354229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93123388497939419444472305 69842541373454564583354229)
                ·
                  refine ⟨6547738253761365429689459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69842541373454564583354229 6547738253761365429689459)
                  ·
                    refine ⟨9821607380642048144534189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6547738253761365429689459 9821607380642048144534189)
                    ·
                      refine ⟨3683102767740768054200321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821607380642048144534189 3683102767740768054200321)
                      ·
                        rfl

theorem cell23_7172817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_7172817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172817 prefixEnd_7172817 := by exact prefixLift 7172817
  have htrace : WordTrace (prefixWord ++ tailWord_7172817) baseStart_7172817 baseEnd_7172817 := by
    simpa [prefixWord, tailWord_7172817, baseEnd_7172817] using wordTrace_append hprefix tailTrace_7172817
  have hstable : (prefixWord ++ tailWord_7172817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172817).length < 2 ^ (prefixWord ++ tailWord_7172817).sum := by decide
  have hdescent : baseEnd_7172817 < baseStart_7172817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172854 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_7172854 : Nat := 118140960795 + 7172854 * 2 ^ 59
def prefixEnd_7172854 : Nat := 4983230072969 + 3 ^ 40 * 7172854 * 2
def baseEnd_7172854 : Nat := 1227707255508328136479217

theorem tailTrace_7172854 : CollatzResearch.WordTrace tailWord_7172854 prefixEnd_7172854 1227707255508328136479217 := by
  unfold tailWord_7172854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350967372248903673688351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174410318637321639186009077 16350967372248903673688351)
  ·
    refine ⟨24526451058373355510532527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350967372248903673688351 24526451058373355510532527)
    ·
      refine ⟨36789676587560033265798791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24526451058373355510532527 36789676587560033265798791)
      ·
        refine ⟨55184514881340049898698187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36789676587560033265798791 55184514881340049898698187)
        ·
          refine ⟨82776772322010074848047281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55184514881340049898698187 82776772322010074848047281)
          ·
            refine ⟨62082579241507556136035461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82776772322010074848047281 62082579241507556136035461)
            ·
              refine ⟨11640483607782666775506649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62082579241507556136035461 11640483607782666775506649)
              ·
                refine ⟨8730362705837000081629987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11640483607782666775506649 8730362705837000081629987)
                ·
                  refine ⟨13095544058755500122444981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730362705837000081629987 13095544058755500122444981)
                  ·
                    refine ⟨1227707255508328136479217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13095544058755500122444981 1227707255508328136479217)
                    ·
                      rfl

theorem cell23_7172854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_7172854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172854 prefixEnd_7172854 := by exact prefixLift 7172854
  have htrace : WordTrace (prefixWord ++ tailWord_7172854) baseStart_7172854 baseEnd_7172854 := by
    simpa [prefixWord, tailWord_7172854, baseEnd_7172854] using wordTrace_append hprefix tailTrace_7172854
  have hstable : (prefixWord ++ tailWord_7172854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172854).length < 2 ^ (prefixWord ++ tailWord_7172854).sum := by decide
  have hdescent : baseEnd_7172854 < baseStart_7172854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7172981 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7172981 : Nat := 118140960795 + 7172981 * 2 ^ 59
def prefixEnd_7172981 : Nat := 4983230072969 + 3 ^ 40 * 7172981 * 2
def baseEnd_7172981 : Nat := 3683186978568105412549567

theorem tailTrace_7172981 : CollatzResearch.WordTrace tailWord_7172981 prefixEnd_7172981 3683186978568105412549567 := by
  unfold tailWord_7172981
  simp only [CollatzResearch.WordTrace]
  refine ⟨261620110026522359468886797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174413406684348239645924531 261620110026522359468886797)
  ·
    refine ⟨98107541259945884800832549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261620110026522359468886797 98107541259945884800832549)
    ·
      refine ⟨18395163986239853400156103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98107541259945884800832549 18395163986239853400156103)
      ·
        refine ⟨27592745979359780100234155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395163986239853400156103 27592745979359780100234155)
        ·
          refine ⟨41389118969039670150351233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27592745979359780100234155 41389118969039670150351233)
          ·
            refine ⟨31041839226779752612763425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41389118969039670150351233 31041839226779752612763425)
            ·
              refine ⟨23281379420084814459572569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31041839226779752612763425 23281379420084814459572569)
              ·
                refine ⟨17461034565063610844679427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23281379420084814459572569 17461034565063610844679427)
                ·
                  refine ⟨26191551847595416267019141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17461034565063610844679427 26191551847595416267019141)
                  ·
                    refine ⟨4910915971424140550066089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26191551847595416267019141 4910915971424140550066089)
                    ·
                      refine ⟨3683186978568105412549567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910915971424140550066089 3683186978568105412549567)
                      ·
                        rfl

theorem cell23_7172981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7172981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7172981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7172981 prefixEnd_7172981 := by exact prefixLift 7172981
  have htrace : WordTrace (prefixWord ++ tailWord_7172981) baseStart_7172981 baseEnd_7172981 := by
    simpa [prefixWord, tailWord_7172981, baseEnd_7172981] using wordTrace_append hprefix tailTrace_7172981
  have hstable : (prefixWord ++ tailWord_7172981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7172981).length < 2 ^ (prefixWord ++ tailWord_7172981).sum := by decide
  have hdescent : baseEnd_7172981 < baseStart_7172981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7172981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173004 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 5]
def baseStart_7173004 : Nat := 118140960795 + 7173004 * 2 ^ 59
def prefixEnd_7173004 : Nat := 4983230072969 + 3 ^ 40 * 7173004 * 2
def baseEnd_7173004 : Nat := 409244309847017646951329

theorem tailTrace_7173004 : CollatzResearch.WordTrace tailWord_7173004 prefixEnd_7173004 409244309847017646951329 := by
  unfold tailWord_7173004
  simp only [CollatzResearch.WordTrace]
  refine ⟨130810474452719517198487033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174413965936959356264649377 130810474452719517198487033)
  ·
    refine ⟨98107855839539637898865275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130810474452719517198487033 98107855839539637898865275)
    ·
      refine ⟨147161783759309456848297913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98107855839539637898865275 147161783759309456848297913)
      ·
        refine ⟨110371337819482092636223435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147161783759309456848297913 110371337819482092636223435)
        ·
          refine ⟨165557006729223138954335153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110371337819482092636223435 165557006729223138954335153)
          ·
            refine ⟨124167755046917354215751365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165557006729223138954335153 124167755046917354215751365)
            ·
              refine ⟨23281454071297003915453381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124167755046917354215751365 23281454071297003915453381)
              ·
                refine ⟨4365272638368188234147509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23281454071297003915453381 4365272638368188234147509)
                ·
                  refine ⟨409244309847017646951329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365272638368188234147509 409244309847017646951329)
                  ·
                    rfl

theorem cell23_7173004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_7173004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173004 prefixEnd_7173004 := by exact prefixLift 7173004
  have htrace : WordTrace (prefixWord ++ tailWord_7173004) baseStart_7173004 baseEnd_7173004 := by
    simpa [prefixWord, tailWord_7173004, baseEnd_7173004] using wordTrace_append hprefix tailTrace_7173004
  have hstable : (prefixWord ++ tailWord_7173004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173004).length < 2 ^ (prefixWord ++ tailWord_7173004).sum := by decide
  have hdescent : baseEnd_7173004 < baseStart_7173004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173024 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2]
def baseStart_7173024 : Nat := 118140960795 + 7173024 * 2 ^ 59
def prefixEnd_7173024 : Nat := 4983230072969 + 3 ^ 40 * 7173024 * 2
def baseEnd_7173024 : Nat := 3683209058236248744311869

theorem tailTrace_7173024 : CollatzResearch.WordTrace tailWord_7173024 prefixEnd_7173024 3683209058236248744311869 := by
  unfold tailWord_7173024
  simp only [CollatzResearch.WordTrace]
  refine ⟨130810839182683288906351063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174414452243577718541801417 130810839182683288906351063)
  ·
    refine ⟨196216258774024933359526595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130810839182683288906351063 196216258774024933359526595)
    ·
      refine ⟨294324388161037400039289893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196216258774024933359526595 294324388161037400039289893)
      ·
        refine ⟨55185822780194512507366855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294324388161037400039289893 55185822780194512507366855)
        ·
          refine ⟨82778734170291768761050283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55185822780194512507366855 82778734170291768761050283)
          ·
            refine ⟨124168101255437653141575425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82778734170291768761050283 124168101255437653141575425)
            ·
              refine ⟨93126075941578239856181569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124168101255437653141575425 93126075941578239856181569)
              ·
                refine ⟨69844556956183679892136177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93126075941578239856181569 69844556956183679892136177)
                ·
                  refine ⟨52383417717137759919102133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69844556956183679892136177 52383417717137759919102133)
                  ·
                    refine ⟨4910945410981664992415825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52383417717137759919102133 4910945410981664992415825)
                    ·
                      refine ⟨3683209058236248744311869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4910945410981664992415825 3683209058236248744311869)
                      ·
                        rfl

theorem cell23_7173024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_7173024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173024 prefixEnd_7173024 := by exact prefixLift 7173024
  have htrace : WordTrace (prefixWord ++ tailWord_7173024) baseStart_7173024 baseEnd_7173024 := by
    simpa [prefixWord, tailWord_7173024, baseEnd_7173024] using wordTrace_append hprefix tailTrace_7173024
  have hstable : (prefixWord ++ tailWord_7173024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173024).length < 2 ^ (prefixWord ++ tailWord_7173024).sum := by decide
  have hdescent : baseEnd_7173024 < baseStart_7173024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173091 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7173091 : Nat := 118140960795 + 7173091 * 2 ^ 59
def prefixEnd_7173091 : Nat := 4983230072969 + 3 ^ 40 * 7173091 * 2
def baseEnd_7173091 : Nat := 3683243461440099982174061

theorem tailTrace_7173091 : CollatzResearch.WordTrace tailWord_7173091 prefixEnd_7173091 3683243461440099982174061 := by
  unfold tailWord_7173091
  simp only [CollatzResearch.WordTrace]
  refine ⟨261624122056123848255391127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174416081370749232170260751 261624122056123848255391127)
  ·
    refine ⟨392436183084185772383086691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261624122056123848255391127 392436183084185772383086691)
    ·
      refine ⟨588654274626278658574630037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392436183084185772383086691 588654274626278658574630037)
      ·
        refine ⟨27593169123106812120685783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 588654274626278658574630037 27593169123106812120685783)
        ·
          refine ⟨41389753684660218181028675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27593169123106812120685783 41389753684660218181028675)
          ·
            refine ⟨62084630526990327271543013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41389753684660218181028675 62084630526990327271543013)
            ·
              refine ⟨11640868223810686363414315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62084630526990327271543013 11640868223810686363414315)
              ·
                refine ⟨17461302335716029545121473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640868223810686363414315 17461302335716029545121473)
                ·
                  refine ⟨13095976751787022158841105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17461302335716029545121473 13095976751787022158841105)
                  ·
                    refine ⟨9821982563840266619130829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13095976751787022158841105 9821982563840266619130829)
                    ·
                      refine ⟨3683243461440099982174061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9821982563840266619130829 3683243461440099982174061)
                      ·
                        rfl

theorem cell23_7173091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7173091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173091 prefixEnd_7173091 := by exact prefixLift 7173091
  have htrace : WordTrace (prefixWord ++ tailWord_7173091) baseStart_7173091 baseEnd_7173091 := by
    simpa [prefixWord, tailWord_7173091, baseEnd_7173091] using wordTrace_append hprefix tailTrace_7173091
  have hstable : (prefixWord ++ tailWord_7173091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173091).length < 2 ^ (prefixWord ++ tailWord_7173091).sum := by decide
  have hdescent : baseEnd_7173091 < baseStart_7173091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173148 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7173148 : Nat := 118140960795 + 7173148 * 2 ^ 59
def prefixEnd_7173148 : Nat := 4983230072969 + 3 ^ 40 * 7173148 * 2
def baseEnd_7173148 : Nat := 3683272729837406259161299

theorem tailTrace_7173148 : CollatzResearch.WordTrace tailWord_7173148 prefixEnd_7173148 3683272729837406259161299 := by
  unfold tailWord_7173148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130813100508458673495108049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174417467344611564660144065 130813100508458673495108049)
  ·
    refine ⟨98109825381344005121331037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130813100508458673495108049 98109825381344005121331037)
    ·
      refine ⟨36791184518004001920499139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98109825381344005121331037 36791184518004001920499139)
      ·
        refine ⟨55186776777006002880748709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36791184518004001920499139 55186776777006002880748709)
        ·
          refine ⟨10347520645688625540140383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55186776777006002880748709 10347520645688625540140383)
          ·
            refine ⟨15521280968532938310210575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347520645688625540140383 15521280968532938310210575)
            ·
              refine ⟨23281921452799407465315863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15521280968532938310210575 23281921452799407465315863)
              ·
                refine ⟨34922882179199111197973795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23281921452799407465315863 34922882179199111197973795)
                ·
                  refine ⟨52384323268798666796960693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34922882179199111197973795 52384323268798666796960693)
                  ·
                    refine ⟨4911030306449875012215065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52384323268798666796960693 4911030306449875012215065)
                    ·
                      refine ⟨3683272729837406259161299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911030306449875012215065 3683272729837406259161299)
                      ·
                        rfl

theorem cell23_7173148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7173148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173148 prefixEnd_7173148 := by exact prefixLift 7173148
  have htrace : WordTrace (prefixWord ++ tailWord_7173148) baseStart_7173148 baseEnd_7173148 := by
    simpa [prefixWord, tailWord_7173148, baseEnd_7173148] using wordTrace_append hprefix tailTrace_7173148
  have hstable : (prefixWord ++ tailWord_7173148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173148).length < 2 ^ (prefixWord ++ tailWord_7173148).sum := by decide
  have hdescent : baseEnd_7173148 < baseStart_7173148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173155 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 1, 1, 3]
def baseStart_7173155 : Nat := 118140960795 + 7173155 * 2 ^ 59
def prefixEnd_7173155 : Nat := 4983230072969 + 3 ^ 40 * 7173155 * 2
def baseEnd_7173155 : Nat := 3683276324201987731773767

theorem tailTrace_7173155 : CollatzResearch.WordTrace tailWord_7173155 prefixEnd_7173155 3683276324201987731773767 := by
  unfold tailWord_7173155
  simp only [CollatzResearch.WordTrace]
  refine ⟨261626456327891987185720919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174417637551927991457147279 261626456327891987185720919)
  ·
    refine ⟨392439684491837980778581379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261626456327891987185720919 392439684491837980778581379)
    ·
      refine ⟨588659526737756971167872069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392439684491837980778581379 588659526737756971167872069)
      ·
        refine ⟨110373661263329432093976013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588659526737756971167872069 110373661263329432093976013)
        ·
          refine ⟨41390122973748537035241005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110373661263329432093976013 41390122973748537035241005)
          ·
            refine ⟨15521296115155701388215377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41390122973748537035241005 15521296115155701388215377)
            ·
              refine ⟨11640972086366776041161533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15521296115155701388215377 11640972086366776041161533)
              ·
                refine ⟨4365364532387541015435575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11640972086366776041161533 4365364532387541015435575)
                ·
                  refine ⟨6548046798581311523153363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365364532387541015435575 6548046798581311523153363)
                  ·
                    refine ⟨9822070197871967284730045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548046798581311523153363 9822070197871967284730045)
                    ·
                      refine ⟨3683276324201987731773767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822070197871967284730045 3683276324201987731773767)
                      ·
                        rfl

theorem cell23_7173155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_7173155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173155 prefixEnd_7173155 := by exact prefixLift 7173155
  have htrace : WordTrace (prefixWord ++ tailWord_7173155) baseStart_7173155 baseEnd_7173155 := by
    simpa [prefixWord, tailWord_7173155, baseEnd_7173155] using wordTrace_append hprefix tailTrace_7173155
  have hstable : (prefixWord ++ tailWord_7173155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173155).length < 2 ^ (prefixWord ++ tailWord_7173155).sum := by decide
  have hdescent : baseEnd_7173155 < baseStart_7173155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173164 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_7173164 : Nat := 118140960795 + 7173164 * 2 ^ 59
def prefixEnd_7173164 : Nat := 4983230072969 + 3 ^ 40 * 7173164 * 2
def baseEnd_7173164 : Nat := 3683280945527878196561225

theorem tailTrace_7173164 : CollatzResearch.WordTrace tailWord_7173164 prefixEnd_7173164 3683280945527878196561225 := by
  unfold tailWord_7173164
  simp only [CollatzResearch.WordTrace]
  refine ⟨130813392292429690861399273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174417856389906254481865697 130813392292429690861399273)
  ·
    refine ⟨98110044219322268146049455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130813392292429690861399273 98110044219322268146049455)
    ·
      refine ⟨147165066328983402219074183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98110044219322268146049455 147165066328983402219074183)
      ·
        refine ⟨220747599493475103328611275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147165066328983402219074183 220747599493475103328611275)
        ·
          refine ⟨331121399240212654992916913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220747599493475103328611275 331121399240212654992916913)
          ·
            refine ⟨248341049430159491244687685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331121399240212654992916913 248341049430159491244687685)
            ·
              refine ⟨46563946768154904608378941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248341049430159491244687685 46563946768154904608378941)
              ·
                refine ⟨17461480038058089228142103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46563946768154904608378941 17461480038058089228142103)
                ·
                  refine ⟨26192220057087133842213155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17461480038058089228142103 26192220057087133842213155)
                  ·
                    refine ⟨39288330085630700763319733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26192220057087133842213155 39288330085630700763319733)
                    ·
                      refine ⟨3683280945527878196561225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39288330085630700763319733 3683280945527878196561225)
                      ·
                        rfl

theorem cell23_7173164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_7173164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173164 prefixEnd_7173164 := by exact prefixLift 7173164
  have htrace : WordTrace (prefixWord ++ tailWord_7173164) baseStart_7173164 baseEnd_7173164 := by
    simpa [prefixWord, tailWord_7173164, baseEnd_7173164] using wordTrace_append hprefix tailTrace_7173164
  have hstable : (prefixWord ++ tailWord_7173164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173164).length < 2 ^ (prefixWord ++ tailWord_7173164).sum := by decide
  have hdescent : baseEnd_7173164 < baseStart_7173164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173172 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7173172 : Nat := 118140960795 + 7173172 * 2 ^ 59
def prefixEnd_7173172 : Nat := 4983230072969 + 3 ^ 40 * 7173172 * 2
def baseEnd_7173172 : Nat := 3683285053373114165261189

theorem tailTrace_7173172 : CollatzResearch.WordTrace tailWord_7173172 prefixEnd_7173172 3683285053373114165261189 := by
  unfold tailWord_7173172
  simp only [CollatzResearch.WordTrace]
  refine ⟨130813538184415199544544885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174418050912553599392726513 130813538184415199544544885)
  ·
    refine ⟨12263769204788924957301083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130813538184415199544544885 12263769204788924957301083)
    ·
      refine ⟨18395653807183387435951625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12263769204788924957301083 18395653807183387435951625)
      ·
        refine ⟨13796740355387540576963719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18395653807183387435951625 13796740355387540576963719)
        ·
          refine ⟨20695110533081310865445579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796740355387540576963719 20695110533081310865445579)
          ·
            refine ⟨31042665799621966298168369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20695110533081310865445579 31042665799621966298168369)
            ·
              refine ⟨23281999349716474723626277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31042665799621966298168369 23281999349716474723626277)
              ·
                refine ⟨4365374878071839010679927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23281999349716474723626277 4365374878071839010679927)
                ·
                  refine ⟨6548062317107758516019891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365374878071839010679927 6548062317107758516019891)
                  ·
                    refine ⟨9822093475661637774029837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548062317107758516019891 9822093475661637774029837)
                    ·
                      refine ⟨3683285053373114165261189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822093475661637774029837 3683285053373114165261189)
                      ·
                        rfl

theorem cell23_7173172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7173172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173172 prefixEnd_7173172 := by exact prefixLift 7173172
  have htrace : WordTrace (prefixWord ++ tailWord_7173172) baseStart_7173172 baseEnd_7173172 := by
    simpa [prefixWord, tailWord_7173172, baseEnd_7173172] using wordTrace_append hprefix tailTrace_7173172
  have hstable : (prefixWord ++ tailWord_7173172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173172).length < 2 ^ (prefixWord ++ tailWord_7173172).sum := by decide
  have hdescent : baseEnd_7173172 < baseStart_7173172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173178 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_7173178 : Nat := 118140960795 + 7173178 * 2 ^ 59
def prefixEnd_7173178 : Nat := 4983230072969 + 3 ^ 40 * 7173178 * 2
def baseEnd_7173178 : Nat := 3683288134257041141786161

theorem tailTrace_7173178 : CollatzResearch.WordTrace tailWord_7173178 prefixEnd_7173178 3683288134257041141786161 := by
  unfold tailWord_7173178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65406823801702165528452047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174418196804539108075872125 65406823801702165528452047)
  ·
    refine ⟨98110235702553248292678071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65406823801702165528452047 98110235702553248292678071)
    ·
      refine ⟨147165353553829872439017107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98110235702553248292678071 147165353553829872439017107)
      ·
        refine ⟨220748030330744808658525661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147165353553829872439017107 220748030330744808658525661)
        ·
          refine ⟨82780511374029303246947123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220748030330744808658525661 82780511374029303246947123)
          ·
            refine ⟨124170767061043954870420685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82780511374029303246947123 124170767061043954870420685)
            ·
              refine ⟨46564037647891483076407757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124170767061043954870420685 46564037647891483076407757)
              ·
                refine ⟨17461514117959306153652909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46564037647891483076407757 17461514117959306153652909)
                ·
                  refine ⟨6548067794234739807619841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17461514117959306153652909 6548067794234739807619841)
                  ·
                    refine ⟨4911050845676054855714881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548067794234739807619841 4911050845676054855714881)
                    ·
                      refine ⟨3683288134257041141786161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911050845676054855714881 3683288134257041141786161)
                      ·
                        rfl

theorem cell23_7173178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_7173178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173178 prefixEnd_7173178 := by exact prefixLift 7173178
  have htrace : WordTrace (prefixWord ++ tailWord_7173178) baseStart_7173178 baseEnd_7173178 := by
    simpa [prefixWord, tailWord_7173178, baseEnd_7173178] using wordTrace_append hprefix tailTrace_7173178
  have hstable : (prefixWord ++ tailWord_7173178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173178).length < 2 ^ (prefixWord ++ tailWord_7173178).sum := by decide
  have hdescent : baseEnd_7173178 < baseStart_7173178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173181 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7173181 : Nat := 118140960795 + 7173181 * 2 ^ 59
def prefixEnd_7173181 : Nat := 4983230072969 + 3 ^ 40 * 7173181 * 2
def baseEnd_7173181 : Nat := 3683289674699004630048647

theorem tailTrace_7173181 : CollatzResearch.WordTrace tailWord_7173181 prefixEnd_7173181 3683289674699004630048647 := by
  unfold tailWord_7173181
  simp only [CollatzResearch.WordTrace]
  refine ⟨261627404625797793626167397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174418269750531862417444931 261627404625797793626167397)
  ·
    refine ⟨49055138367337086304906387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261627404625797793626167397 49055138367337086304906387)
    ·
      refine ⟨73582707551005629457359581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49055138367337086304906387 73582707551005629457359581)
      ·
        refine ⟨27593515331627111046509843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73582707551005629457359581 27593515331627111046509843)
        ·
          refine ⟨41390272997440666569764765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27593515331627111046509843 41390272997440666569764765)
          ·
            refine ⟨15521352374040249963661787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41390272997440666569764765 15521352374040249963661787)
            ·
              refine ⟨23282028561060374945492681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15521352374040249963661787 23282028561060374945492681)
              ·
                refine ⟨17461521420795281209119511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23282028561060374945492681 17461521420795281209119511)
                ·
                  refine ⟨26192282131192921813679267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17461521420795281209119511 26192282131192921813679267)
                  ·
                    refine ⟨39288423196789382720518901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26192282131192921813679267 39288423196789382720518901)
                    ·
                      refine ⟨3683289674699004630048647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39288423196789382720518901 3683289674699004630048647)
                      ·
                        rfl

theorem cell23_7173181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7173181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173181 prefixEnd_7173181 := by exact prefixLift 7173181
  have htrace : WordTrace (prefixWord ++ tailWord_7173181) baseStart_7173181 baseEnd_7173181 := by
    simpa [prefixWord, tailWord_7173181, baseEnd_7173181] using wordTrace_append hprefix tailTrace_7173181
  have hstable : (prefixWord ++ tailWord_7173181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173181).length < 2 ^ (prefixWord ++ tailWord_7173181).sum := by decide
  have hdescent : baseEnd_7173181 < baseStart_7173181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173191 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_7173191 : Nat := 118140960795 + 7173191 * 2 ^ 59
def prefixEnd_7173191 : Nat := 4983230072969 + 3 ^ 40 * 7173191 * 2
def baseEnd_7173191 : Nat := 3683294809505549590923601

theorem tailTrace_7173191 : CollatzResearch.WordTrace tailWord_7173191 prefixEnd_7173191 3683294809505549590923601 := by
  unfold tailWord_7173191
  simp only [CollatzResearch.WordTrace]
  refine ⟨261627769355761565334031427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174418512903841043556020951 261627769355761565334031427)
  ·
    refine ⟨392441654033642348001047141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261627769355761565334031427 392441654033642348001047141)
    ·
      refine ⟨73582810131307940250196339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392441654033642348001047141 73582810131307940250196339)
      ·
        refine ⟨110374215196961910375294509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73582810131307940250196339 110374215196961910375294509)
        ·
          refine ⟨41390330698860716390735441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110374215196961910375294509 41390330698860716390735441)
          ·
            refine ⟨31042748024145537293051581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41390330698860716390735441 31042748024145537293051581)
            ·
              refine ⟨11641030509054576484894343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31042748024145537293051581 11641030509054576484894343)
              ·
                refine ⟨17461545763581864727341515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11641030509054576484894343 17461545763581864727341515)
                ·
                  refine ⟨26192318645372797091012273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17461545763581864727341515 26192318645372797091012273)
                  ·
                    refine ⟨19644238984029597818259205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26192318645372797091012273 19644238984029597818259205)
                    ·
                      refine ⟨3683294809505549590923601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19644238984029597818259205 3683294809505549590923601)
                      ·
                        rfl

theorem cell23_7173191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_7173191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173191 prefixEnd_7173191 := by exact prefixLift 7173191
  have htrace : WordTrace (prefixWord ++ tailWord_7173191) baseStart_7173191 baseEnd_7173191 := by
    simpa [prefixWord, tailWord_7173191, baseEnd_7173191] using wordTrace_append hprefix tailTrace_7173191
  have hstable : (prefixWord ++ tailWord_7173191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173191).length < 2 ^ (prefixWord ++ tailWord_7173191).sum := by decide
  have hdescent : baseEnd_7173191 < baseStart_7173191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173198 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_7173198 : Nat := 118140960795 + 7173198 * 2 ^ 59
def prefixEnd_7173198 : Nat := 4983230072969 + 3 ^ 40 * 7173198 * 2
def baseEnd_7173198 : Nat := 3683298403870131063536069

theorem tailTrace_7173198 : CollatzResearch.WordTrace tailWord_7173198 prefixEnd_7173198 3683298403870131063536069 := by
  unfold tailWord_7173198
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703503083342025691192031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174418683111157470353024165 32703503083342025691192031)
  ·
    refine ⟨49055254625013038536788047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32703503083342025691192031 49055254625013038536788047)
    ·
      refine ⟨73582881937519557805182071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49055254625013038536788047 73582881937519557805182071)
      ·
        refine ⟨110374322906279336707773107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73582881937519557805182071 110374322906279336707773107)
        ·
          refine ⟨165561484359419005061659661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110374322906279336707773107 165561484359419005061659661)
          ·
            refine ⟨62085556634782126898122373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165561484359419005061659661 62085556634782126898122373)
            ·
              refine ⟨11641041869021648793397945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62085556634782126898122373 11641041869021648793397945)
              ·
                refine ⟨8730781401766236595048459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641041869021648793397945 8730781401766236595048459)
                ·
                  refine ⟨13096172102649354892572689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730781401766236595048459 13096172102649354892572689)
                  ·
                    refine ⟨9822129076987016169429517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13096172102649354892572689 9822129076987016169429517)
                    ·
                      refine ⟨3683298403870131063536069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822129076987016169429517 3683298403870131063536069)
                      ·
                        rfl

theorem cell23_7173198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_7173198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173198 prefixEnd_7173198 := by exact prefixLift 7173198
  have htrace : WordTrace (prefixWord ++ tailWord_7173198) baseStart_7173198 baseEnd_7173198 := by
    simpa [prefixWord, tailWord_7173198, baseEnd_7173198] using wordTrace_append hprefix tailTrace_7173198
  have hstable : (prefixWord ++ tailWord_7173198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173198).length < 2 ^ (prefixWord ++ tailWord_7173198).sum := by decide
  have hdescent : baseEnd_7173198 < baseStart_7173198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173206 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7173206 : Nat := 118140960795 + 7173206 * 2 ^ 59
def prefixEnd_7173206 : Nat := 4983230072969 + 3 ^ 40 * 7173206 * 2
def baseEnd_7173206 : Nat := 3683302511715367032236033

theorem tailTrace_7173206 : CollatzResearch.WordTrace tailWord_7173206 prefixEnd_7173206 3683302511715367032236033 := by
  unfold tailWord_7173206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351769778169201430989217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174418877633804815263884981 16351769778169201430989217)
  ·
    refine ⟨12263827333626901073241913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16351769778169201430989217 12263827333626901073241913)
    ·
      refine ⟨9197870500220175804931435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12263827333626901073241913 9197870500220175804931435)
      ·
        refine ⟨13796805750330263707397153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197870500220175804931435 13796805750330263707397153)
        ·
          refine ⟨10347604312747697780547865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13796805750330263707397153 10347604312747697780547865)
          ·
            refine ⟨7760703234560773335410899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10347604312747697780547865 7760703234560773335410899)
            ·
              refine ⟨11641054851841160003116349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760703234560773335410899 11641054851841160003116349)
              ·
                refine ⟨4365395569440435001168631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11641054851841160003116349 4365395569440435001168631)
                ·
                  refine ⟨6548093354160652501752947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365395569440435001168631 6548093354160652501752947)
                  ·
                    refine ⟨9822140031240978752629421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548093354160652501752947 9822140031240978752629421)
                    ·
                      refine ⟨3683302511715367032236033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822140031240978752629421 3683302511715367032236033)
                      ·
                        rfl

theorem cell23_7173206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7173206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173206 prefixEnd_7173206 := by exact prefixLift 7173206
  have htrace : WordTrace (prefixWord ++ tailWord_7173206) baseStart_7173206 baseEnd_7173206 := by
    simpa [prefixWord, tailWord_7173206, baseEnd_7173206] using wordTrace_append hprefix tailTrace_7173206
  have hstable : (prefixWord ++ tailWord_7173206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173206).length < 2 ^ (prefixWord ++ tailWord_7173206).sum := by decide
  have hdescent : baseEnd_7173206 < baseStart_7173206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173228 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_7173228 : Nat := 118140960795 + 7173228 * 2 ^ 59
def prefixEnd_7173228 : Nat := 4983230072969 + 3 ^ 40 * 7173228 * 2
def baseEnd_7173228 : Nat := 3683313808289765946160931

theorem tailTrace_7173228 : CollatzResearch.WordTrace tailWord_7173228 prefixEnd_7173228 3683313808289765946160931 := by
  unfold tailWord_7173228
  simp only [CollatzResearch.WordTrace]
  refine ⟨130814559428313760326564169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174419412571085013768752225 130814559428313760326564169)
  ·
    refine ⟨98110919571235320244923127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130814559428313760326564169 98110919571235320244923127)
    ·
      refine ⟨147166379356852980367384691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98110919571235320244923127 147166379356852980367384691)
      ·
        refine ⟨220749569035279470551077037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147166379356852980367384691 220749569035279470551077037)
        ·
          refine ⟨82781088388229801456653889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220749569035279470551077037 82781088388229801456653889)
          ·
            refine ⟨62085816291172351092490417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82781088388229801456653889 62085816291172351092490417)
            ·
              refine ⟨46564362218379263319367813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62085816291172351092490417 46564362218379263319367813)
              ·
                refine ⟨8730817915946111872381465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46564362218379263319367813 8730817915946111872381465)
                ·
                  refine ⟨6548113436959583904286099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8730817915946111872381465 6548113436959583904286099)
                  ·
                    refine ⟨9822170155439375856429149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548113436959583904286099 9822170155439375856429149)
                    ·
                      refine ⟨3683313808289765946160931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822170155439375856429149 3683313808289765946160931)
                      ·
                        rfl

theorem cell23_7173228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_7173228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173228 prefixEnd_7173228 := by exact prefixLift 7173228
  have htrace : WordTrace (prefixWord ++ tailWord_7173228) baseStart_7173228 baseEnd_7173228 := by
    simpa [prefixWord, tailWord_7173228, baseEnd_7173228] using wordTrace_append hprefix tailTrace_7173228
  have hstable : (prefixWord ++ tailWord_7173228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173228).length < 2 ^ (prefixWord ++ tailWord_7173228).sum := by decide
  have hdescent : baseEnd_7173228 < baseStart_7173228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173229 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7173229 : Nat := 118140960795 + 7173229 * 2 ^ 59
def prefixEnd_7173229 : Nat := 4983230072969 + 3 ^ 40 * 7173229 * 2
def baseEnd_7173229 : Nat := 3683314321770420442248427

theorem tailTrace_7173229 : CollatzResearch.WordTrace tailWord_7173229 prefixEnd_7173229 3683314321770420442248427 := by
  unfold tailWord_7173229
  simp only [CollatzResearch.WordTrace]
  refine ⟨261629155329623897823914741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174419436886415931882609827 261629155329623897823914741)
  ·
    refine ⟨24527733312152240420992007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261629155329623897823914741 24527733312152240420992007)
    ·
      refine ⟨36791599968228360631488011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24527733312152240420992007 36791599968228360631488011)
      ·
        refine ⟨55187399952342540947232017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36791599968228360631488011 55187399952342540947232017)
        ·
          refine ⟨41390549964256905710424013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55187399952342540947232017 41390549964256905710424013)
          ·
            refine ⟨15521456236596339641409005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41390549964256905710424013 15521456236596339641409005)
            ·
              refine ⟨5820546088723627365528377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15521456236596339641409005 5820546088723627365528377)
              ·
                refine ⟨4365409566542720524146283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5820546088723627365528377 4365409566542720524146283)
                ·
                  refine ⟨6548114349814080786219425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365409566542720524146283 6548114349814080786219425)
                  ·
                    refine ⟨4911085762360560589664569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548114349814080786219425 4911085762360560589664569)
                    ·
                      refine ⟨3683314321770420442248427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911085762360560589664569 3683314321770420442248427)
                      ·
                        rfl

theorem cell23_7173229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7173229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173229 prefixEnd_7173229 := by exact prefixLift 7173229
  have htrace : WordTrace (prefixWord ++ tailWord_7173229) baseStart_7173229 baseEnd_7173229 := by
    simpa [prefixWord, tailWord_7173229, baseEnd_7173229] using wordTrace_append hprefix tailTrace_7173229
  have hstable : (prefixWord ++ tailWord_7173229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173229).length < 2 ^ (prefixWord ++ tailWord_7173229).sum := by decide
  have hdescent : baseEnd_7173229 < baseStart_7173229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173244 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_7173244 : Nat := 118140960795 + 7173244 * 2 ^ 59
def prefixEnd_7173244 : Nat := 4983230072969 + 3 ^ 40 * 7173244 * 2
def baseEnd_7173244 : Nat := 1227774007993412627853619

theorem tailTrace_7173244 : CollatzResearch.WordTrace tailWord_7173244 prefixEnd_7173244 1227774007993412627853619 := by
  unfold tailWord_7173244
  simp only [CollatzResearch.WordTrace]
  refine ⟨130814851212284777692855393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174419801616379703590473857 130814851212284777692855393)
  ·
    refine ⟨98111138409213583269641545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130814851212284777692855393 98111138409213583269641545)
    ·
      refine ⟨73583353806910187452231159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98111138409213583269641545 73583353806910187452231159)
      ·
        refine ⟨110375030710365281178346739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73583353806910187452231159 110375030710365281178346739)
        ·
          refine ⟨165562546065547921767520109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110375030710365281178346739 165562546065547921767520109)
          ·
            refine ⟨62085954774580470662820041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165562546065547921767520109 62085954774580470662820041)
            ·
              refine ⟨46564466080935352997115031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62085954774580470662820041 46564466080935352997115031)
              ·
                refine ⟨69846699121403029495672547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46564466080935352997115031 69846699121403029495672547)
                ·
                  refine ⟨104770048682104544243508821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69846699121403029495672547 104770048682104544243508821)
                  ·
                    refine ⟨1227774007993412627853619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104770048682104544243508821 1227774007993412627853619)
                    ·
                      rfl

theorem cell23_7173244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_7173244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173244 prefixEnd_7173244 := by exact prefixLift 7173244
  have htrace : WordTrace (prefixWord ++ tailWord_7173244) baseStart_7173244 baseEnd_7173244 := by
    simpa [prefixWord, tailWord_7173244, baseEnd_7173244] using wordTrace_append hprefix tailTrace_7173244
  have hstable : (prefixWord ++ tailWord_7173244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173244).length < 2 ^ (prefixWord ++ tailWord_7173244).sum := by decide
  have hdescent : baseEnd_7173244 < baseStart_7173244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173246 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7173246 : Nat := 118140960795 + 7173246 * 2 ^ 59
def prefixEnd_7173246 : Nat := 4983230072969 + 3 ^ 40 * 7173246 * 2
def baseEnd_7173246 : Nat := 3683323050941546875735849

theorem tailTrace_7173246 : CollatzResearch.WordTrace tailWord_7173246 prefixEnd_7173246 3683323050941546875735849 := by
  unfold tailWord_7173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703721921320288715910449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174419850247041539818189061 32703721921320288715910449)
  ·
    refine ⟨24527791440990216536932837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32703721921320288715910449 24527791440990216536932837)
    ·
      refine ⟨4598960895185665600674907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24527791440990216536932837 4598960895185665600674907)
      ·
        refine ⟨6898441342778498401012361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4598960895185665600674907 6898441342778498401012361)
        ·
          refine ⟨5173831007083873800759271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6898441342778498401012361 5173831007083873800759271)
          ·
            refine ⟨7760746510625810701138907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173831007083873800759271 7760746510625810701138907)
            ·
              refine ⟨11641119765938716051708361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760746510625810701138907 11641119765938716051708361)
              ·
                refine ⟨8730839824454037038781271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641119765938716051708361 8730839824454037038781271)
                ·
                  refine ⟨13096259736681055558171907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730839824454037038781271 13096259736681055558171907)
                  ·
                    refine ⟨19644389605021583337257861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13096259736681055558171907 19644389605021583337257861)
                    ·
                      refine ⟨3683323050941546875735849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19644389605021583337257861 3683323050941546875735849)
                      ·
                        rfl

theorem cell23_7173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7173246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173246 prefixEnd_7173246 := by exact prefixLift 7173246
  have htrace : WordTrace (prefixWord ++ tailWord_7173246) baseStart_7173246 baseEnd_7173246 := by
    simpa [prefixWord, tailWord_7173246, baseEnd_7173246] using wordTrace_append hprefix tailTrace_7173246
  have hstable : (prefixWord ++ tailWord_7173246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173246).length < 2 ^ (prefixWord ++ tailWord_7173246).sum := by decide
  have hdescent : baseEnd_7173246 < baseStart_7173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173264 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_7173264 : Nat := 118140960795 + 7173264 * 2 ^ 59
def prefixEnd_7173264 : Nat := 4983230072969 + 3 ^ 40 * 7173264 * 2
def baseEnd_7173264 : Nat := 3683332293593327805310765

theorem tailTrace_7173264 : CollatzResearch.WordTrace tailWord_7173264 prefixEnd_7173264 3683332293593327805310765 := by
  unfold tailWord_7173264
  simp only [CollatzResearch.WordTrace]
  refine ⟨130815215942248549400719423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174420287922998065867625897 130815215942248549400719423)
  ·
    refine ⟨196222823913372824101079135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130815215942248549400719423 196222823913372824101079135)
    ·
      refine ⟨294334235870059236151618703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196222823913372824101079135 294334235870059236151618703)
      ·
        refine ⟨441501353805088854227428055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294334235870059236151618703 441501353805088854227428055)
        ·
          refine ⟨662252030707633281341142083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441501353805088854227428055 662252030707633281341142083)
          ·
            refine ⟨993378046061449922011713125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662252030707633281341142083 993378046061449922011713125)
            ·
              refine ⟨186258383636521860377196211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 993378046061449922011713125 186258383636521860377196211)
              ·
                refine ⟨279387575454782790565794317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186258383636521860377196211 279387575454782790565794317)
                ·
                  refine ⟨104770340795543546462172869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279387575454782790565794317 104770340795543546462172869)
                  ·
                    refine ⟨19644438899164414961657413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104770340795543546462172869 19644438899164414961657413)
                    ·
                      refine ⟨3683332293593327805310765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19644438899164414961657413 3683332293593327805310765)
                      ·
                        rfl

theorem cell23_7173264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_7173264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173264 prefixEnd_7173264 := by exact prefixLift 7173264
  have htrace : WordTrace (prefixWord ++ tailWord_7173264) baseStart_7173264 baseEnd_7173264 := by
    simpa [prefixWord, tailWord_7173264, baseEnd_7173264] using wordTrace_append hprefix tailTrace_7173264
  have hstable : (prefixWord ++ tailWord_7173264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173264).length < 2 ^ (prefixWord ++ tailWord_7173264).sum := by decide
  have hdescent : baseEnd_7173264 < baseStart_7173264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173271 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_7173271 : Nat := 118140960795 + 7173271 * 2 ^ 59
def prefixEnd_7173271 : Nat := 4983230072969 + 3 ^ 40 * 7173271 * 2
def baseEnd_7173271 : Nat := 3683335887957909277923233

theorem tailTrace_7173271 : CollatzResearch.WordTrace tailWord_7173271 prefixEnd_7173271 3683335887957909277923233 := by
  unfold tailWord_7173271
  simp only [CollatzResearch.WordTrace]
  refine ⟨261630687195471738996943667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174420458130314492664629111 261630687195471738996943667)
  ·
    refine ⟨392446030793207608495415501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261630687195471738996943667 392446030793207608495415501)
    ·
      refine ⟨147167261547452853185780813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392446030793207608495415501 147167261547452853185780813)
      ·
        refine ⟨55187723080294819944667805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147167261547452853185780813 55187723080294819944667805)
        ·
          refine ⟨20695396155110557479250427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55187723080294819944667805 20695396155110557479250427)
          ·
            refine ⟨31043094232665836218875641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20695396155110557479250427 31043094232665836218875641)
            ·
              refine ⟨23282320674499377164156731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31043094232665836218875641 23282320674499377164156731)
              ·
                refine ⟨34923481011749065746235097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23282320674499377164156731 34923481011749065746235097)
                ·
                  refine ⟨26192610758811799309676323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34923481011749065746235097 26192610758811799309676323)
                  ·
                    refine ⟨39288916138217698964514485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26192610758811799309676323 39288916138217698964514485)
                    ·
                      refine ⟨3683335887957909277923233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39288916138217698964514485 3683335887957909277923233)
                      ·
                        rfl

theorem cell23_7173271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_7173271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173271 prefixEnd_7173271 := by exact prefixLift 7173271
  have htrace : WordTrace (prefixWord ++ tailWord_7173271) baseStart_7173271 baseEnd_7173271 := by
    simpa [prefixWord, tailWord_7173271, baseEnd_7173271] using wordTrace_append hprefix tailTrace_7173271
  have hstable : (prefixWord ++ tailWord_7173271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173271).length < 2 ^ (prefixWord ++ tailWord_7173271).sum := by decide
  have hdescent : baseEnd_7173271 < baseStart_7173271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173272 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7173272 : Nat := 118140960795 + 7173272 * 2 ^ 59
def prefixEnd_7173272 : Nat := 4983230072969 + 3 ^ 40 * 7173272 * 2
def baseEnd_7173272 : Nat := 3683336401438563774010729

theorem tailTrace_7173272 : CollatzResearch.WordTrace tailWord_7173272 prefixEnd_7173272 3683336401438563774010729 := by
  unfold tailWord_7173272
  simp only [CollatzResearch.WordTrace]
  refine ⟨130815361834234058083865035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174420482445645410778486713 130815361834234058083865035)
  ·
    refine ⟨196223042751351087125797553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130815361834234058083865035 196223042751351087125797553)
    ·
      refine ⟨147167282063513315344348165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196223042751351087125797553 147167282063513315344348165)
      ·
        refine ⟨27593865386908746627065281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147167282063513315344348165 27593865386908746627065281)
        ·
          refine ⟨20695399040181559970298961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27593865386908746627065281 20695399040181559970298961)
          ·
            refine ⟨15521549280136169977724221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20695399040181559970298961 15521549280136169977724221)
            ·
              refine ⟨5820580980051063741646583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15521549280136169977724221 5820580980051063741646583)
              ·
                refine ⟨8730871470076595612469875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820580980051063741646583 8730871470076595612469875)
                ·
                  refine ⟨13096307205114893418704813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730871470076595612469875 13096307205114893418704813)
                  ·
                    refine ⟨4911115201918085032014305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13096307205114893418704813 4911115201918085032014305)
                    ·
                      refine ⟨3683336401438563774010729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911115201918085032014305 3683336401438563774010729)
                      ·
                        rfl

theorem cell23_7173272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7173272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173272 prefixEnd_7173272 := by exact prefixLift 7173272
  have htrace : WordTrace (prefixWord ++ tailWord_7173272) baseStart_7173272 baseEnd_7173272 := by
    simpa [prefixWord, tailWord_7173272, baseEnd_7173272] using wordTrace_append hprefix tailTrace_7173272
  have hstable : (prefixWord ++ tailWord_7173272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173272).length < 2 ^ (prefixWord ++ tailWord_7173272).sum := by decide
  have hdescent : baseEnd_7173272 < baseStart_7173272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173281 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7173281 : Nat := 118140960795 + 7173281 * 2 ^ 59
def prefixEnd_7173281 : Nat := 4983230072969 + 3 ^ 40 * 7173281 * 2
def baseEnd_7173281 : Nat := 3683341022764454238798187

theorem tailTrace_7173281 : CollatzResearch.WordTrace tailWord_7173281 prefixEnd_7173281 3683341022764454238798187 := by
  unfold tailWord_7173281
  simp only [CollatzResearch.WordTrace]
  refine ⟨261631051925435510704807697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174420701283623673803205131 261631051925435510704807697)
  ·
    refine ⟨196223288944076633028605773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261631051925435510704807697 196223288944076633028605773)
    ·
      refine ⟨73583733354028737385727165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196223288944076633028605773 73583733354028737385727165)
      ·
        refine ⟨27593900007760776519647687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73583733354028737385727165 27593900007760776519647687)
        ·
          refine ⟨41390850011641164779471531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27593900007760776519647687 41390850011641164779471531)
          ·
            refine ⟨62086275017461747169207297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41390850011641164779471531 62086275017461747169207297)
            ·
              refine ⟨46564706263096310376905473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62086275017461747169207297 46564706263096310376905473)
              ·
                refine ⟨34923529697322232782679105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46564706263096310376905473 34923529697322232782679105)
                ·
                  refine ⟨26192647272991674587009329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34923529697322232782679105 26192647272991674587009329)
                  ·
                    refine ⟨19644485454743755940256997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26192647272991674587009329 19644485454743755940256997)
                    ·
                      refine ⟨3683341022764454238798187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19644485454743755940256997 3683341022764454238798187)
                      ·
                        rfl

theorem cell23_7173281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7173281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173281 prefixEnd_7173281 := by exact prefixLift 7173281
  have htrace : WordTrace (prefixWord ++ tailWord_7173281) baseStart_7173281 baseEnd_7173281 := by
    simpa [prefixWord, tailWord_7173281, baseEnd_7173281] using wordTrace_append hprefix tailTrace_7173281
  have hstable : (prefixWord ++ tailWord_7173281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173281).length < 2 ^ (prefixWord ++ tailWord_7173281).sum := by decide
  have hdescent : baseEnd_7173281 < baseStart_7173281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173285 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_7173285 : Nat := 118140960795 + 7173285 * 2 ^ 59
def prefixEnd_7173285 : Nat := 4983230072969 + 3 ^ 40 * 7173285 * 2
def baseEnd_7173285 : Nat := 3683343076687072223148169

theorem tailTrace_7173285 : CollatzResearch.WordTrace tailWord_7173285 prefixEnd_7173285 3683343076687072223148169 := by
  unfold tailWord_7173285
  simp only [CollatzResearch.WordTrace]
  refine ⟨261631197817421019387953309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174420798544947346258635539 261631197817421019387953309)
  ·
    refine ⟨98111699181532882270482491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261631197817421019387953309 98111699181532882270482491)
    ·
      refine ⟨147167548772299323405723737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98111699181532882270482491 147167548772299323405723737)
      ·
        refine ⟨110375661579224492554292803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147167548772299323405723737 110375661579224492554292803)
        ·
          refine ⟨165563492368836738831439205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110375661579224492554292803 165563492368836738831439205)
          ·
            refine ⟨31043154819156888530894851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165563492368836738831439205 31043154819156888530894851)
            ·
              refine ⟨46564732228735332796342277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31043154819156888530894851 46564732228735332796342277)
              ·
                refine ⟨8730887292887874899314177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46564732228735332796342277 8730887292887874899314177)
                ·
                  refine ⟨6548165469665906174485633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8730887292887874899314177 6548165469665906174485633)
                  ·
                    refine ⟨4911124102249429630864225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548165469665906174485633 4911124102249429630864225)
                    ·
                      refine ⟨3683343076687072223148169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911124102249429630864225 3683343076687072223148169)
                      ·
                        rfl

theorem cell23_7173285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_7173285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173285 prefixEnd_7173285 := by exact prefixLift 7173285
  have htrace : WordTrace (prefixWord ++ tailWord_7173285) baseStart_7173285 baseEnd_7173285 := by
    simpa [prefixWord, tailWord_7173285, baseEnd_7173285] using wordTrace_append hprefix tailTrace_7173285
  have hstable : (prefixWord ++ tailWord_7173285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173285).length < 2 ^ (prefixWord ++ tailWord_7173285).sum := by decide
  have hdescent : baseEnd_7173285 < baseStart_7173285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173453 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7173453 : Nat := 118140960795 + 7173453 * 2 ^ 59
def prefixEnd_7173453 : Nat := 4983230072969 + 3 ^ 40 * 7173453 * 2
def baseEnd_7173453 : Nat := 1227809780479009188615799

theorem tailTrace_7173453 : CollatzResearch.WordTrace tailWord_7173453 prefixEnd_7173453 1227809780479009188615799 := by
  unfold tailWord_7173453
  simp only [CollatzResearch.WordTrace]
  refine ⟨261637325280812384080069013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174424883520541589386712675 261637325280812384080069013)
  ·
    refine ⟨12264249622538080503753235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261637325280812384080069013 12264249622538080503753235)
    ·
      refine ⟨18396374433807120755629853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12264249622538080503753235 18396374433807120755629853)
      ·
        refine ⟨6898640412677670283361195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18396374433807120755629853 6898640412677670283361195)
        ·
          refine ⟨10347960619016505425041793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898640412677670283361195 10347960619016505425041793)
          ·
            refine ⟨7760970464262379068781345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10347960619016505425041793 7760970464262379068781345)
            ·
              refine ⟨5820727848196784301586009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760970464262379068781345 5820727848196784301586009)
              ·
                refine ⟨4365545886147588226189507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5820727848196784301586009 4365545886147588226189507)
                ·
                  refine ⟨6548318829221382339284261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365545886147588226189507 6548318829221382339284261)
                  ·
                    refine ⟨1227809780479009188615799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6548318829221382339284261 1227809780479009188615799)
                    ·
                      rfl

theorem cell23_7173453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7173453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173453 prefixEnd_7173453 := by exact prefixLift 7173453
  have htrace : WordTrace (prefixWord ++ tailWord_7173453) baseStart_7173453 baseEnd_7173453 := by
    simpa [prefixWord, tailWord_7173453, baseEnd_7173453] using wordTrace_append hprefix tailTrace_7173453
  have hstable : (prefixWord ++ tailWord_7173453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173453).length < 2 ^ (prefixWord ++ tailWord_7173453).sum := by decide
  have hdescent : baseEnd_7173453 < baseStart_7173453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173475 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 2, 4]
def baseStart_7173475 : Nat := 118140960795 + 7173475 * 2 ^ 59
def prefixEnd_7173475 : Nat := 4983230072969 + 3 ^ 40 * 7173475 * 2
def baseEnd_7173475 : Nat := 1227813546003808826590765

theorem tailTrace_7173475 : CollatzResearch.WordTrace tailWord_7173475 prefixEnd_7173475 1227813546003808826590765 := by
  unfold tailWord_7173475
  simp only [CollatzResearch.WordTrace]
  refine ⟨261638127686732681837369879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174425418457821787891579919 261638127686732681837369879)
  ·
    refine ⟨392457191530099022756054819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261638127686732681837369879 392457191530099022756054819)
    ·
      refine ⟨588685787295148534134082229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392457191530099022756054819 588685787295148534134082229)
      ·
        refine ⟨55189292558920175075070209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 588685787295148534134082229 55189292558920175075070209)
        ·
          refine ⟨41391969419190131306302657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55189292558920175075070209 41391969419190131306302657)
          ·
            refine ⟨31043977064392598479726993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41391969419190131306302657 31043977064392598479726993)
            ·
              refine ⟨23282982798294448859795245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31043977064392598479726993 23282982798294448859795245)
              ·
                refine ⟨8731118549360418322423217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23282982798294448859795245 8731118549360418322423217)
                ·
                  refine ⟨6548338912020313741817413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8731118549360418322423217 6548338912020313741817413)
                  ·
                    refine ⟨1227813546003808826590765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6548338912020313741817413 1227813546003808826590765)
                    ·
                      rfl

theorem cell23_7173475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 4].length) (baseStart_7173475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173475 prefixEnd_7173475 := by exact prefixLift 7173475
  have htrace : WordTrace (prefixWord ++ tailWord_7173475) baseStart_7173475 baseEnd_7173475 := by
    simpa [prefixWord, tailWord_7173475, baseEnd_7173475] using wordTrace_append hprefix tailTrace_7173475
  have hstable : (prefixWord ++ tailWord_7173475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173475).length < 2 ^ (prefixWord ++ tailWord_7173475).sum := by decide
  have hdescent : baseEnd_7173475 < baseStart_7173475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173485 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7173485 : Nat := 118140960795 + 7173485 * 2 ^ 59
def prefixEnd_7173485 : Nat := 4983230072969 + 3 ^ 40 * 7173485 * 2
def baseEnd_7173485 : Nat := 3683445772817971440647249

theorem tailTrace_7173485 : CollatzResearch.WordTrace tailWord_7173485 prefixEnd_7173485 3683445772817971440647249 := by
  unfold tailWord_7173485
  simp only [CollatzResearch.WordTrace]
  refine ⟨261638492416696453545233909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174425661611130969030155939 261638492416696453545233909)
  ·
    refine ⟨24528608664065292519865679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261638492416696453545233909 24528608664065292519865679)
    ·
      refine ⟨36792912996097938779798519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24528608664065292519865679 36792912996097938779798519)
      ·
        refine ⟨55189369494146908169697779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36792912996097938779798519 55189369494146908169697779)
        ·
          refine ⟨82784054241220362254546669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55189369494146908169697779 82784054241220362254546669)
          ·
            refine ⟨31044020340457635845455001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82784054241220362254546669 31044020340457635845455001)
            ·
              refine ⟨23283015255343226884091251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31044020340457635845455001 23283015255343226884091251)
              ·
                refine ⟨34924522883014840326136877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23283015255343226884091251 34924522883014840326136877)
                ·
                  refine ⟨13096696081130565122301329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34924522883014840326136877 13096696081130565122301329)
                  ·
                    refine ⟨9822522060847923841725997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13096696081130565122301329 9822522060847923841725997)
                    ·
                      refine ⟨3683445772817971440647249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822522060847923841725997 3683445772817971440647249)
                      ·
                        rfl

theorem cell23_7173485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7173485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173485 prefixEnd_7173485 := by exact prefixLift 7173485
  have htrace : WordTrace (prefixWord ++ tailWord_7173485) baseStart_7173485 baseEnd_7173485 := by
    simpa [prefixWord, tailWord_7173485, baseEnd_7173485] using wordTrace_append hprefix tailTrace_7173485
  have hstable : (prefixWord ++ tailWord_7173485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173485).length < 2 ^ (prefixWord ++ tailWord_7173485).sum := by decide
  have hdescent : baseEnd_7173485 < baseStart_7173485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173486 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7173486 : Nat := 118140960795 + 7173486 * 2 ^ 59
def prefixEnd_7173486 : Nat := 4983230072969 + 3 ^ 40 * 7173486 * 2
def baseEnd_7173486 : Nat := 3683446286298625936734745

theorem tailTrace_7173486 : CollatzResearch.WordTrace tailWord_7173486 prefixEnd_7173486 3683446286298625936734745 := by
  unfold tailWord_7173486
  simp only [CollatzResearch.WordTrace]
  refine ⟨32704816111211603839502539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174425685926461887144013541 32704816111211603839502539)
  ·
    refine ⟨49057224166817405759253809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32704816111211603839502539 49057224166817405759253809)
    ·
      refine ⟨36792918125113054319440357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49057224166817405759253809 36792918125113054319440357)
      ·
        refine ⟨6898672148458697684895067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36792918125113054319440357 6898672148458697684895067)
        ·
          refine ⟨10348008222688046527342601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898672148458697684895067 10348008222688046527342601)
          ·
            refine ⟨7761006167016034895506951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10348008222688046527342601 7761006167016034895506951)
            ·
              refine ⟨11641509250524052343260427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761006167016034895506951 11641509250524052343260427)
              ·
                refine ⟨17462263875786078514890641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11641509250524052343260427 17462263875786078514890641)
                ·
                  refine ⟨13096697906839558886167981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17462263875786078514890641 13096697906839558886167981)
                  ·
                    refine ⟨4911261715064834582312993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13096697906839558886167981 4911261715064834582312993)
                    ·
                      refine ⟨3683446286298625936734745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911261715064834582312993 3683446286298625936734745)
                      ·
                        rfl

theorem cell23_7173486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7173486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173486 prefixEnd_7173486 := by exact prefixLift 7173486
  have htrace : WordTrace (prefixWord ++ tailWord_7173486) baseStart_7173486 baseEnd_7173486 := by
    simpa [prefixWord, tailWord_7173486, baseEnd_7173486] using wordTrace_append hprefix tailTrace_7173486
  have hstable : (prefixWord ++ tailWord_7173486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173486).length < 2 ^ (prefixWord ++ tailWord_7173486).sum := by decide
  have hdescent : baseEnd_7173486 < baseStart_7173486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173488 : List Nat := [2, 1, 1, 1, 4, 2, 5, 7]
def baseStart_7173488 : Nat := 118140960795 + 7173488 * 2 ^ 59
def prefixEnd_7173488 : Nat := 4983230072969 + 3 ^ 40 * 7173488 * 2
def baseEnd_7173488 : Nat := 136423974565182775144805

theorem tailTrace_7173488 : CollatzResearch.WordTrace tailWord_7173488 prefixEnd_7173488 136423974565182775144805 := by
  unfold tailWord_7173488
  simp only [CollatzResearch.WordTrace]
  refine ⟨130819300917842792528796559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174425734557123723371728745 130819300917842792528796559)
  ·
    refine ⟨196228951376764188793194839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130819300917842792528796559 196228951376764188793194839)
    ·
      refine ⟨294343427065146283189792259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196228951376764188793194839 294343427065146283189792259)
      ·
        refine ⟨441515140597719424784688389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294343427065146283189792259 441515140597719424784688389)
        ·
          refine ⟨82784088862072392147129073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441515140597719424784688389 82784088862072392147129073)
          ·
            refine ⟨62088066646554294110346805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82784088862072392147129073 62088066646554294110346805)
            ·
              refine ⟨5820756248114465072845013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62088066646554294110346805 5820756248114465072845013)
              ·
                refine ⟨136423974565182775144805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5820756248114465072845013 136423974565182775144805)
                ·
                  rfl

theorem cell23_7173488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 7].length) (baseStart_7173488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173488 prefixEnd_7173488 := by exact prefixLift 7173488
  have htrace : WordTrace (prefixWord ++ tailWord_7173488) baseStart_7173488 baseEnd_7173488 := by
    simpa [prefixWord, tailWord_7173488, baseEnd_7173488] using wordTrace_append hprefix tailTrace_7173488
  have hstable : (prefixWord ++ tailWord_7173488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173488).length < 2 ^ (prefixWord ++ tailWord_7173488).sum := by decide
  have hdescent : baseEnd_7173488 < baseStart_7173488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173499 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 1, 2, 2]
def baseStart_7173499 : Nat := 118140960795 + 7173499 * 2 ^ 59
def prefixEnd_7173499 : Nat := 4983230072969 + 3 ^ 40 * 7173499 * 2
def baseEnd_7173499 : Nat := 3683452961547134385872185

theorem tailTrace_7173499 : CollatzResearch.WordTrace tailWord_7173499 prefixEnd_7173499 3683452961547134385872185 := by
  unfold tailWord_7173499
  simp only [CollatzResearch.WordTrace]
  refine ⟨261639003038645733936243551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174426002025763822624162367 261639003038645733936243551)
  ·
    refine ⟨392458504557968600904365327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261639003038645733936243551 392458504557968600904365327)
    ·
      refine ⟨588687756836952901356547991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392458504557968600904365327 588687756836952901356547991)
      ·
        refine ⟨883031635255429352034821987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588687756836952901356547991 883031635255429352034821987)
        ·
          refine ⟨1324547452883144028052232981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883031635255429352034821987 1324547452883144028052232981)
          ·
            refine ⟨62088161853897376314948421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1324547452883144028052232981 62088161853897376314948421)
            ·
              refine ⟨11641530347605758059052829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62088161853897376314948421 11641530347605758059052829)
              ·
                refine ⟨4365573880352159272144811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11641530347605758059052829 4365573880352159272144811)
                ·
                  refine ⟨6548360820528238908217217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365573880352159272144811 6548360820528238908217217)
                  ·
                    refine ⟨4911270615396179181162913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548360820528238908217217 4911270615396179181162913)
                    ·
                      refine ⟨3683452961547134385872185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911270615396179181162913 3683452961547134385872185)
                      ·
                        rfl

theorem cell23_7173499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 2, 2].length) (baseStart_7173499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173499 prefixEnd_7173499 := by exact prefixLift 7173499
  have htrace : WordTrace (prefixWord ++ tailWord_7173499) baseStart_7173499 baseEnd_7173499 := by
    simpa [prefixWord, tailWord_7173499, baseEnd_7173499] using wordTrace_append hprefix tailTrace_7173499
  have hstable : (prefixWord ++ tailWord_7173499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173499).length < 2 ^ (prefixWord ++ tailWord_7173499).sum := by decide
  have hdescent : baseEnd_7173499 < baseStart_7173499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173515 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 3]
def baseStart_7173515 : Nat := 118140960795 + 7173515 * 2 ^ 59
def prefixEnd_7173515 : Nat := 4983230072969 + 3 ^ 40 * 7173515 * 2
def baseEnd_7173515 : Nat := 3683461177237606323272111

theorem tailTrace_7173515 : CollatzResearch.WordTrace tailWord_7173515 prefixEnd_7173515 3683461177237606323272111 := by
  unfold tailWord_7173515
  simp only [CollatzResearch.WordTrace]
  refine ⟨261639586606587768668825999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174426391071058512445883999 261639586606587768668825999)
  ·
    refine ⟨392459379909881653003238999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261639586606587768668825999 392459379909881653003238999)
    ·
      refine ⟨588689069864822479504858499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392459379909881653003238999 588689069864822479504858499)
      ·
        refine ⟨883033604797233719257287749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588689069864822479504858499 883033604797233719257287749)
        ·
          refine ⟨165568800899481322360741453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 883033604797233719257287749 165568800899481322360741453)
          ·
            refine ⟨62088300337305495885278045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165568800899481322360741453 62088300337305495885278045)
            ·
              refine ⟨23283112626489560956979267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62088300337305495885278045 23283112626489560956979267)
              ·
                refine ⟨34924668939734341435468901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23283112626489560956979267 34924668939734341435468901)
                ·
                  refine ⟨6548375426200189019150419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34924668939734341435468901 6548375426200189019150419)
                  ·
                    refine ⟨9822563139300283528725629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548375426200189019150419 9822563139300283528725629)
                    ·
                      refine ⟨3683461177237606323272111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822563139300283528725629 3683461177237606323272111)
                      ·
                        rfl

theorem cell23_7173515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 3].length) (baseStart_7173515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173515 prefixEnd_7173515 := by exact prefixLift 7173515
  have htrace : WordTrace (prefixWord ++ tailWord_7173515) baseStart_7173515 baseEnd_7173515 := by
    simpa [prefixWord, tailWord_7173515, baseEnd_7173515] using wordTrace_append hprefix tailTrace_7173515
  have hstable : (prefixWord ++ tailWord_7173515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173515).length < 2 ^ (prefixWord ++ tailWord_7173515).sum := by decide
  have hdescent : baseEnd_7173515 < baseStart_7173515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173525 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_7173525 : Nat := 118140960795 + 7173525 * 2 ^ 59
def prefixEnd_7173525 : Nat := 4983230072969 + 3 ^ 40 * 7173525 * 2
def baseEnd_7173525 : Nat := 3683466312044151284147065

theorem tailTrace_7173525 : CollatzResearch.WordTrace tailWord_7173525 prefixEnd_7173525 3683466312044151284147065 := by
  unfold tailWord_7173525
  simp only [CollatzResearch.WordTrace]
  refine ⟨261639951336551540376690029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174426634224367693584460019 261639951336551540376690029)
  ·
    refine ⟨98114981751206827641258761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261639951336551540376690029 98114981751206827641258761)
    ·
      refine ⟨73586236313405120730944071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98114981751206827641258761 73586236313405120730944071)
      ·
        refine ⟨110379354470107681096416107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73586236313405120730944071 110379354470107681096416107)
        ·
          refine ⟨165569031705161521644624161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110379354470107681096416107 165569031705161521644624161)
          ·
            refine ⟨124176773778871141233468121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165569031705161521644624161 124176773778871141233468121)
            ·
              refine ⟨93132580334153355925101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124176773778871141233468121 93132580334153355925101091)
              ·
                refine ⟨139698870501230033887651637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93132580334153355925101091 139698870501230033887651637)
                ·
                  refine ⟨13096769109490315676967341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139698870501230033887651637 13096769109490315676967341)
                  ·
                    refine ⟨4911288416058868378862753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13096769109490315676967341 4911288416058868378862753)
                    ·
                      refine ⟨3683466312044151284147065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911288416058868378862753 3683466312044151284147065)
                      ·
                        rfl

theorem cell23_7173525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_7173525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173525 prefixEnd_7173525 := by exact prefixLift 7173525
  have htrace : WordTrace (prefixWord ++ tailWord_7173525) baseStart_7173525 baseEnd_7173525 := by
    simpa [prefixWord, tailWord_7173525, baseEnd_7173525] using wordTrace_append hprefix tailTrace_7173525
  have hstable : (prefixWord ++ tailWord_7173525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173525).length < 2 ^ (prefixWord ++ tailWord_7173525).sum := by decide
  have hdescent : baseEnd_7173525 < baseStart_7173525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173555 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 4, 2]
def baseStart_7173555 : Nat := 118140960795 + 7173555 * 2 ^ 59
def prefixEnd_7173555 : Nat := 4983230072969 + 3 ^ 40 * 7173555 * 2
def baseEnd_7173555 : Nat := 3683481716463786166771927

theorem tailTrace_7173555 : CollatzResearch.WordTrace tailWord_7173555 prefixEnd_7173555 3683481716463786166771927 := by
  unfold tailWord_7173555
  simp only [CollatzResearch.WordTrace]
  refine ⟨261641045526442855500282119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174427363684295237000188079 261641045526442855500282119)
  ·
    refine ⟨392461568289664283250423179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261641045526442855500282119 392461568289664283250423179)
    ·
      refine ⟨588692352434496424875634769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392461568289664283250423179 588692352434496424875634769)
      ·
        refine ⟨441519264325872318656726077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588692352434496424875634769 441519264325872318656726077)
        ·
          refine ⟨165569724122202119496272279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441519264325872318656726077 165569724122202119496272279)
          ·
            refine ⟨248354586183303179244408419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165569724122202119496272279 248354586183303179244408419)
            ·
              refine ⟨372531879274954768866612629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248354586183303179244408419 372531879274954768866612629)
              ·
                refine ⟨17462431841013504790622467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372531879274954768866612629 17462431841013504790622467)
                ·
                  refine ⟨26193647761520257185933701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17462431841013504790622467 26193647761520257185933701)
                  ·
                    refine ⟨4911308955285048222362569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26193647761520257185933701 4911308955285048222362569)
                    ·
                      refine ⟨3683481716463786166771927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911308955285048222362569 3683481716463786166771927)
                      ·
                        rfl

theorem cell23_7173555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4, 2].length) (baseStart_7173555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173555 prefixEnd_7173555 := by exact prefixLift 7173555
  have htrace : WordTrace (prefixWord ++ tailWord_7173555) baseStart_7173555 baseEnd_7173555 := by
    simpa [prefixWord, tailWord_7173555, baseEnd_7173555] using wordTrace_append hprefix tailTrace_7173555
  have hstable : (prefixWord ++ tailWord_7173555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173555).length < 2 ^ (prefixWord ++ tailWord_7173555).sum := by decide
  have hdescent : baseEnd_7173555 < baseStart_7173555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173568 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_7173568 : Nat := 118140960795 + 7173568 * 2 ^ 59
def prefixEnd_7173568 : Nat := 4983230072969 + 3 ^ 40 * 7173568 * 2
def baseEnd_7173568 : Nat := 3683488391712294615909367

theorem tailTrace_7173568 : CollatzResearch.WordTrace tailWord_7173568 prefixEnd_7173568 3683488391712294615909367 := by
  unfold tailWord_7173568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130820759837697879360252679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174427679783597172480336905 130820759837697879360252679)
  ·
    refine ⟨196231139756546819040379019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130820759837697879360252679 196231139756546819040379019)
    ·
      refine ⟨294346709634820228560568529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196231139756546819040379019 294346709634820228560568529)
      ·
        refine ⟨220760032226115171420426397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294346709634820228560568529 220760032226115171420426397)
        ·
          refine ⟨82785012084793189282659899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220760032226115171420426397 82785012084793189282659899)
          ·
            refine ⟨124177518127189783923989849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82785012084793189282659899 124177518127189783923989849)
            ·
              refine ⟨93133138595392337942992387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124177518127189783923989849 93133138595392337942992387)
              ·
                refine ⟨139699707893088506914488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93133138595392337942992387 139699707893088506914488581)
                ·
                  refine ⟨26193695229954095046466609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139699707893088506914488581 26193695229954095046466609)
                  ·
                    refine ⟨19645271422465571284849957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26193695229954095046466609 19645271422465571284849957)
                    ·
                      refine ⟨3683488391712294615909367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19645271422465571284849957 3683488391712294615909367)
                      ·
                        rfl

theorem cell23_7173568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_7173568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173568 prefixEnd_7173568 := by exact prefixLift 7173568
  have htrace : WordTrace (prefixWord ++ tailWord_7173568) baseStart_7173568 baseEnd_7173568 := by
    simpa [prefixWord, tailWord_7173568, baseEnd_7173568] using wordTrace_append hprefix tailTrace_7173568
  have hstable : (prefixWord ++ tailWord_7173568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173568).length < 2 ^ (prefixWord ++ tailWord_7173568).sum := by decide
  have hdescent : baseEnd_7173568 < baseStart_7173568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173589 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7173589 : Nat := 118140960795 + 7173589 * 2 ^ 59
def prefixEnd_7173589 : Nat := 4983230072969 + 3 ^ 40 * 7173589 * 2
def baseEnd_7173589 : Nat := 3683499174806039033746771

theorem tailTrace_7173589 : CollatzResearch.WordTrace tailWord_7173589 prefixEnd_7173589 3683499174806039033746771 := by
  unfold tailWord_7173589
  simp only [CollatzResearch.WordTrace]
  refine ⟨261642285608319679307019821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174428190405546452871346547 261642285608319679307019821)
  ·
    refine ⟨98115857103119879740132433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261642285608319679307019821 98115857103119879740132433)
    ·
      refine ⟨73586892827339909805099325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98115857103119879740132433 73586892827339909805099325)
      ·
        refine ⟨27595084810252466176912247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73586892827339909805099325 27595084810252466176912247)
        ·
          refine ⟨41392627215378699265368371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27595084810252466176912247 41392627215378699265368371)
          ·
            refine ⟨62088940823068048898052557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41392627215378699265368371 62088940823068048898052557)
            ·
              refine ⟨23283352808650518336769709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62088940823068048898052557 23283352808650518336769709)
              ·
                refine ⟨8731257303243944376288641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23283352808650518336769709 8731257303243944376288641)
                ·
                  refine ⟨6548442977432958282216481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8731257303243944376288641 6548442977432958282216481)
                  ·
                    refine ⟨4911332233074718711662361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548442977432958282216481 4911332233074718711662361)
                    ·
                      refine ⟨3683499174806039033746771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911332233074718711662361 3683499174806039033746771)
                      ·
                        rfl

theorem cell23_7173589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7173589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173589 prefixEnd_7173589 := by exact prefixLift 7173589
  have htrace : WordTrace (prefixWord ++ tailWord_7173589) baseStart_7173589 baseEnd_7173589 := by
    simpa [prefixWord, tailWord_7173589, baseEnd_7173589] using wordTrace_append hprefix tailTrace_7173589
  have hstable : (prefixWord ++ tailWord_7173589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173589).length < 2 ^ (prefixWord ++ tailWord_7173589).sum := by decide
  have hdescent : baseEnd_7173589 < baseStart_7173589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173629 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 5]
def baseStart_7173629 : Nat := 118140960795 + 7173629 * 2 ^ 59
def prefixEnd_7173629 : Nat := 4983230072969 + 3 ^ 40 * 7173629 * 2
def baseEnd_7173629 : Nat := 409279968225802097471843

theorem tailTrace_7173629 : CollatzResearch.WordTrace tailWord_7173629 prefixEnd_7173629 409279968225802097471843 := by
  unfold tailWord_7173629
  simp only [CollatzResearch.WordTrace]
  refine ⟨261643744528174766138475941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174429163018783177425650627 261643744528174766138475941)
  ·
    refine ⟨49058202099032768650964239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261643744528174766138475941 49058202099032768650964239)
    ·
      refine ⟨73587303148549152976446359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49058202099032768650964239 73587303148549152976446359)
      ·
        refine ⟨110380954722823729464669539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73587303148549152976446359 110380954722823729464669539)
        ·
          refine ⟨165571432084235594197004309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110380954722823729464669539 165571432084235594197004309)
          ·
            refine ⟨7761160878948543477984577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165571432084235594197004309 7761160878948543477984577)
            ·
              refine ⟨5820870659211407608488433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761160878948543477984577 5820870659211407608488433)
              ·
                refine ⟨4365652994408555706366325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5820870659211407608488433 4365652994408555706366325)
                ·
                  refine ⟨409279968225802097471843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365652994408555706366325 409279968225802097471843)
                  ·
                    rfl

theorem cell23_7173629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_7173629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173629 prefixEnd_7173629 := by exact prefixLift 7173629
  have htrace : WordTrace (prefixWord ++ tailWord_7173629) baseStart_7173629 baseEnd_7173629 := by
    simpa [prefixWord, tailWord_7173629, baseEnd_7173629] using wordTrace_append hprefix tailTrace_7173629
  have hstable : (prefixWord ++ tailWord_7173629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173629).length < 2 ^ (prefixWord ++ tailWord_7173629).sum := by decide
  have hdescent : baseEnd_7173629 < baseStart_7173629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173685 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 8]
def baseStart_7173685 : Nat := 118140960795 + 7173685 * 2 ^ 59
def prefixEnd_7173685 : Nat := 4983230072969 + 3 ^ 40 * 7173685 * 2
def baseEnd_7173685 : Nat := 409283163216541184238481

theorem tailTrace_7173685 : CollatzResearch.WordTrace tailWord_7173685 prefixEnd_7173685 409283163216541184238481 := by
  unfold tailWord_7173685
  simp only [CollatzResearch.WordTrace]
  refine ⟨261645787015971887702514509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174430524677314591801676339 261645787015971887702514509)
  ·
    refine ⟨98117170130989457888442941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261645787015971887702514509 98117170130989457888442941)
    ·
      refine ⟨36793938799121046708166103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98117170130989457888442941 36793938799121046708166103)
      ·
        refine ⟨55190908198681570062249155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36793938799121046708166103 55190908198681570062249155)
        ·
          refine ⟨82786362298022355093373733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55190908198681570062249155 82786362298022355093373733)
          ·
            refine ⟨15522442930879191580007575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82786362298022355093373733 15522442930879191580007575)
            ·
              refine ⟨23283664396318787370011363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15522442930879191580007575 23283664396318787370011363)
              ·
                refine ⟨34925496594478181055017045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23283664396318787370011363 34925496594478181055017045)
                ·
                  refine ⟨409283163216541184238481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34925496594478181055017045 409283163216541184238481)
                  ·
                    rfl

theorem cell23_7173685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_7173685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173685 prefixEnd_7173685 := by exact prefixLift 7173685
  have htrace : WordTrace (prefixWord ++ tailWord_7173685) baseStart_7173685 baseEnd_7173685 := by
    simpa [prefixWord, tailWord_7173685, baseEnd_7173685] using wordTrace_append hprefix tailTrace_7173685
  have hstable : (prefixWord ++ tailWord_7173685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173685).length < 2 ^ (prefixWord ++ tailWord_7173685).sum := by decide
  have hdescent : baseEnd_7173685 < baseStart_7173685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173689 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 1, 4]
def baseStart_7173689 : Nat := 118140960795 + 7173689 * 2 ^ 59
def prefixEnd_7173689 : Nat := 4983230072969 + 3 ^ 40 * 7173689 * 2
def baseEnd_7173689 : Nat := 1227850174290496214165437

theorem tailTrace_7173689 : CollatzResearch.WordTrace tailWord_7173689 prefixEnd_7173689 1227850174290496214165437 := by
  unfold tailWord_7173689
  simp only [CollatzResearch.WordTrace]
  refine ⟨261645932907957396385660121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174430621938638264257106747 261645932907957396385660121)
  ·
    refine ⟨196234449680968047289245091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261645932907957396385660121 196234449680968047289245091)
    ·
      refine ⟨294351674521452070933867637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196234449680968047289245091 294351674521452070933867637)
      ·
        refine ⟨27595469486386131650050091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294351674521452070933867637 27595469486386131650050091)
        ·
          refine ⟨41393204229579197475075137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27595469486386131650050091 41393204229579197475075137)
          ·
            refine ⟨31044903172184398106306353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41393204229579197475075137 31044903172184398106306353)
            ·
              refine ⟨23283677379138298579729765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31044903172184398106306353 23283677379138298579729765)
              ·
                refine ⟨4365689508588430983699331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23283677379138298579729765 4365689508588430983699331)
                ·
                  refine ⟨6548534262882646475548997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365689508588430983699331 6548534262882646475548997)
                  ·
                    refine ⟨1227850174290496214165437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6548534262882646475548997 1227850174290496214165437)
                    ·
                      rfl

theorem cell23_7173689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_7173689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173689 prefixEnd_7173689 := by exact prefixLift 7173689
  have htrace : WordTrace (prefixWord ++ tailWord_7173689) baseStart_7173689 baseEnd_7173689 := by
    simpa [prefixWord, tailWord_7173689, baseEnd_7173689] using wordTrace_append hprefix tailTrace_7173689
  have hstable : (prefixWord ++ tailWord_7173689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173689).length < 2 ^ (prefixWord ++ tailWord_7173689).sum := by decide
  have hdescent : baseEnd_7173689 < baseStart_7173689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173712 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_7173712 : Nat := 118140960795 + 7173712 * 2 ^ 59
def prefixEnd_7173712 : Nat := 4983230072969 + 3 ^ 40 * 7173712 * 2
def baseEnd_7173712 : Nat := 3683562332926542052508705

theorem tailTrace_7173712 : CollatzResearch.WordTrace tailWord_7173712 prefixEnd_7173712 3683562332926542052508705 := by
  unfold tailWord_7173712
  simp only [CollatzResearch.WordTrace]
  refine ⟨130823385893437035656873695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174431181191249380875831593 130823385893437035656873695)
  ·
    refine ⟨196235078840155553485310543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130823385893437035656873695 196235078840155553485310543)
    ·
      refine ⟨294352618260233330227965815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196235078840155553485310543 294352618260233330227965815)
      ·
        refine ⟨441528927390349995341948723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294352618260233330227965815 441528927390349995341948723)
        ·
          refine ⟨662293391085524993012923085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441528927390349995341948723 662293391085524993012923085)
          ·
            refine ⟨248360021657071872379846157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 662293391085524993012923085 248360021657071872379846157)
            ·
              refine ⟨93135008121401952142442309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248360021657071872379846157 93135008121401952142442309)
              ·
                refine ⟨17462814022762866026707933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93135008121401952142442309 17462814022762866026707933)
                ·
                  refine ⟨6548555258536074760015475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17462814022762866026707933 6548555258536074760015475)
                  ·
                    refine ⟨9822832887804112140023213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548555258536074760015475 9822832887804112140023213)
                    ·
                      refine ⟨3683562332926542052508705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822832887804112140023213 3683562332926542052508705)
                      ·
                        rfl

theorem cell23_7173712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_7173712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173712 prefixEnd_7173712 := by exact prefixLift 7173712
  have htrace : WordTrace (prefixWord ++ tailWord_7173712) baseStart_7173712 baseEnd_7173712 := by
    simpa [prefixWord, tailWord_7173712, baseEnd_7173712] using wordTrace_append hprefix tailTrace_7173712
  have hstable : (prefixWord ++ tailWord_7173712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173712).length < 2 ^ (prefixWord ++ tailWord_7173712).sum := by decide
  have hdescent : baseEnd_7173712 < baseStart_7173712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_7173722 : Nat := 118140960795 + 7173722 * 2 ^ 59
def prefixEnd_7173722 : Nat := 4983230072969 + 3 ^ 40 * 7173722 * 2
def baseEnd_7173722 : Nat := 3683567467733087013383659

theorem tailTrace_7173722 : CollatzResearch.WordTrace tailWord_7173722 prefixEnd_7173722 3683567467733087013383659 := by
  unfold tailWord_7173722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65411784129209460755402855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174431424344558562014407613 65411784129209460755402855)
  ·
    refine ⟨98117676193814191133104283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65411784129209460755402855 98117676193814191133104283)
    ·
      refine ⟨147176514290721286699656425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98117676193814191133104283 147176514290721286699656425)
      ·
        refine ⟨110382385718040965024742319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147176514290721286699656425 110382385718040965024742319)
        ·
          refine ⟨165573578577061447537113479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110382385718040965024742319 165573578577061447537113479)
          ·
            refine ⟨248360367865592171305670219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165573578577061447537113479 248360367865592171305670219)
            ·
              refine ⟨372540551798388256958505329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248360367865592171305670219 372540551798388256958505329)
              ·
                refine ⟨279405413848791192718878997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372540551798388256958505329 279405413848791192718878997)
                ·
                  refine ⟨13097128774162087158697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279405413848791192718878997 13097128774162087158697453)
                  ·
                    refine ⟨4911423290310782684511545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13097128774162087158697453 4911423290310782684511545)
                    ·
                      refine ⟨3683567467733087013383659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911423290310782684511545 3683567467733087013383659)
                      ·
                        rfl

theorem cell23_7173722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_7173722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173722 prefixEnd_7173722 := by exact prefixLift 7173722
  have htrace : WordTrace (prefixWord ++ tailWord_7173722) baseStart_7173722 baseEnd_7173722 := by
    simpa [prefixWord, tailWord_7173722, baseEnd_7173722] using wordTrace_append hprefix tailTrace_7173722
  have hstable : (prefixWord ++ tailWord_7173722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173722).length < 2 ^ (prefixWord ++ tailWord_7173722).sum := by decide
  have hdescent : baseEnd_7173722 < baseStart_7173722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173732 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_7173732 : Nat := 118140960795 + 7173732 * 2 ^ 59
def prefixEnd_7173732 : Nat := 4983230072969 + 3 ^ 40 * 7173732 * 2
def baseEnd_7173732 : Nat := 1227857534179877324752871

theorem tailTrace_7173732 : CollatzResearch.WordTrace tailWord_7173732 prefixEnd_7173732 1227857534179877324752871 := by
  unfold tailWord_7173732
  simp only [CollatzResearch.WordTrace]
  refine ⟨130823750623400807364737725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174431667497867743152983633 130823750623400807364737725)
  ·
    refine ⟨49058906483775302761776647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130823750623400807364737725 49058906483775302761776647)
    ·
      refine ⟨73588359725662954142664971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49058906483775302761776647 73588359725662954142664971)
      ·
        refine ⟨110382539588494431213997457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73588359725662954142664971 110382539588494431213997457)
        ·
          refine ⟨82786904691370823410498093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110382539588494431213997457 82786904691370823410498093)
          ·
            refine ⟨31045089259264058778936785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82786904691370823410498093 31045089259264058778936785)
            ·
              refine ⟨23283816944448044084202589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31045089259264058778936785 23283816944448044084202589)
              ·
                refine ⟨8731431354168016531575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23283816944448044084202589 8731431354168016531575971)
                ·
                  refine ⟨13097147031252024797363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8731431354168016531575971 13097147031252024797363957)
                  ·
                    refine ⟨1227857534179877324752871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13097147031252024797363957 1227857534179877324752871)
                    ·
                      rfl

theorem cell23_7173732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_7173732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173732 prefixEnd_7173732 := by exact prefixLift 7173732
  have htrace : WordTrace (prefixWord ++ tailWord_7173732) baseStart_7173732 baseEnd_7173732 := by
    simpa [prefixWord, tailWord_7173732, baseEnd_7173732] using wordTrace_append hprefix tailTrace_7173732
  have hstable : (prefixWord ++ tailWord_7173732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173732).length < 2 ^ (prefixWord ++ tailWord_7173732).sum := by decide
  have hdescent : baseEnd_7173732 < baseStart_7173732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173746 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7173746 : Nat := 118140960795 + 7173746 * 2 ^ 59
def prefixEnd_7173746 : Nat := 4983230072969 + 3 ^ 40 * 7173746 * 2
def baseEnd_7173746 : Nat := 3683579791268794919483549

theorem tailTrace_7173746 : CollatzResearch.WordTrace tailWord_7173746 prefixEnd_7173746 3683579791268794919483549 := by
  unfold tailWord_7173746
  simp only [CollatzResearch.WordTrace]
  refine ⟨65412002967187723780121273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174432007912500596746990061 65412002967187723780121273)
  ·
    refine ⟨49059002225390792835090955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65412002967187723780121273 49059002225390792835090955)
    ·
      refine ⟨73588503338086189252636433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49059002225390792835090955 73588503338086189252636433)
      ·
        refine ⟨55191377503564641939477325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73588503338086189252636433 55191377503564641939477325)
        ·
          refine ⟨20696766563836740727303997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55191377503564641939477325 20696766563836740727303997)
          ·
            refine ⟨7761287461438777772738999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20696766563836740727303997 7761287461438777772738999)
            ·
              refine ⟨11641931192158166659108499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761287461438777772738999 11641931192158166659108499)
              ·
                refine ⟨17462896788237249988662749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11641931192158166659108499 17462896788237249988662749)
                ·
                  refine ⟨6548586295588968745748531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17462896788237249988662749 6548586295588968745748531)
                  ·
                    refine ⟨9822879443383453118622797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548586295588968745748531 9822879443383453118622797)
                    ·
                      refine ⟨3683579791268794919483549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822879443383453118622797 3683579791268794919483549)
                      ·
                        rfl

theorem cell23_7173746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7173746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173746 prefixEnd_7173746 := by exact prefixLift 7173746
  have htrace : WordTrace (prefixWord ++ tailWord_7173746) baseStart_7173746 baseEnd_7173746 := by
    simpa [prefixWord, tailWord_7173746, baseEnd_7173746] using wordTrace_append hprefix tailTrace_7173746
  have hstable : (prefixWord ++ tailWord_7173746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173746).length < 2 ^ (prefixWord ++ tailWord_7173746).sum := by decide
  have hdescent : baseEnd_7173746 < baseStart_7173746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173755 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_7173755 : Nat := 118140960795 + 7173755 * 2 ^ 59
def prefixEnd_7173755 : Nat := 4983230072969 + 3 ^ 40 * 7173755 * 2
def baseEnd_7173755 : Nat := 3683584412594685384271007

theorem tailTrace_7173755 : CollatzResearch.WordTrace tailWord_7173755 prefixEnd_7173755 3683584412594685384271007 := by
  unfold tailWord_7173755
  simp only [CollatzResearch.WordTrace]
  refine ⟨261648340125718289657562719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174432226750478859771708479 261648340125718289657562719)
  ·
    refine ⟨392472510188577434486344079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261648340125718289657562719 392472510188577434486344079)
    ·
      refine ⟨588708765282866151729516119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392472510188577434486344079 588708765282866151729516119)
      ·
        refine ⟨883063147924299227594274179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588708765282866151729516119 883063147924299227594274179)
        ·
          refine ⟨1324594721886448841391411269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883063147924299227594274179 1324594721886448841391411269)
          ·
            refine ⟨248361510353709157760889613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1324594721886448841391411269 248361510353709157760889613)
            ·
              refine ⟨93135566382640934160333605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248361510353709157760889613 93135566382640934160333605)
              ·
                refine ⟨17462918696745175155062551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93135566382640934160333605 17462918696745175155062551)
                ·
                  refine ⟨26194378045117762732593827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17462918696745175155062551 26194378045117762732593827)
                  ·
                    refine ⟨39291567067676644098890741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26194378045117762732593827 39291567067676644098890741)
                    ·
                      refine ⟨3683584412594685384271007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39291567067676644098890741 3683584412594685384271007)
                      ·
                        rfl

theorem cell23_7173755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_7173755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173755 prefixEnd_7173755 := by exact prefixLift 7173755
  have htrace : WordTrace (prefixWord ++ tailWord_7173755) baseStart_7173755 baseEnd_7173755 := by
    simpa [prefixWord, tailWord_7173755, baseEnd_7173755] using wordTrace_append hprefix tailTrace_7173755
  have hstable : (prefixWord ++ tailWord_7173755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173755).length < 2 ^ (prefixWord ++ tailWord_7173755).sum := by decide
  have hdescent : baseEnd_7173755 < baseStart_7173755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173765 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_7173765 : Nat := 118140960795 + 7173765 * 2 ^ 59
def prefixEnd_7173765 : Nat := 4983230072969 + 3 ^ 40 * 7173765 * 2
def baseEnd_7173765 : Nat := 3683589547401230345145961

theorem tailTrace_7173765 : CollatzResearch.WordTrace tailWord_7173765 prefixEnd_7173765 3683589547401230345145961 := by
  unfold tailWord_7173765
  simp only [CollatzResearch.WordTrace]
  refine ⟨261648704855682061365426749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174432469903788040910284499 261648704855682061365426749)
  ·
    refine ⟨98118264320880773012035031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261648704855682061365426749 98118264320880773012035031)
    ·
      refine ⟨147177396481321159518052547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98118264320880773012035031 147177396481321159518052547)
      ·
        refine ⟨220766094721981739277078821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147177396481321159518052547 220766094721981739277078821)
        ·
          refine ⟨41393642760371576114452279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220766094721981739277078821 41393642760371576114452279)
          ·
            refine ⟨62090464140557364171678419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41393642760371576114452279 62090464140557364171678419)
            ·
              refine ⟨93135696210836046257517629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62090464140557364171678419 93135696210836046257517629)
              ·
                refine ⟨34925886079063517346569111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93135696210836046257517629 34925886079063517346569111)
                ·
                  refine ⟨52388829118595276019853667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34925886079063517346569111 52388829118595276019853667)
                  ·
                    refine ⟨78583243677892914029780501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52388829118595276019853667 78583243677892914029780501)
                    ·
                      refine ⟨3683589547401230345145961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78583243677892914029780501 3683589547401230345145961)
                      ·
                        rfl

theorem cell23_7173765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_7173765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173765 prefixEnd_7173765 := by exact prefixLift 7173765
  have htrace : WordTrace (prefixWord ++ tailWord_7173765) baseStart_7173765 baseEnd_7173765 := by
    simpa [prefixWord, tailWord_7173765, baseEnd_7173765] using wordTrace_append hprefix tailTrace_7173765
  have hstable : (prefixWord ++ tailWord_7173765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173765).length < 2 ^ (prefixWord ++ tailWord_7173765).sum := by decide
  have hdescent : baseEnd_7173765 < baseStart_7173765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173769 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 3, 2, 2]
def baseStart_7173769 : Nat := 118140960795 + 7173769 * 2 ^ 59
def prefixEnd_7173769 : Nat := 4983230072969 + 3 ^ 40 * 7173769 * 2
def baseEnd_7173769 : Nat := 3683591601323848329495943

theorem tailTrace_7173769 : CollatzResearch.WordTrace tailWord_7173769 prefixEnd_7173769 3683591601323848329495943 := by
  unfold tailWord_7173769
  simp only [CollatzResearch.WordTrace]
  refine ⟨261648850747667570048572361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174432567165111713365714907 261648850747667570048572361)
  ·
    refine ⟨196236638060750677536429271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261648850747667570048572361 196236638060750677536429271)
    ·
      refine ⟨294354957091126016304643907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196236638060750677536429271 294354957091126016304643907)
      ·
        refine ⟨441532435636689024456965861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294354957091126016304643907 441532435636689024456965861)
        ·
          refine ⟨82787331681879192085681099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441532435636689024456965861 82787331681879192085681099)
          ·
            refine ⟨124180997522818788128521649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82787331681879192085681099 124180997522818788128521649)
            ·
              refine ⟨93135748142114091096391237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124180997522818788128521649 93135748142114091096391237)
              ·
                refine ⟨17462952776646392080573357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93135748142114091096391237 17462952776646392080573357)
                ·
                  refine ⟨6548607291242397030215009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17462952776646392080573357 6548607291242397030215009)
                  ·
                    refine ⟨4911455468431797772661257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548607291242397030215009 4911455468431797772661257)
                    ·
                      refine ⟨3683591601323848329495943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911455468431797772661257 3683591601323848329495943)
                      ·
                        rfl

theorem cell23_7173769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2, 2].length) (baseStart_7173769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173769 prefixEnd_7173769 := by exact prefixLift 7173769
  have htrace : WordTrace (prefixWord ++ tailWord_7173769) baseStart_7173769 baseEnd_7173769 := by
    simpa [prefixWord, tailWord_7173769, baseEnd_7173769] using wordTrace_append hprefix tailTrace_7173769
  have hstable : (prefixWord ++ tailWord_7173769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173769).length < 2 ^ (prefixWord ++ tailWord_7173769).sum := by decide
  have hdescent : baseEnd_7173769 < baseStart_7173769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173772 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_7173772 : Nat := 118140960795 + 7173772 * 2 ^ 59
def prefixEnd_7173772 : Nat := 4983230072969 + 3 ^ 40 * 7173772 * 2
def baseEnd_7173772 : Nat := 3683593141765811817758429

theorem tailTrace_7173772 : CollatzResearch.WordTrace tailWord_7173772 prefixEnd_7173772 3683593141765811817758429 := by
  unfold tailWord_7173772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130824480083328350780465785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174432640111104467707287713 130824480083328350780465785)
  ·
    refine ⟨98118360062496263085349339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130824480083328350780465785 98118360062496263085349339)
    ·
      refine ⟨147177540093744394628024009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98118360062496263085349339 147177540093744394628024009)
      ·
        refine ⟨110383155070308295971018007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147177540093744394628024009 110383155070308295971018007)
        ·
          refine ⟨165574732605462443956527011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110383155070308295971018007 165574732605462443956527011)
          ·
            refine ⟨248362098908193665934790517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165574732605462443956527011 248362098908193665934790517)
            ·
              refine ⟨23283946772643156181386611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248362098908193665934790517 23283946772643156181386611)
              ·
                refine ⟨34925920158964734272079917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23283946772643156181386611 34925920158964734272079917)
                ·
                  refine ⟨13097220059611775352029969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34925920158964734272079917 13097220059611775352029969)
                  ·
                    refine ⟨9822915044708831514022477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13097220059611775352029969 9822915044708831514022477)
                    ·
                      refine ⟨3683593141765811817758429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9822915044708831514022477 3683593141765811817758429)
                      ·
                        rfl

theorem cell23_7173772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_7173772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173772 prefixEnd_7173772 := by exact prefixLift 7173772
  have htrace : WordTrace (prefixWord ++ tailWord_7173772) baseStart_7173772 baseEnd_7173772 := by
    simpa [prefixWord, tailWord_7173772, baseEnd_7173772] using wordTrace_append hprefix tailTrace_7173772
  have hstable : (prefixWord ++ tailWord_7173772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173772).length < 2 ^ (prefixWord ++ tailWord_7173772).sum := by decide
  have hdescent : baseEnd_7173772 < baseStart_7173772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173837 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7173837 : Nat := 118140960795 + 7173837 * 2 ^ 59
def prefixEnd_7173837 : Nat := 4983230072969 + 3 ^ 40 * 7173837 * 2
def baseEnd_7173837 : Nat := 3683626518008354063445631

theorem tailTrace_7173837 : CollatzResearch.WordTrace tailWord_7173837 prefixEnd_7173837 3683626518008354063445631 := by
  unfold tailWord_7173837
  simp only [CollatzResearch.WordTrace]
  refine ⟨261651330911421217662047765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174434220607614145108031843 261651330911421217662047765)
  ·
    refine ⟨12264906136472869577908489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261651330911421217662047765 12264906136472869577908489)
    ·
      refine ⟨9198679602354652183431367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12264906136472869577908489 9198679602354652183431367)
      ·
        refine ⟨13798019403531978275147051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9198679602354652183431367 13798019403531978275147051)
        ·
          refine ⟨20697029105297967412720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13798019403531978275147051 20697029105297967412720577)
          ·
            refine ⟨15522771828973475559540433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20697029105297967412720577 15522771828973475559540433)
            ·
              refine ⟨11642078871730106669655325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15522771828973475559540433 11642078871730106669655325)
              ·
                refine ⟨4365779576898790001120747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642078871730106669655325 4365779576898790001120747)
                ·
                  refine ⟨6548669365348185001681121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365779576898790001120747 6548669365348185001681121)
                  ·
                    refine ⟨4911502024011138751260841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548669365348185001681121 4911502024011138751260841)
                    ·
                      refine ⟨3683626518008354063445631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911502024011138751260841 3683626518008354063445631)
                      ·
                        rfl

theorem cell23_7173837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7173837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173837 prefixEnd_7173837 := by exact prefixLift 7173837
  have htrace : WordTrace (prefixWord ++ tailWord_7173837) baseStart_7173837 baseEnd_7173837 := by
    simpa [prefixWord, tailWord_7173837, baseEnd_7173837] using wordTrace_append hprefix tailTrace_7173837
  have hstable : (prefixWord ++ tailWord_7173837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173837).length < 2 ^ (prefixWord ++ tailWord_7173837).sum := by decide
  have hdescent : baseEnd_7173837 < baseStart_7173837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173853 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7173853 : Nat := 118140960795 + 7173853 * 2 ^ 59
def prefixEnd_7173853 : Nat := 4983230072969 + 3 ^ 40 * 7173853 * 2
def baseEnd_7173853 : Nat := 3683634733698826000845557

theorem tailTrace_7173853 : CollatzResearch.WordTrace tailWord_7173853 prefixEnd_7173853 3683634733698826000845557 := by
  unfold tailWord_7173853
  simp only [CollatzResearch.WordTrace]
  refine ⟨261651914479363252394630213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174434609652908834929753475 261651914479363252394630213)
  ·
    refine ⟨49059733964880609823993165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261651914479363252394630213 49059733964880609823993165)
    ·
      refine ⟨18397400236830228683997437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49059733964880609823993165 18397400236830228683997437)
      ·
        refine ⟨6899025088811335756499039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18397400236830228683997437 6899025088811335756499039)
        ·
          refine ⟨10348537633217003634748559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899025088811335756499039 10348537633217003634748559)
          ·
            refine ⟨15522806449825505452122839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348537633217003634748559 15522806449825505452122839)
            ·
              refine ⟨23284209674738258178184259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15522806449825505452122839 23284209674738258178184259)
              ·
                refine ⟨34926314512107387267276389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23284209674738258178184259 34926314512107387267276389)
                ·
                  refine ⟨6548683971020135112614323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34926314512107387267276389 6548683971020135112614323)
                  ·
                    refine ⟨9823025956530202668921485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548683971020135112614323 9823025956530202668921485)
                    ·
                      refine ⟨3683634733698826000845557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823025956530202668921485 3683634733698826000845557)
                      ·
                        rfl

theorem cell23_7173853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7173853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173853 prefixEnd_7173853 := by exact prefixLift 7173853
  have htrace : WordTrace (prefixWord ++ tailWord_7173853) baseStart_7173853 baseEnd_7173853 := by
    simpa [prefixWord, tailWord_7173853, baseEnd_7173853] using wordTrace_append hprefix tailTrace_7173853
  have hstable : (prefixWord ++ tailWord_7173853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173853).length < 2 ^ (prefixWord ++ tailWord_7173853).sum := by decide
  have hdescent : baseEnd_7173853 < baseStart_7173853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173899 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 5]
def baseStart_7173899 : Nat := 118140960795 + 7173899 * 2 ^ 59
def prefixEnd_7173899 : Nat := 4983230072969 + 3 ^ 40 * 7173899 * 2
def baseEnd_7173899 : Nat := 409295372645436980096705

theorem tailTrace_7173899 : CollatzResearch.WordTrace tailWord_7173899 prefixEnd_7173899 409295372645436980096705 := by
  unfold tailWord_7173899
  simp only [CollatzResearch.WordTrace]
  refine ⟨261653592237196602250804751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174435728158131068167203167 261653592237196602250804751)
  ·
    refine ⟨392480388355794903376207127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261653592237196602250804751 392480388355794903376207127)
    ·
      refine ⟨588720582533692355064310691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392480388355794903376207127 588720582533692355064310691)
      ·
        refine ⟨883080873800538532596466037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588720582533692355064310691 883080873800538532596466037)
        ·
          refine ⟨82788831918800487430918691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 883080873800538532596466037 82788831918800487430918691)
          ·
            refine ⟨124183247878200731146378037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82788831918800487430918691 124183247878200731146378037)
            ·
              refine ⟨11642179488581318544972941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124183247878200731146378037 11642179488581318544972941)
              ·
                refine ⟨4365817308217994454364853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642179488581318544972941 4365817308217994454364853)
                ·
                  refine ⟨409295372645436980096705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365817308217994454364853 409295372645436980096705)
                  ·
                    rfl

theorem cell23_7173899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 5].length) (baseStart_7173899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173899 prefixEnd_7173899 := by exact prefixLift 7173899
  have htrace : WordTrace (prefixWord ++ tailWord_7173899) baseStart_7173899 baseEnd_7173899 := by
    simpa [prefixWord, tailWord_7173899, baseEnd_7173899] using wordTrace_append hprefix tailTrace_7173899
  have hstable : (prefixWord ++ tailWord_7173899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173899).length < 2 ^ (prefixWord ++ tailWord_7173899).sum := by decide
  have hdescent : baseEnd_7173899 < baseStart_7173899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173912 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_7173912 : Nat := 118140960795 + 7173912 * 2 ^ 59
def prefixEnd_7173912 : Nat := 4983230072969 + 3 ^ 40 * 7173912 * 2
def baseEnd_7173912 : Nat := 1227888343019147090002595

theorem tailTrace_7173912 : CollatzResearch.WordTrace tailWord_7173912 prefixEnd_7173912 1227888343019147090002595 := by
  unfold tailWord_7173912
  simp only [CollatzResearch.WordTrace]
  refine ⟨130827033193074752735513995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174436044257433003647351993 130827033193074752735513995)
  ·
    refine ⟨196240549789612129103270993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130827033193074752735513995 196240549789612129103270993)
    ·
      refine ⟨147180412342209096827453245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196240549789612129103270993 147180412342209096827453245)
      ·
        refine ⟨55192654628328411310294967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147180412342209096827453245 55192654628328411310294967)
        ·
          refine ⟨82788981942492616965442451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55192654628328411310294967 82788981942492616965442451)
          ·
            refine ⟨124183472913738925448163677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82788981942492616965442451 124183472913738925448163677)
            ·
              refine ⟨46568802342652097043061379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124183472913738925448163677 46568802342652097043061379)
              ·
                refine ⟨69853203513978145564592069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46568802342652097043061379 69853203513978145564592069)
                ·
                  refine ⟨13097475658870902293361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69853203513978145564592069 13097475658870902293361013)
                  ·
                    refine ⟨1227888343019147090002595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13097475658870902293361013 1227888343019147090002595)
                    ·
                      rfl

theorem cell23_7173912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_7173912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173912 prefixEnd_7173912 := by exact prefixLift 7173912
  have htrace : WordTrace (prefixWord ++ tailWord_7173912) baseStart_7173912 baseEnd_7173912 := by
    simpa [prefixWord, tailWord_7173912, baseEnd_7173912] using wordTrace_append hprefix tailTrace_7173912
  have hstable : (prefixWord ++ tailWord_7173912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173912).length < 2 ^ (prefixWord ++ tailWord_7173912).sum := by decide
  have hdescent : baseEnd_7173912 < baseStart_7173912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173916 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 5]
def baseStart_7173916 : Nat := 118140960795 + 7173916 * 2 ^ 59
def prefixEnd_7173916 : Nat := 4983230072969 + 3 ^ 40 * 7173916 * 2
def baseEnd_7173916 : Nat := 409296342553339917150863

theorem tailTrace_7173916 : CollatzResearch.WordTrace tailWord_7173916 prefixEnd_7173916 409296342553339917150863 := by
  unfold tailWord_7173916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130827106139067507077086801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174436141518756676102782401 130827106139067507077086801)
  ·
    refine ⟨98120329604300630307815101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130827106139067507077086801 98120329604300630307815101)
    ·
      refine ⟨36795123601612736365430663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98120329604300630307815101 36795123601612736365430663)
      ·
        refine ⟨55192685402419104548145995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36795123601612736365430663 55192685402419104548145995)
        ·
          refine ⟨82789028103628656822218993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55192685402419104548145995 82789028103628656822218993)
          ·
            refine ⟨62091771077721492616664245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82789028103628656822218993 62091771077721492616664245)
            ·
              refine ⟨5821103538536389932812273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62091771077721492616664245 5821103538536389932812273)
              ·
                refine ⟨4365827653902292449609205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821103538536389932812273 4365827653902292449609205)
                ·
                  refine ⟨409296342553339917150863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365827653902292449609205 409296342553339917150863)
                  ·
                    rfl

theorem cell23_7173916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_7173916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173916 prefixEnd_7173916 := by exact prefixLift 7173916
  have htrace : WordTrace (prefixWord ++ tailWord_7173916) baseStart_7173916 baseEnd_7173916 := by
    simpa [prefixWord, tailWord_7173916, baseEnd_7173916] using wordTrace_append hprefix tailTrace_7173916
  have hstable : (prefixWord ++ tailWord_7173916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173916).length < 2 ^ (prefixWord ++ tailWord_7173916).sum := by decide
  have hdescent : baseEnd_7173916 < baseStart_7173916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173919 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 5, 2]
def baseStart_7173919 : Nat := 118140960795 + 7173919 * 2 ^ 59
def prefixEnd_7173919 : Nat := 4983230072969 + 3 ^ 40 * 7173919 * 2
def baseEnd_7173919 : Nat := 3683668623422022742620253

theorem tailTrace_7173919 : CollatzResearch.WordTrace tailWord_7173919 prefixEnd_7173919 3683668623422022742620253 := by
  unfold tailWord_7173919
  simp only [CollatzResearch.WordTrace]
  refine ⟨261654321697124145666532811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174436214464749430444355207 261654321697124145666532811)
  ·
    refine ⟨392481482545686218499799217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261654321697124145666532811 392481482545686218499799217)
    ·
      refine ⟨294361111909264663874849413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392481482545686218499799217 294361111909264663874849413)
      ·
        refine ⟨55192708482987124476534265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294361111909264663874849413 55192708482987124476534265)
        ·
          refine ⟨41394531362240343357400699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55192708482987124476534265 41394531362240343357400699)
          ·
            refine ⟨62091797043360515036101049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41394531362240343357400699 62091797043360515036101049)
            ·
              refine ⟨46568847782520386277075787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62091797043360515036101049 46568847782520386277075787)
              ·
                refine ⟨69853271673780579415613681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46568847782520386277075787 69853271673780579415613681)
                ·
                  refine ⟨52389953755335434561710261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69853271673780579415613681 52389953755335434561710261)
                  ·
                    refine ⟨4911558164562696990160337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52389953755335434561710261 4911558164562696990160337)
                    ·
                      refine ⟨3683668623422022742620253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911558164562696990160337 3683668623422022742620253)
                      ·
                        rfl

theorem cell23_7173919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_7173919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173919 prefixEnd_7173919 := by exact prefixLift 7173919
  have htrace : WordTrace (prefixWord ++ tailWord_7173919) baseStart_7173919 baseEnd_7173919 := by
    simpa [prefixWord, tailWord_7173919, baseEnd_7173919] using wordTrace_append hprefix tailTrace_7173919
  have hstable : (prefixWord ++ tailWord_7173919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173919).length < 2 ^ (prefixWord ++ tailWord_7173919).sum := by decide
  have hdescent : baseEnd_7173919 < baseStart_7173919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173962 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_7173962 : Nat := 118140960795 + 7173962 * 2 ^ 59
def prefixEnd_7173962 : Nat := 4983230072969 + 3 ^ 40 * 7173962 * 2
def baseEnd_7173962 : Nat := 3683690703090166074382555

theorem tailTrace_7173962 : CollatzResearch.WordTrace tailWord_7173962 prefixEnd_7173962 3683690703090166074382555 := by
  unfold tailWord_7173962
  simp only [CollatzResearch.WordTrace]
  refine ⟨65413972508992091002587035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174437260023978909340232093 65413972508992091002587035)
  ·
    refine ⟨98120958763488136503880553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65413972508992091002587035 98120958763488136503880553)
    ·
      refine ⟨73590719072616102377910415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98120958763488136503880553 73590719072616102377910415)
      ·
        refine ⟨110386078608924153566865623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73590719072616102377910415 110386078608924153566865623)
        ·
          refine ⟨165579117913386230350298435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110386078608924153566865623 165579117913386230350298435)
          ·
            refine ⟨248368676870079345525447653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165579117913386230350298435 248368676870079345525447653)
            ·
              refine ⟨46569126913139877286021435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248368676870079345525447653 46569126913139877286021435)
              ·
                refine ⟨69853690369709815929032153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46569126913139877286021435 69853690369709815929032153)
                ·
                  refine ⟨52390267777282361946774115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69853690369709815929032153 52390267777282361946774115)
                  ·
                    refine ⟨78585401665923542920161173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52390267777282361946774115 78585401665923542920161173)
                    ·
                      refine ⟨3683690703090166074382555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78585401665923542920161173 3683690703090166074382555)
                      ·
                        rfl

theorem cell23_7173962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_7173962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7173962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7173962 prefixEnd_7173962 := by exact prefixLift 7173962
  have htrace : WordTrace (prefixWord ++ tailWord_7173962) baseStart_7173962 baseEnd_7173962 := by
    simpa [prefixWord, tailWord_7173962, baseEnd_7173962] using wordTrace_append hprefix tailTrace_7173962
  have hstable : (prefixWord ++ tailWord_7173962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173962).length < 2 ^ (prefixWord ++ tailWord_7173962).sum := by decide
  have hdescent : baseEnd_7173962 < baseStart_7173962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174012 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_7174012 : Nat := 118140960795 + 7174012 * 2 ^ 59
def prefixEnd_7174012 : Nat := 4983230072969 + 3 ^ 40 * 7174012 * 2
def baseEnd_7174012 : Nat := 3683716377122890878757325

theorem tailTrace_7174012 : CollatzResearch.WordTrace tailWord_7174012 prefixEnd_7174012 3683716377122890878757325 := by
  unfold tailWord_7174012
  simp only [CollatzResearch.WordTrace]
  refine ⟨130828856842893611274834145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174438475790524815033112193 130828856842893611274834145)
  ·
    refine ⟨98121642632170208456125609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130828856842893611274834145 98121642632170208456125609)
    ·
      refine ⟨73591231974127656342094207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98121642632170208456125609 73591231974127656342094207)
      ·
        refine ⟨110386847961191484513141311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73591231974127656342094207 110386847961191484513141311)
        ·
          refine ⟨165580271941787226769711967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110386847961191484513141311 165580271941787226769711967)
          ·
            refine ⟨248370407912680840154567951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165580271941787226769711967 248370407912680840154567951)
            ·
              refine ⟨372555611869021260231851927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248370407912680840154567951 372555611869021260231851927)
              ·
                refine ⟨558833417803531890347777891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372555611869021260231851927 558833417803531890347777891)
                ·
                  refine ⟨838250126705297835521666837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558833417803531890347777891 838250126705297835521666837)
                  ·
                    refine ⟨39292974689310836040078133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 838250126705297835521666837 39292974689310836040078133)
                    ·
                      refine ⟨3683716377122890878757325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39292974689310836040078133 3683716377122890878757325)
                      ·
                        rfl

theorem cell23_7174012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_7174012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174012 prefixEnd_7174012 := by exact prefixLift 7174012
  have htrace : WordTrace (prefixWord ++ tailWord_7174012) baseStart_7174012 baseEnd_7174012 := by
    simpa [prefixWord, tailWord_7174012, baseEnd_7174012] using wordTrace_append hprefix tailTrace_7174012
  have hstable : (prefixWord ++ tailWord_7174012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174012).length < 2 ^ (prefixWord ++ tailWord_7174012).sum := by decide
  have hdescent : baseEnd_7174012 < baseStart_7174012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174023 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 6]
def baseStart_7174023 : Nat := 118140960795 + 7174023 * 2 ^ 59
def prefixEnd_7174023 : Nat := 4983230072969 + 3 ^ 40 * 7174023 * 2
def baseEnd_7174023 : Nat := 409302447267787815079975

theorem tailTrace_7174023 : CollatzResearch.WordTrace tailWord_7174023 prefixEnd_7174023 409302447267787815079975 := by
  unfold tailWord_7174023
  simp only [CollatzResearch.WordTrace]
  refine ⟨261658114888747371428318723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174438743259164914285545815 261658114888747371428318723)
  ·
    refine ⟨392487172333121057142478085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261658114888747371428318723 392487172333121057142478085)
    ·
      refine ⟨73591344812460198214214641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392487172333121057142478085 73591344812460198214214641)
      ·
        refine ⟨55193508609345148660660981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73591344812460198214214641 55193508609345148660660981)
        ·
          refine ⟨5174391432126107686936967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55193508609345148660660981 5174391432126107686936967)
          ·
            refine ⟨7761587148189161530405451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174391432126107686936967 7761587148189161530405451)
            ·
              refine ⟨11642380722283742295608177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761587148189161530405451 11642380722283742295608177)
              ·
                refine ⟨8731785541712806721706133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11642380722283742295608177 8731785541712806721706133)
                ·
                  refine ⟨409302447267787815079975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8731785541712806721706133 409302447267787815079975)
                  ·
                    rfl

theorem cell23_7174023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 6].length) (baseStart_7174023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174023 prefixEnd_7174023 := by exact prefixLift 7174023
  have htrace : WordTrace (prefixWord ++ tailWord_7174023) baseStart_7174023 baseEnd_7174023 := by
    simpa [prefixWord, tailWord_7174023, baseEnd_7174023] using wordTrace_append hprefix tailTrace_7174023
  have hstable : (prefixWord ++ tailWord_7174023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174023).length < 2 ^ (prefixWord ++ tailWord_7174023).sum := by decide
  have hdescent : baseEnd_7174023 < baseStart_7174023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_7174032 : Nat := 118140960795 + 7174032 * 2 ^ 59
def prefixEnd_7174032 : Nat := 4983230072969 + 3 ^ 40 * 7174032 * 2
def baseEnd_7174032 : Nat := 1227908882245326933502411

theorem tailTrace_7174032 : CollatzResearch.WordTrace tailWord_7174032 prefixEnd_7174032 1227908882245326933502411 := by
  unfold tailWord_7174032
  simp only [CollatzResearch.WordTrace]
  refine ⟨130829221572857382982698175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174438962097143177310264233 130829221572857382982698175)
  ·
    refine ⟨196243832359286074474047263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130829221572857382982698175 196243832359286074474047263)
    ·
      refine ⟨294365748538929111711070895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196243832359286074474047263 294365748538929111711070895)
      ·
        refine ⟨441548622808393667566606343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294365748538929111711070895 441548622808393667566606343)
        ·
          refine ⟨662322934212590501349909515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441548622808393667566606343 662322934212590501349909515)
          ·
            refine ⟨993484401318885752024864273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662322934212590501349909515 993484401318885752024864273)
            ·
              refine ⟨745113300989164314018648205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993484401318885752024864273 745113300989164314018648205)
              ·
                refine ⟨279417487870936617756993077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745113300989164314018648205 279417487870936617756993077)
                ·
                  refine ⟨26195389487900307914718101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279417487870936617756993077 26195389487900307914718101)
                  ·
                    refine ⟨1227908882245326933502411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26195389487900307914718101 1227908882245326933502411)
                    ·
                      rfl

theorem cell23_7174032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_7174032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174032 prefixEnd_7174032 := by exact prefixLift 7174032
  have htrace : WordTrace (prefixWord ++ tailWord_7174032) baseStart_7174032 baseEnd_7174032 := by
    simpa [prefixWord, tailWord_7174032, baseEnd_7174032] using wordTrace_append hprefix tailTrace_7174032
  have hstable : (prefixWord ++ tailWord_7174032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174032).length < 2 ^ (prefixWord ++ tailWord_7174032).sum := by decide
  have hdescent : baseEnd_7174032 < baseStart_7174032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174033 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_7174033 : Nat := 118140960795 + 7174033 * 2 ^ 59
def prefixEnd_7174033 : Nat := 4983230072969 + 3 ^ 40 * 7174033 * 2
def baseEnd_7174033 : Nat := 3683727160216635296594729

theorem tailTrace_7174033 : CollatzResearch.WordTrace tailWord_7174033 prefixEnd_7174033 3683727160216635296594729 := by
  unfold tailWord_7174033
  simp only [CollatzResearch.WordTrace]
  refine ⟨261658479618711143136182753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174438986412474095424121835 261658479618711143136182753)
  ·
    refine ⟨196243859714033357352137065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261658479618711143136182753 196243859714033357352137065)
    ·
      refine ⟨147182894785525018014102799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196243859714033357352137065 147182894785525018014102799)
      ·
        refine ⟨220774342178287527021154199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147182894785525018014102799 220774342178287527021154199)
        ·
          refine ⟨331161513267431290531731299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220774342178287527021154199 331161513267431290531731299)
          ·
            refine ⟨496742269901146935797596949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331161513267431290531731299 496742269901146935797596949)
            ·
              refine ⟨23284793901616262615512357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496742269901146935797596949 23284793901616262615512357)
              ·
                refine ⟨4365898856553049240408567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23284793901616262615512357 4365898856553049240408567)
                ·
                  refine ⟨6548848284829573860612851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365898856553049240408567 6548848284829573860612851)
                  ·
                    refine ⟨9823272427244360790919277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548848284829573860612851 9823272427244360790919277)
                    ·
                      refine ⟨3683727160216635296594729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823272427244360790919277 3683727160216635296594729)
                      ·
                        rfl

theorem cell23_7174033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_7174033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174033 prefixEnd_7174033 := by exact prefixLift 7174033
  have htrace : WordTrace (prefixWord ++ tailWord_7174033) baseStart_7174033 baseEnd_7174033 := by
    simpa [prefixWord, tailWord_7174033, baseEnd_7174033] using wordTrace_append hprefix tailTrace_7174033
  have hstable : (prefixWord ++ tailWord_7174033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174033).length < 2 ^ (prefixWord ++ tailWord_7174033).sum := by decide
  have hdescent : baseEnd_7174033 < baseStart_7174033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174089 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_7174089 : Nat := 118140960795 + 7174089 * 2 ^ 59
def prefixEnd_7174089 : Nat := 4983230072969 + 3 ^ 40 * 7174089 * 2
def baseEnd_7174089 : Nat := 3683755915133287077494471

theorem tailTrace_7174089 : CollatzResearch.WordTrace tailWord_7174089 prefixEnd_7174089 3683755915133287077494471 := by
  unfold tailWord_7174089
  simp only [CollatzResearch.WordTrace]
  refine ⟨261660522106508264700221321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174440348071005509800147547 261660522106508264700221321)
  ·
    refine ⟨196245391579881198525165991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261660522106508264700221321 196245391579881198525165991)
    ·
      refine ⟨294368087369821797787748987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196245391579881198525165991 294368087369821797787748987)
      ·
        refine ⟨441552131054732696681623481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294368087369821797787748987 441552131054732696681623481)
        ·
          refine ⟨331164098291049522511217611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441552131054732696681623481 331164098291049522511217611)
          ·
            refine ⟨496746147436574283766826417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331164098291049522511217611 496746147436574283766826417)
            ·
              refine ⟨372559610577430712825119813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496746147436574283766826417 372559610577430712825119813)
              ·
                refine ⟨69854926983268258654709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372559610577430712825119813 69854926983268258654709965)
                ·
                  refine ⟨26195597618725596995516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69854926983268258654709965 26195597618725596995516237)
                  ·
                    refine ⟨9823349107022098873318589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26195597618725596995516237 9823349107022098873318589)
                    ·
                      refine ⟨3683755915133287077494471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823349107022098873318589 3683755915133287077494471)
                      ·
                        rfl

theorem cell23_7174089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_7174089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174089 prefixEnd_7174089 := by exact prefixLift 7174089
  have htrace : WordTrace (prefixWord ++ tailWord_7174089) baseStart_7174089 baseEnd_7174089 := by
    simpa [prefixWord, tailWord_7174089, baseEnd_7174089] using wordTrace_append hprefix tailTrace_7174089
  have hstable : (prefixWord ++ tailWord_7174089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174089).length < 2 ^ (prefixWord ++ tailWord_7174089).sum := by decide
  have hdescent : baseEnd_7174089 < baseStart_7174089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174090 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_7174090 : Nat := 118140960795 + 7174090 * 2 ^ 59
def prefixEnd_7174090 : Nat := 4983230072969 + 3 ^ 40 * 7174090 * 2
def baseEnd_7174090 : Nat := 3683756428613941573581967

theorem tailTrace_7174090 : CollatzResearch.WordTrace tailWord_7174090 prefixEnd_7174090 3683756428613941573581967 := by
  unfold tailWord_7174090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65415139644876160467751931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174440372386336427914005149 65415139644876160467751931)
  ·
    refine ⟨98122709467314240701627897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65415139644876160467751931 98122709467314240701627897)
    ·
      refine ⟨73592032100485680526220923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98122709467314240701627897 73592032100485680526220923)
      ·
        refine ⟨110388048150728520789331385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73592032100485680526220923 110388048150728520789331385)
        ·
          refine ⟨82791036113046390591998539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110388048150728520789331385 82791036113046390591998539)
          ·
            refine ⟨124186554169569585887997809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82791036113046390591998539 124186554169569585887997809)
            ·
              refine ⟨93139915627177189415998357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124186554169569585887997809 93139915627177189415998357)
              ·
                refine ⟨4365933545023930753874923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93139915627177189415998357 4365933545023930753874923)
                ·
                  refine ⟨6548900317535896130812385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365933545023930753874923 6548900317535896130812385)
                  ·
                    refine ⟨4911675238151922098109289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548900317535896130812385 4911675238151922098109289)
                    ·
                      refine ⟨3683756428613941573581967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911675238151922098109289 3683756428613941573581967)
                      ·
                        rfl

theorem cell23_7174090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_7174090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174090 prefixEnd_7174090 := by exact prefixLift 7174090
  have htrace : WordTrace (prefixWord ++ tailWord_7174090) baseStart_7174090 baseEnd_7174090 := by
    simpa [prefixWord, tailWord_7174090, baseEnd_7174090] using wordTrace_append hprefix tailTrace_7174090
  have hstable : (prefixWord ++ tailWord_7174090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174090).length < 2 ^ (prefixWord ++ tailWord_7174090).sum := by decide
  have hdescent : baseEnd_7174090 < baseStart_7174090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174237 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 5]
def baseStart_7174237 : Nat := 118140960795 + 7174237 * 2 ^ 59
def prefixEnd_7174237 : Nat := 4983230072969 + 3 ^ 40 * 7174237 * 2
def baseEnd_7174237 : Nat := 409314656696683610938199

theorem tailTrace_7174237 : CollatzResearch.WordTrace tailWord_7174237 prefixEnd_7174237 409314656696683610938199 := by
  unfold tailWord_7174237
  simp only [CollatzResearch.WordTrace]
  refine ⟨261665920109972085976608965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174443946739981390651072643 261665920109972085976608965)
  ·
    refine ⟨49062360020619766120614181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261665920109972085976608965 49062360020619766120614181)
    ·
      refine ⟨9199192503866206147615159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49062360020619766120614181 9199192503866206147615159)
      ·
        refine ⟨13798788755799309221422739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199192503866206147615159 13798788755799309221422739)
        ·
          refine ⟨20698183133698963832134109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13798788755799309221422739 20698183133698963832134109)
          ·
            refine ⟨7761818675137111437050291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20698183133698963832134109 7761818675137111437050291)
            ·
              refine ⟨11642728012705667155575437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761818675137111437050291 11642728012705667155575437)
              ·
                refine ⟨4366023004764625183340789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642728012705667155575437 4366023004764625183340789)
                ·
                  refine ⟨409314656696683610938199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366023004764625183340789 409314656696683610938199)
                  ·
                    rfl

theorem cell23_7174237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_7174237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174237 prefixEnd_7174237 := by exact prefixLift 7174237
  have htrace : WordTrace (prefixWord ++ tailWord_7174237) baseStart_7174237 baseEnd_7174237 := by
    simpa [prefixWord, tailWord_7174237, baseEnd_7174237] using wordTrace_append hprefix tailTrace_7174237
  have hstable : (prefixWord ++ tailWord_7174237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174237).length < 2 ^ (prefixWord ++ tailWord_7174237).sum := by decide
  have hdescent : baseEnd_7174237 < baseStart_7174237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174253 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7174253 : Nat := 118140960795 + 7174253 * 2 ^ 59
def prefixEnd_7174253 : Nat := 4983230072969 + 3 ^ 40 * 7174253 * 2
def baseEnd_7174253 : Nat := 3683840125960624435843717

theorem tailTrace_7174253 : CollatzResearch.WordTrace tailWord_7174253 prefixEnd_7174253 3683840125960624435843717 := by
  unfold tailWord_7174253
  simp only [CollatzResearch.WordTrace]
  refine ⟨261666503677914120709191413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174444335785276080472794275 261666503677914120709191413)
  ·
    refine ⟨24531234719804448816486695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261666503677914120709191413 24531234719804448816486695)
    ·
      refine ⟨36796852079706673224730043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531234719804448816486695 36796852079706673224730043)
      ·
        refine ⟨55195278119560009837095065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36796852079706673224730043 55195278119560009837095065)
        ·
          refine ⟨41396458589670007377821299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55195278119560009837095065 41396458589670007377821299)
          ·
            refine ⟨62094687884505011066731949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41396458589670007377821299 62094687884505011066731949)
            ·
              refine ⟨23285507956689379150024481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62094687884505011066731949 23285507956689379150024481)
              ·
                refine ⟨17464130967517034362518361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23285507956689379150024481 17464130967517034362518361)
                ·
                  refine ⟨13098098225637775771888771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17464130967517034362518361 13098098225637775771888771)
                  ·
                    refine ⟨19647147338456663657833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13098098225637775771888771 19647147338456663657833157)
                    ·
                      refine ⟨3683840125960624435843717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19647147338456663657833157 3683840125960624435843717)
                      ·
                        rfl

theorem cell23_7174253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7174253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174253 prefixEnd_7174253 := by exact prefixLift 7174253
  have htrace : WordTrace (prefixWord ++ tailWord_7174253) baseStart_7174253 baseEnd_7174253 := by
    simpa [prefixWord, tailWord_7174253, baseEnd_7174253] using wordTrace_append hprefix tailTrace_7174253
  have hstable : (prefixWord ++ tailWord_7174253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174253).length < 2 ^ (prefixWord ++ tailWord_7174253).sum := by decide
  have hdescent : baseEnd_7174253 < baseStart_7174253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174263 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 3, 4]
def baseStart_7174263 : Nat := 118140960795 + 7174263 * 2 ^ 59
def prefixEnd_7174263 : Nat := 4983230072969 + 3 ^ 40 * 7174263 * 2
def baseEnd_7174263 : Nat := 1227948420255723132239557

theorem tailTrace_7174263 : CollatzResearch.WordTrace tailWord_7174263 prefixEnd_7174263 1227948420255723132239557 := by
  unfold tailWord_7174263
  simp only [CollatzResearch.WordTrace]
  refine ⟨261666868407877892417055443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174444578938585261611370295 261666868407877892417055443)
  ·
    refine ⟨392500302611816838625583165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261666868407877892417055443 392500302611816838625583165)
    ·
      refine ⟨147187613479431314484593687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392500302611816838625583165 147187613479431314484593687)
      ·
        refine ⟨220781420219146971726890531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147187613479431314484593687 220781420219146971726890531)
        ·
          refine ⟨331172130328720457590335797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220781420219146971726890531 331172130328720457590335797)
          ·
            refine ⟨31047387218317542899093981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331172130328720457590335797 31047387218317542899093981)
            ·
              refine ⟨11642770206869078587160243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31047387218317542899093981 11642770206869078587160243)
              ·
                refine ⟨17464155310303617880740365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642770206869078587160243 17464155310303617880740365)
                ·
                  refine ⟨6549058241363856705277637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17464155310303617880740365 6549058241363856705277637)
                  ·
                    refine ⟨1227948420255723132239557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549058241363856705277637 1227948420255723132239557)
                    ·
                      rfl

theorem cell23_7174263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_7174263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174263 prefixEnd_7174263 := by exact prefixLift 7174263
  have htrace : WordTrace (prefixWord ++ tailWord_7174263) baseStart_7174263 baseEnd_7174263 := by
    simpa [prefixWord, tailWord_7174263, baseEnd_7174263] using wordTrace_append hprefix tailTrace_7174263
  have hstable : (prefixWord ++ tailWord_7174263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174263).length < 2 ^ (prefixWord ++ tailWord_7174263).sum := by decide
  have hdescent : baseEnd_7174263 < baseStart_7174263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174290 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7174290 : Nat := 118140960795 + 7174290 * 2 ^ 59
def prefixEnd_7174290 : Nat := 4983230072969 + 3 ^ 40 * 7174290 * 2
def baseEnd_7174290 : Nat := 3683859124744840791081047

theorem tailTrace_7174290 : CollatzResearch.WordTrace tailWord_7174290 prefixEnd_7174290 3683859124744840791081047 := by
  unfold tailWord_7174290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65416963294695019007072081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174445235452520050685525549 65416963294695019007072081)
  ·
    refine ⟨49062722471021264255304061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65416963294695019007072081 49062722471021264255304061)
    ·
      refine ⟨18398520926632974095739023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49062722471021264255304061 18398520926632974095739023)
      ·
        refine ⟨27597781389949461143608535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18398520926632974095739023 27597781389949461143608535)
        ·
          refine ⟨41396672084924191715412803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27597781389949461143608535 41396672084924191715412803)
          ·
            refine ⟨62095008127386287573119205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41396672084924191715412803 62095008127386287573119205)
            ·
              refine ⟨11642814023884928919959851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62095008127386287573119205 11642814023884928919959851)
              ·
                refine ⟨17464221035827393379939777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642814023884928919959851 17464221035827393379939777)
                ·
                  refine ⟨13098165776870545034954833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17464221035827393379939777 13098165776870545034954833)
                  ·
                    refine ⟨9823624332652908776216125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13098165776870545034954833 9823624332652908776216125)
                    ·
                      refine ⟨3683859124744840791081047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823624332652908776216125 3683859124744840791081047)
                      ·
                        rfl

theorem cell23_7174290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7174290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174290 prefixEnd_7174290 := by exact prefixLift 7174290
  have htrace : WordTrace (prefixWord ++ tailWord_7174290) baseStart_7174290 baseEnd_7174290 := by
    simpa [prefixWord, tailWord_7174290, baseEnd_7174290] using wordTrace_append hprefix tailTrace_7174290
  have hstable : (prefixWord ++ tailWord_7174290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174290).length < 2 ^ (prefixWord ++ tailWord_7174290).sum := by decide
  have hdescent : baseEnd_7174290 < baseStart_7174290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174314 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7174314 : Nat := 118140960795 + 7174314 * 2 ^ 59
def prefixEnd_7174314 : Nat := 4983230072969 + 3 ^ 40 * 7174314 * 2
def baseEnd_7174314 : Nat := 1227957149426849565726979

theorem tailTrace_7174314 : CollatzResearch.WordTrace tailWord_7174314 prefixEnd_7174314 1227957149426849565726979 := by
  unfold tailWord_7174314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65417182132673282031790499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174445819020462085418107997 65417182132673282031790499)
  ·
    refine ⟨98125773199009923047685749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65417182132673282031790499 98125773199009923047685749)
    ·
      refine ⟨9199291237407180285720539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98125773199009923047685749 9199291237407180285720539)
      ·
        refine ⟨13798936856110770428580809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199291237407180285720539 13798936856110770428580809)
        ·
          refine ⟨10349202642083077821435607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13798936856110770428580809 10349202642083077821435607)
          ·
            refine ⟨15523803963124616732153411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349202642083077821435607 15523803963124616732153411)
            ·
              refine ⟨23285705944686925098230117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523803963124616732153411 23285705944686925098230117)
              ·
                refine ⟨4366069864628798455918147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23285705944686925098230117 4366069864628798455918147)
                ·
                  refine ⟨6549104796943197683877221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366069864628798455918147 6549104796943197683877221)
                  ·
                    refine ⟨1227957149426849565726979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549104796943197683877221 1227957149426849565726979)
                    ·
                      rfl

theorem cell23_7174314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7174314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174314 prefixEnd_7174314 := by exact prefixLift 7174314
  have htrace : WordTrace (prefixWord ++ tailWord_7174314) baseStart_7174314 baseEnd_7174314 := by
    simpa [prefixWord, tailWord_7174314, baseEnd_7174314] using wordTrace_append hprefix tailTrace_7174314
  have hstable : (prefixWord ++ tailWord_7174314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174314).length < 2 ^ (prefixWord ++ tailWord_7174314).sum := by decide
  have hdescent : baseEnd_7174314 < baseStart_7174314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174354 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7174354 : Nat := 118140960795 + 7174354 * 2 ^ 59
def prefixEnd_7174354 : Nat := 4983230072969 + 3 ^ 40 * 7174354 * 2
def baseEnd_7174354 : Nat := 3683891987506728540680753

theorem tailTrace_7174354 : CollatzResearch.WordTrace tailWord_7174354 prefixEnd_7174354 3683891987506728540680753 := by
  unfold tailWord_7174354
  simp only [CollatzResearch.WordTrace]
  refine ⟨65417546862637053739654529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174446791633698809972412077 65417546862637053739654529)
  ·
    refine ⟨49063160146977790304740897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65417546862637053739654529 49063160146977790304740897)
    ·
      refine ⟨36797370110233342728555673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49063160146977790304740897 36797370110233342728555673)
      ·
        refine ⟨27598027582675007046416755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36797370110233342728555673 27598027582675007046416755)
        ·
          refine ⟨41397041374012510569625133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27598027582675007046416755 41397041374012510569625133)
          ·
            refine ⟨15523890515254691463609425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41397041374012510569625133 15523890515254691463609425)
            ·
              refine ⟨11642917886441018597707069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15523890515254691463609425 11642917886441018597707069)
              ·
                refine ⟨4366094207415381974140151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642917886441018597707069 4366094207415381974140151)
                ·
                  refine ⟨6549141311123072961210227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366094207415381974140151 6549141311123072961210227)
                  ·
                    refine ⟨9823711966684609441815341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549141311123072961210227 9823711966684609441815341)
                    ·
                      refine ⟨3683891987506728540680753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823711966684609441815341 3683891987506728540680753)
                      ·
                        rfl

theorem cell23_7174354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7174354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174354 prefixEnd_7174354 := by exact prefixLift 7174354
  have htrace : WordTrace (prefixWord ++ tailWord_7174354) baseStart_7174354 baseEnd_7174354 := by
    simpa [prefixWord, tailWord_7174354, baseEnd_7174354] using wordTrace_append hprefix tailTrace_7174354
  have hstable : (prefixWord ++ tailWord_7174354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174354).length < 2 ^ (prefixWord ++ tailWord_7174354).sum := by decide
  have hdescent : baseEnd_7174354 < baseStart_7174354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174360 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_7174360 : Nat := 118140960795 + 7174360 * 2 ^ 59
def prefixEnd_7174360 : Nat := 4983230072969 + 3 ^ 40 * 7174360 * 2
def baseEnd_7174360 : Nat := 3683895068390655517205725

theorem tailTrace_7174360 : CollatzResearch.WordTrace tailWord_7174360 prefixEnd_7174360 3683895068390655517205725 := by
  unfold tailWord_7174360
  simp only [CollatzResearch.WordTrace]
  refine ⟨130835203144263238991668267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174446937525684318655557689 130835203144263238991668267)
  ·
    refine ⟨196252804716394858487502401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130835203144263238991668267 196252804716394858487502401)
    ·
      refine ⟨147189603537296143865626801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196252804716394858487502401 147189603537296143865626801)
      ·
        refine ⟨110392202652972107899220101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147189603537296143865626801 110392202652972107899220101)
        ·
          refine ⟨20698537997432270231103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110392202652972107899220101 20698537997432270231103769)
          ·
            refine ⟨15523903498074202673327827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20698537997432270231103769 15523903498074202673327827)
            ·
              refine ⟨23285855247111304009991741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523903498074202673327827 23285855247111304009991741)
              ·
                refine ⟨8732195717666739003746903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23285855247111304009991741 8732195717666739003746903)
                ·
                  refine ⟨13098293576500108505620355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8732195717666739003746903 13098293576500108505620355)
                  ·
                    refine ⟨19647440364750162758430533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13098293576500108505620355 19647440364750162758430533)
                    ·
                      refine ⟨3683895068390655517205725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19647440364750162758430533 3683895068390655517205725)
                      ·
                        rfl

theorem cell23_7174360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_7174360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174360 prefixEnd_7174360 := by exact prefixLift 7174360
  have htrace : WordTrace (prefixWord ++ tailWord_7174360) baseStart_7174360 baseEnd_7174360 := by
    simpa [prefixWord, tailWord_7174360, baseEnd_7174360] using wordTrace_append hprefix tailTrace_7174360
  have hstable : (prefixWord ++ tailWord_7174360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174360).length < 2 ^ (prefixWord ++ tailWord_7174360).sum := by decide
  have hdescent : baseEnd_7174360 < baseStart_7174360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174390 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7174390 : Nat := 118140960795 + 7174390 * 2 ^ 59
def prefixEnd_7174390 : Nat := 4983230072969 + 3 ^ 40 * 7174390 * 2
def baseEnd_7174390 : Nat := 3683910472810290399830587

theorem tailTrace_7174390 : CollatzResearch.WordTrace tailWord_7174390 prefixEnd_7174390 3683910472810290399830587 := by
  unfold tailWord_7174390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354468779901112069183039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174447666985611862071285749 16354468779901112069183039)
  ·
    refine ⟨24531703169851668103774559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16354468779901112069183039 24531703169851668103774559)
    ·
      refine ⟨36797554754777502155661839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531703169851668103774559 36797554754777502155661839)
      ·
        refine ⟨55196332132166253233492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797554754777502155661839 55196332132166253233492759)
        ·
          refine ⟨82794498198249379850239139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55196332132166253233492759 82794498198249379850239139)
          ·
            refine ⟨124191747297374069775358709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82794498198249379850239139 124191747297374069775358709)
            ·
              refine ⟨11642976309128819041439879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124191747297374069775358709 11642976309128819041439879)
              ·
                refine ⟨17464464463693228562159819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642976309128819041439879 17464464463693228562159819)
                ·
                  refine ⟨26196696695539842843239729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17464464463693228562159819 26196696695539842843239729)
                  ·
                    refine ⟨19647522521654882132429797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26196696695539842843239729 19647522521654882132429797)
                    ·
                      refine ⟨3683910472810290399830587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19647522521654882132429797 3683910472810290399830587)
                      ·
                        rfl

theorem cell23_7174390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7174390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174390 prefixEnd_7174390 := by exact prefixLift 7174390
  have htrace : WordTrace (prefixWord ++ tailWord_7174390) baseStart_7174390 baseEnd_7174390 := by
    simpa [prefixWord, tailWord_7174390, baseEnd_7174390] using wordTrace_append hprefix tailTrace_7174390
  have hstable : (prefixWord ++ tailWord_7174390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174390).length < 2 ^ (prefixWord ++ tailWord_7174390).sum := by decide
  have hdescent : baseEnd_7174390 < baseStart_7174390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174393 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_7174393 : Nat := 118140960795 + 7174393 * 2 ^ 59
def prefixEnd_7174393 : Nat := 4983230072969 + 3 ^ 40 * 7174393 * 2
def baseEnd_7174393 : Nat := 3683912013252253888093073

theorem tailTrace_7174393 : CollatzResearch.WordTrace tailWord_7174393 prefixEnd_7174393 3683912013252253888093073 := by
  unfold tailWord_7174393
  simp only [CollatzResearch.WordTrace]
  refine ⟨261671609897406924619287833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174447739931604616412858555 261671609897406924619287833)
  ·
    refine ⟨196253707423055193464465875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261671609897406924619287833 196253707423055193464465875)
    ·
      refine ⟨294380561134582790196698813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196253707423055193464465875 294380561134582790196698813)
      ·
        refine ⟨110392710425468546323762055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294380561134582790196698813 110392710425468546323762055)
        ·
          refine ⟨165589065638202819485643083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110392710425468546323762055 165589065638202819485643083)
          ·
            refine ⟨248383598457304229228464625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165589065638202819485643083 248383598457304229228464625)
            ·
              refine ⟨186287698842978171921348469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248383598457304229228464625 186287698842978171921348469)
              ·
                refine ⟨17464471766529203617626419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186287698842978171921348469 17464471766529203617626419)
                ·
                  refine ⟨26196707649793805426439629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17464471766529203617626419 26196707649793805426439629)
                  ·
                    refine ⟨9823765368672677034914861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26196707649793805426439629 9823765368672677034914861)
                    ·
                      refine ⟨3683912013252253888093073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823765368672677034914861 3683912013252253888093073)
                      ·
                        rfl

theorem cell23_7174393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_7174393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174393 prefixEnd_7174393 := by exact prefixLift 7174393
  have htrace : WordTrace (prefixWord ++ tailWord_7174393) baseStart_7174393 baseEnd_7174393 := by
    simpa [prefixWord, tailWord_7174393, baseEnd_7174393] using wordTrace_append hprefix tailTrace_7174393
  have hstable : (prefixWord ++ tailWord_7174393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174393).length < 2 ^ (prefixWord ++ tailWord_7174393).sum := by decide
  have hdescent : baseEnd_7174393 < baseStart_7174393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174410 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7174410 : Nat := 118140960795 + 7174410 * 2 ^ 59
def prefixEnd_7174410 : Nat := 4983230072969 + 3 ^ 40 * 7174410 * 2
def baseEnd_7174410 : Nat := 3683920742423380321580495

theorem tailTrace_7174410 : CollatzResearch.WordTrace tailWord_7174410 prefixEnd_7174410 3683920742423380321580495 := by
  unfold tailWord_7174410
  simp only [CollatzResearch.WordTrace]
  refine ⟨65418057484586334130664171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174448153292230224348437789 65418057484586334130664171)
  ·
    refine ⟨98127086226879501195996257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65418057484586334130664171 98127086226879501195996257)
    ·
      refine ⟨73595314670159625896997193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98127086226879501195996257 73595314670159625896997193)
      ·
        refine ⟨55196486002619719422747895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73595314670159625896997193 55196486002619719422747895)
        ·
          refine ⟨82794729003929579134121843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55196486002619719422747895 82794729003929579134121843)
          ·
            refine ⟨124192093505894368701182765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82794729003929579134121843 124192093505894368701182765)
            ·
              refine ⟨46572035064710388262943537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124192093505894368701182765 46572035064710388262943537)
              ·
                refine ⟨34929026298532791197207653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46572035064710388262943537 34929026298532791197207653)
                ·
                  refine ⟨6549192430974898349476435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34929026298532791197207653 6549192430974898349476435)
                  ·
                    refine ⟨9823788646462347524214653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549192430974898349476435 9823788646462347524214653)
                    ·
                      refine ⟨3683920742423380321580495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823788646462347524214653 3683920742423380321580495)
                      ·
                        rfl

theorem cell23_7174410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7174410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174410 prefixEnd_7174410 := by exact prefixLift 7174410
  have htrace : WordTrace (prefixWord ++ tailWord_7174410) baseStart_7174410 baseEnd_7174410 := by
    simpa [prefixWord, tailWord_7174410, baseEnd_7174410] using wordTrace_append hprefix tailTrace_7174410
  have hstable : (prefixWord ++ tailWord_7174410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174410).length < 2 ^ (prefixWord ++ tailWord_7174410).sum := by decide
  have hdescent : baseEnd_7174410 < baseStart_7174410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174453 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7174453 : Nat := 118140960795 + 7174453 * 2 ^ 59
def prefixEnd_7174453 : Nat := 4983230072969 + 3 ^ 40 * 7174453 * 2
def baseEnd_7174453 : Nat := 3683942822091523653342797

theorem tailTrace_7174453 : CollatzResearch.WordTrace tailWord_7174453 prefixEnd_7174453 3683942822091523653342797 := by
  unfold tailWord_7174453
  simp only [CollatzResearch.WordTrace]
  refine ⟨261673798277189554866472013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174449198851459703244314675 261673798277189554866472013)
  ·
    refine ⟨98127674353946083074927005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261673798277189554866472013 98127674353946083074927005)
    ·
      refine ⟨36797877882729781153097627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98127674353946083074927005 36797877882729781153097627)
      ·
        refine ⟨55196816824094671729646441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797877882729781153097627 55196816824094671729646441)
        ·
          refine ⟨41397612618071003797234831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55196816824094671729646441 41397612618071003797234831)
          ·
            refine ⟨62096418927106505695852247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41397612618071003797234831 62096418927106505695852247)
            ·
              refine ⟨93144628390659758543778371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62096418927106505695852247 93144628390659758543778371)
              ·
                refine ⟨139716942585989637815667557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93144628390659758543778371 139716942585989637815667557)
                ·
                  refine ⟨26196926734873057090437667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139716942585989637815667557 26196926734873057090437667)
                  ·
                    refine ⟨39295390102309585635656501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26196926734873057090437667 39295390102309585635656501)
                    ·
                      refine ⟨3683942822091523653342797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39295390102309585635656501 3683942822091523653342797)
                      ·
                        rfl

theorem cell23_7174453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7174453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174453 prefixEnd_7174453 := by exact prefixLift 7174453
  have htrace : WordTrace (prefixWord ++ tailWord_7174453) baseStart_7174453 baseEnd_7174453 := by
    simpa [prefixWord, tailWord_7174453, baseEnd_7174453] using wordTrace_append hprefix tailTrace_7174453
  have hstable : (prefixWord ++ tailWord_7174453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174453).length < 2 ^ (prefixWord ++ tailWord_7174453).sum := by decide
  have hdescent : baseEnd_7174453 < baseStart_7174453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174484 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_7174484 : Nat := 118140960795 + 7174484 * 2 ^ 59
def prefixEnd_7174484 : Nat := 4983230072969 + 3 ^ 40 * 7174484 * 2
def baseEnd_7174484 : Nat := 3683958739991813032055155

theorem tailTrace_7174484 : CollatzResearch.WordTrace tailWord_7174484 prefixEnd_7174484 3683958739991813032055155 := by
  unfold tailWord_7174484
  simp only [CollatzResearch.WordTrace]
  refine ⟨130837464470038623580425253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174449952626718164773900337 130837464470038623580425253)
  ·
    refine ⟨24532024588132241921329735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130837464470038623580425253 24532024588132241921329735)
    ·
      refine ⟨36798036882198362881994603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24532024588132241921329735 36798036882198362881994603)
      ·
        refine ⟨55197055323297544322991905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36798036882198362881994603 55197055323297544322991905)
        ·
          refine ⟨41397791492473158242243929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55197055323297544322991905 41397791492473158242243929)
          ·
            refine ⟨31048343619354868681682947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41397791492473158242243929 31048343619354868681682947)
            ·
              refine ⟨46572515429032303022524421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31048343619354868681682947 46572515429032303022524421)
              ·
                refine ⟨8732346642943556816723329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46572515429032303022524421 8732346642943556816723329)
                ·
                  refine ⟨6549259982207667612542497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732346642943556816723329 6549259982207667612542497)
                  ·
                    refine ⟨4911944986655750709406873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549259982207667612542497 4911944986655750709406873)
                    ·
                      refine ⟨3683958739991813032055155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4911944986655750709406873 3683958739991813032055155)
                      ·
                        rfl

theorem cell23_7174484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_7174484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174484 prefixEnd_7174484 := by exact prefixLift 7174484
  have htrace : WordTrace (prefixWord ++ tailWord_7174484) baseStart_7174484 baseEnd_7174484 := by
    simpa [prefixWord, tailWord_7174484, baseEnd_7174484] using wordTrace_append hprefix tailTrace_7174484
  have hstable : (prefixWord ++ tailWord_7174484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174484).length < 2 ^ (prefixWord ++ tailWord_7174484).sum := by decide
  have hdescent : baseEnd_7174484 < baseStart_7174484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174500 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_7174500 : Nat := 118140960795 + 7174500 * 2 ^ 59
def prefixEnd_7174500 : Nat := 4983230072969 + 3 ^ 40 * 7174500 * 2
def baseEnd_7174500 : Nat := 3683966955682284969455081

theorem tailTrace_7174500 : CollatzResearch.WordTrace tailWord_7174500 prefixEnd_7174500 3683966955682284969455081 := by
  unfold tailWord_7174500
  simp only [CollatzResearch.WordTrace]
  refine ⟨130837756254009640946716477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174450341672012854595621969 130837756254009640946716477)
  ·
    refine ⟨49064158595253615355018679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130837756254009640946716477 49064158595253615355018679)
    ·
      refine ⟨73596237892880423032528019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49064158595253615355018679 73596237892880423032528019)
      ·
        refine ⟨110394356839320634548792029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73596237892880423032528019 110394356839320634548792029)
        ·
          refine ⟨41397883814745237955797011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110394356839320634548792029 41397883814745237955797011)
          ·
            refine ⟨62096825722117856933695517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41397883814745237955797011 62096825722117856933695517)
            ·
              refine ⟨23286309645794196350135819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62096825722117856933695517 23286309645794196350135819)
              ·
                refine ⟨34929464468691294525203729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23286309645794196350135819 34929464468691294525203729)
                ·
                  refine ⟨26197098351518470893902797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34929464468691294525203729 26197098351518470893902797)
                  ·
                    refine ⟨9823911881819426585213549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26197098351518470893902797 9823911881819426585213549)
                    ·
                      refine ⟨3683966955682284969455081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823911881819426585213549 3683966955682284969455081)
                      ·
                        rfl

theorem cell23_7174500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_7174500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174500 prefixEnd_7174500 := by exact prefixLift 7174500
  have htrace : WordTrace (prefixWord ++ tailWord_7174500) baseStart_7174500 baseEnd_7174500 := by
    simpa [prefixWord, tailWord_7174500, baseEnd_7174500] using wordTrace_append hprefix tailTrace_7174500
  have hstable : (prefixWord ++ tailWord_7174500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174500).length < 2 ^ (prefixWord ++ tailWord_7174500).sum := by decide
  have hdescent : baseEnd_7174500 < baseStart_7174500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174553 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_7174553 : Nat := 118140960795 + 7174553 * 2 ^ 59
def prefixEnd_7174553 : Nat := 4983230072969 + 3 ^ 40 * 7174553 * 2
def baseEnd_7174553 : Nat := 3683994170156973262092337

theorem tailTrace_7174553 : CollatzResearch.WordTrace tailWord_7174553 prefixEnd_7174553 3683994170156973262092337 := by
  unfold tailWord_7174553
  simp only [CollatzResearch.WordTrace]
  refine ⟨261677445576827271945112313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174451630384551514630074875 261677445576827271945112313)
  ·
    refine ⟨196258084182620453958834235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261677445576827271945112313 196258084182620453958834235)
    ·
      refine ⟨294387126273930680938251353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196258084182620453958834235 294387126273930680938251353)
      ·
        refine ⟨220790344705448010703688515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294387126273930680938251353 220790344705448010703688515)
        ·
          refine ⟨331185517058172016055532773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220790344705448010703688515 331185517058172016055532773)
          ·
            refine ⟨62097284448407253010412395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331185517058172016055532773 62097284448407253010412395)
            ·
              refine ⟨93145926672610879515618593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62097284448407253010412395 93145926672610879515618593)
              ·
                refine ⟨69859445004458159636713945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93145926672610879515618593 69859445004458159636713945)
                ·
                  refine ⟨52394583753343619727535459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69859445004458159636713945 52394583753343619727535459)
                  ·
                    refine ⟨78591875630015429591303189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52394583753343619727535459 78591875630015429591303189)
                    ·
                      refine ⟨3683994170156973262092337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78591875630015429591303189 3683994170156973262092337)
                      ·
                        rfl

theorem cell23_7174553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_7174553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174553 prefixEnd_7174553 := by exact prefixLift 7174553
  have htrace : WordTrace (prefixWord ++ tailWord_7174553) baseStart_7174553 baseEnd_7174553 := by
    simpa [prefixWord, tailWord_7174553, baseEnd_7174553] using wordTrace_append hprefix tailTrace_7174553
  have hstable : (prefixWord ++ tailWord_7174553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174553).length < 2 ^ (prefixWord ++ tailWord_7174553).sum := by decide
  have hdescent : baseEnd_7174553 < baseStart_7174553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174560 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_7174560 : Nat := 118140960795 + 7174560 * 2 ^ 59
def prefixEnd_7174560 : Nat := 4983230072969 + 3 ^ 40 * 7174560 * 2
def baseEnd_7174560 : Nat := 3683997764521554734704805

theorem tailTrace_7174560 : CollatzResearch.WordTrace tailWord_7174560 prefixEnd_7174560 3683997764521554734704805 := by
  unfold tailWord_7174560
  simp only [CollatzResearch.WordTrace]
  refine ⟨130838850443900956070308567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174451800591867941427078089 130838850443900956070308567)
  ·
    refine ⟨196258275665851434105462851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130838850443900956070308567 196258275665851434105462851)
    ·
      refine ⟨294387413498777151158194277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196258275665851434105462851 294387413498777151158194277)
      ·
        refine ⟨55197640031020715842161427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294387413498777151158194277 55197640031020715842161427)
        ·
          refine ⟨82796460046531073763242141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55197640031020715842161427 82796460046531073763242141)
          ·
            refine ⟨31048672517449152661215803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82796460046531073763242141 31048672517449152661215803)
            ·
              refine ⟨46573008776173728991823705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31048672517449152661215803 46573008776173728991823705)
              ·
                refine ⟨34929756582130296743867779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46573008776173728991823705 34929756582130296743867779)
                ·
                  refine ⟨52394634873195445115801669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34929756582130296743867779 52394634873195445115801669)
                  ·
                    refine ⟨9823994038724145959212813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52394634873195445115801669 9823994038724145959212813)
                    ·
                      refine ⟨3683997764521554734704805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9823994038724145959212813 3683997764521554734704805)
                      ·
                        rfl

theorem cell23_7174560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_7174560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174560 prefixEnd_7174560 := by exact prefixLift 7174560
  have htrace : WordTrace (prefixWord ++ tailWord_7174560) baseStart_7174560 baseEnd_7174560 := by
    simpa [prefixWord, tailWord_7174560, baseEnd_7174560] using wordTrace_append hprefix tailTrace_7174560
  have hstable : (prefixWord ++ tailWord_7174560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174560).length < 2 ^ (prefixWord ++ tailWord_7174560).sum := by decide
  have hdescent : baseEnd_7174560 < baseStart_7174560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174567 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 3, 4]
def baseStart_7174567 : Nat := 118140960795 + 7174567 * 2 ^ 59
def prefixEnd_7174567 : Nat := 4983230072969 + 3 ^ 40 * 7174567 * 2
def baseEnd_7174567 : Nat := 1228000452962045402439091

theorem tailTrace_7174567 : CollatzResearch.WordTrace tailWord_7174567 prefixEnd_7174567 1228000452962045402439091 := by
  unfold tailWord_7174567
  simp only [CollatzResearch.WordTrace]
  refine ⟨261677956198776552336121955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174451970799184368224081303 261677956198776552336121955)
  ·
    refine ⟨392516934298164828504182933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261677956198776552336121955 392516934298164828504182933)
    ·
      refine ⟨18399231295226476336133575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 392516934298164828504182933 18399231295226476336133575)
      ·
        refine ⟨27598846942839714504200363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18399231295226476336133575 27598846942839714504200363)
        ·
          refine ⟨41398270414259571756300545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27598846942839714504200363 41398270414259571756300545)
          ·
            refine ⟨31048702810694678817225409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41398270414259571756300545 31048702810694678817225409)
            ·
              refine ⟨23286527108021009112919057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31048702810694678817225409 23286527108021009112919057)
              ·
                refine ⟨17464895331015756834689293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23286527108021009112919057 17464895331015756834689293)
                ·
                  refine ⟨6549335749130908813008485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17464895331015756834689293 6549335749130908813008485)
                  ·
                    refine ⟨1228000452962045402439091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549335749130908813008485 1228000452962045402439091)
                    ·
                      rfl

theorem cell23_7174567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_7174567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174567 prefixEnd_7174567 := by exact prefixLift 7174567
  have htrace : WordTrace (prefixWord ++ tailWord_7174567) baseStart_7174567 baseEnd_7174567 := by
    simpa [prefixWord, tailWord_7174567, baseEnd_7174567] using wordTrace_append hprefix tailTrace_7174567
  have hstable : (prefixWord ++ tailWord_7174567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174567).length < 2 ^ (prefixWord ++ tailWord_7174567).sum := by decide
  have hdescent : baseEnd_7174567 < baseStart_7174567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174603 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_7174603 : Nat := 118140960795 + 7174603 * 2 ^ 59
def prefixEnd_7174603 : Nat := 4983230072969 + 3 ^ 40 * 7174603 * 2
def baseEnd_7174603 : Nat := 3684019844189698066467107

theorem tailTrace_7174603 : CollatzResearch.WordTrace tailWord_7174603 prefixEnd_7174603 3684019844189698066467107 := by
  unfold tailWord_7174603
  simp only [CollatzResearch.WordTrace]
  refine ⟨261679269226646130484432463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174452846151097420322954975 261679269226646130484432463)
  ·
    refine ⟨392518903839969195726648695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261679269226646130484432463 392518903839969195726648695)
    ·
      refine ⟨588778355759953793589973043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392518903839969195726648695 588778355759953793589973043)
      ·
        refine ⟨883167533639930690384959565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588778355759953793589973043 883167533639930690384959565)
        ·
          refine ⟨331187825114974008894359837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 883167533639930690384959565 331187825114974008894359837)
          ·
            refine ⟨124195434418115253335384939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331187825114974008894359837 124195434418115253335384939)
            ·
              refine ⟨186293151627172880003077409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124195434418115253335384939 186293151627172880003077409)
              ·
                refine ⟨139719863720379660002308057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186293151627172880003077409 139719863720379660002308057)
                ·
                  refine ⟨104789897790284745001731043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139719863720379660002308057 104789897790284745001731043)
                  ·
                    refine ⟨157184846685427117502596565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104789897790284745001731043 157184846685427117502596565)
                    ·
                      refine ⟨3684019844189698066467107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157184846685427117502596565 3684019844189698066467107)
                      ·
                        rfl

theorem cell23_7174603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_7174603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174603 prefixEnd_7174603 := by exact prefixLift 7174603
  have htrace : WordTrace (prefixWord ++ tailWord_7174603) baseStart_7174603 baseEnd_7174603 := by
    simpa [prefixWord, tailWord_7174603, baseEnd_7174603] using wordTrace_append hprefix tailTrace_7174603
  have hstable : (prefixWord ++ tailWord_7174603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174603).length < 2 ^ (prefixWord ++ tailWord_7174603).sum := by decide
  have hdescent : baseEnd_7174603 < baseStart_7174603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174617 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 4, 3, 2]
def baseStart_7174617 : Nat := 118140960795 + 7174617 * 2 ^ 59
def prefixEnd_7174617 : Nat := 4983230072969 + 3 ^ 40 * 7174617 * 2
def baseEnd_7174617 : Nat := 3684027032918861011692043

theorem tailTrace_7174617 : CollatzResearch.WordTrace tailWord_7174617 prefixEnd_7174617 3684027032918861011692043 := by
  unfold tailWord_7174617
  simp only [CollatzResearch.WordTrace]
  refine ⟨261679779848595410875442105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174453186565730273916961403 261679779848595410875442105)
  ·
    refine ⟨196259834886446558156581579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261679779848595410875442105 196259834886446558156581579)
    ·
      refine ⟨294389752329669837234872369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196259834886446558156581579 294389752329669837234872369)
      ·
        refine ⟨220792314247252377926154277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294389752329669837234872369 220792314247252377926154277)
        ·
          refine ⟨41398558921359820861153927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220792314247252377926154277 41398558921359820861153927)
          ·
            refine ⟨62097838382039731291730891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41398558921359820861153927 62097838382039731291730891)
            ·
              refine ⟨93146757573059596937596337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62097838382039731291730891 93146757573059596937596337)
              ·
                refine ⟨69860068179794697703197253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93146757573059596937596337 69860068179794697703197253)
                ·
                  refine ⟨13098762783711505819349485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69860068179794697703197253 13098762783711505819349485)
                  ·
                    refine ⟨4912036043891814682256057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13098762783711505819349485 4912036043891814682256057)
                    ·
                      refine ⟨3684027032918861011692043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912036043891814682256057 3684027032918861011692043)
                      ·
                        rfl

theorem cell23_7174617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_7174617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174617 prefixEnd_7174617 := by exact prefixLift 7174617
  have htrace : WordTrace (prefixWord ++ tailWord_7174617) baseStart_7174617 baseEnd_7174617 := by
    simpa [prefixWord, tailWord_7174617, baseEnd_7174617] using wordTrace_append hprefix tailTrace_7174617
  have hstable : (prefixWord ++ tailWord_7174617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174617).length < 2 ^ (prefixWord ++ tailWord_7174617).sum := by decide
  have hdescent : baseEnd_7174617 < baseStart_7174617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174627 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 3, 5]
def baseStart_7174627 : Nat := 118140960795 + 7174627 * 2 ^ 59
def prefixEnd_7174627 : Nat := 4983230072969 + 3 ^ 40 * 7174627 * 2
def baseEnd_7174627 : Nat := 1228010722575135324188999

theorem tailTrace_7174627 : CollatzResearch.WordTrace tailWord_7174627 prefixEnd_7174627 1228010722575135324188999 := by
  unfold tailWord_7174627
  simp only [CollatzResearch.WordTrace]
  refine ⟨261680144578559182583306135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174453429719039455055537423 261680144578559182583306135)
  ·
    refine ⟨392520216867838773874959203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261680144578559182583306135 392520216867838773874959203)
    ·
      refine ⟨588780325301758160812438805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392520216867838773874959203 588780325301758160812438805)
      ·
        refine ⟨27599077748519913788083069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 588780325301758160812438805 27599077748519913788083069)
        ·
          refine ⟨10349654155694967670531151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27599077748519913788083069 10349654155694967670531151)
          ·
            refine ⟨15524481233542451505796727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349654155694967670531151 15524481233542451505796727)
            ·
              refine ⟨23286721850313677258695091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524481233542451505796727 23286721850313677258695091)
              ·
                refine ⟨34930082775470515888042637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23286721850313677258695091 34930082775470515888042637)
                ·
                  refine ⟨13098781040801443458015989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34930082775470515888042637 13098781040801443458015989)
                  ·
                    refine ⟨1228010722575135324188999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13098781040801443458015989 1228010722575135324188999)
                    ·
                      rfl

theorem cell23_7174627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].length) (baseStart_7174627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174627 prefixEnd_7174627 := by exact prefixLift 7174627
  have htrace : WordTrace (prefixWord ++ tailWord_7174627) baseStart_7174627 baseEnd_7174627 := by
    simpa [prefixWord, tailWord_7174627, baseEnd_7174627] using wordTrace_append hprefix tailTrace_7174627
  have hstable : (prefixWord ++ tailWord_7174627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174627).length < 2 ^ (prefixWord ++ tailWord_7174627).sum := by decide
  have hdescent : baseEnd_7174627 < baseStart_7174627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174634 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_7174634 : Nat := 118140960795 + 7174634 * 2 ^ 59
def prefixEnd_7174634 : Nat := 4983230072969 + 3 ^ 40 * 7174634 * 2
def baseEnd_7174634 : Nat := 3684035762089987445179465

theorem tailTrace_7174634 : CollatzResearch.WordTrace tailWord_7174634 prefixEnd_7174634 3684035762089987445179465 := by
  unfold tailWord_7174634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420099972383455694702739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174453599926355881852540637 65420099972383455694702739)
  ·
    refine ⟨98130149958575183542054109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420099972383455694702739 98130149958575183542054109)
    ·
      refine ⟨36798806234465693828270291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98130149958575183542054109 36798806234465693828270291)
      ·
        refine ⟨55198209351698540742405437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36798806234465693828270291 55198209351698540742405437)
        ·
          refine ⟨20699328506886952778402039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55198209351698540742405437 20699328506886952778402039)
          ·
            refine ⟨31048992760330429167603059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699328506886952778402039 31048992760330429167603059)
            ·
              refine ⟨46573489140495643751404589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31048992760330429167603059 46573489140495643751404589)
              ·
                refine ⟨17465058427685866406776721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46573489140495643751404589 17465058427685866406776721)
                ·
                  refine ⟨13098793820764399805082541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17465058427685866406776721 13098793820764399805082541)
                  ·
                    refine ⟨4912047682786649926905953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13098793820764399805082541 4912047682786649926905953)
                    ·
                      refine ⟨3684035762089987445179465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912047682786649926905953 3684035762089987445179465)
                      ·
                        rfl

theorem cell23_7174634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_7174634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174634 prefixEnd_7174634 := by exact prefixLift 7174634
  have htrace : WordTrace (prefixWord ++ tailWord_7174634) baseStart_7174634 baseEnd_7174634 := by
    simpa [prefixWord, tailWord_7174634, baseEnd_7174634] using wordTrace_append hprefix tailTrace_7174634
  have hstable : (prefixWord ++ tailWord_7174634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174634).length < 2 ^ (prefixWord ++ tailWord_7174634).sum := by decide
  have hdescent : baseEnd_7174634 < baseStart_7174634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174640 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_7174640 : Nat := 118140960795 + 7174640 * 2 ^ 59
def prefixEnd_7174640 : Nat := 4983230072969 + 3 ^ 40 * 7174640 * 2
def baseEnd_7174640 : Nat := 1228012947657971473901479

theorem tailTrace_7174640 : CollatzResearch.WordTrace tailWord_7174640 prefixEnd_7174640 1228012947657971473901479 := by
  unfold tailWord_7174640
  simp only [CollatzResearch.WordTrace]
  refine ⟨130840309363756042901764687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174453745818341390535686249 130840309363756042901764687)
  ·
    refine ⟨196260464045634064352647031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130840309363756042901764687 196260464045634064352647031)
    ·
      refine ⟨294390696068451096528970547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196260464045634064352647031 294390696068451096528970547)
      ·
        refine ⟨441586044102676644793455821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294390696068451096528970547 441586044102676644793455821)
        ·
          refine ⟨165594766538503741797545933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441586044102676644793455821 165594766538503741797545933)
          ·
            refine ⟨62098037451938903174079725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165594766538503741797545933 62098037451938903174079725)
            ·
              refine ⟨23286764044477088690279897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62098037451938903174079725 23286764044477088690279897)
              ·
                refine ⟨17465073033357816517709923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23286764044477088690279897 17465073033357816517709923)
                ·
                  refine ⟨26197609550036724776564885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17465073033357816517709923 26197609550036724776564885)
                  ·
                    refine ⟨1228012947657971473901479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26197609550036724776564885 1228012947657971473901479)
                    ·
                      rfl

theorem cell23_7174640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_7174640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174640 prefixEnd_7174640 := by exact prefixLift 7174640
  have htrace : WordTrace (prefixWord ++ tailWord_7174640) baseStart_7174640 baseEnd_7174640 := by
    simpa [prefixWord, tailWord_7174640, baseEnd_7174640] using wordTrace_append hprefix tailTrace_7174640
  have hstable : (prefixWord ++ tailWord_7174640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174640).length < 2 ^ (prefixWord ++ tailWord_7174640).sum := by decide
  have hdescent : baseEnd_7174640 < baseStart_7174640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174650 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_7174650 : Nat := 118140960795 + 7174650 * 2 ^ 59
def prefixEnd_7174650 : Nat := 4983230072969 + 3 ^ 40 * 7174650 * 2
def baseEnd_7174650 : Nat := 3684043977780459382579391

theorem tailTrace_7174650 : CollatzResearch.WordTrace tailWord_7174650 prefixEnd_7174650 3684043977780459382579391 := by
  unfold tailWord_7174650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420245864368964377848351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174453988971650571674262269 65420245864368964377848351)
  ·
    refine ⟨98130368796553446566772527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420245864368964377848351 98130368796553446566772527)
    ·
      refine ⟨147195553194830169850158791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98130368796553446566772527 147195553194830169850158791)
      ·
        refine ⟨220793329792245254775238187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147195553194830169850158791 220793329792245254775238187)
        ·
          refine ⟨331189994688367882162857281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220793329792245254775238187 331189994688367882162857281)
          ·
            refine ⟨248392496016275911622142961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331189994688367882162857281 248392496016275911622142961)
            ·
              refine ⟨186294372012206933716607221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248392496016275911622142961 186294372012206933716607221)
              ·
                refine ⟨17465097376144400035931927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186294372012206933716607221 17465097376144400035931927)
                ·
                  refine ⟨26197646064216600053897891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17465097376144400035931927 26197646064216600053897891)
                  ·
                    refine ⟨39296469096324900080846837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26197646064216600053897891 39296469096324900080846837)
                    ·
                      refine ⟨3684043977780459382579391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39296469096324900080846837 3684043977780459382579391)
                      ·
                        rfl

theorem cell23_7174650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_7174650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174650 prefixEnd_7174650 := by exact prefixLift 7174650
  have htrace : WordTrace (prefixWord ++ tailWord_7174650) baseStart_7174650 baseEnd_7174650 := by
    simpa [prefixWord, tailWord_7174650, baseEnd_7174650] using wordTrace_append hprefix tailTrace_7174650
  have hstable : (prefixWord ++ tailWord_7174650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174650).length < 2 ^ (prefixWord ++ tailWord_7174650).sum := by decide
  have hdescent : baseEnd_7174650 < baseStart_7174650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174664 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_7174664 : Nat := 118140960795 + 7174664 * 2 ^ 59
def prefixEnd_7174664 : Nat := 4983230072969 + 3 ^ 40 * 7174664 * 2
def baseEnd_7174664 : Nat := 3684051166509622327804327

theorem tailTrace_7174664 : CollatzResearch.WordTrace tailWord_7174664 prefixEnd_7174664 3684051166509622327804327 := by
  unfold tailWord_7174664
  simp only [CollatzResearch.WordTrace]
  refine ⟨130840747039712568951201523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174454329386283425268268697 130840747039712568951201523)
  ·
    refine ⟨196261120559568853426802285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130840747039712568951201523 196261120559568853426802285)
    ·
      refine ⟨73597920209838320035050857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196261120559568853426802285 73597920209838320035050857)
      ·
        refine ⟨55198440157378740026288143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73597920209838320035050857 55198440157378740026288143)
        ·
          refine ⟨82797660236068110039432215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55198440157378740026288143 82797660236068110039432215)
          ·
            refine ⟨124196490354102165059148323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82797660236068110039432215 124196490354102165059148323)
            ·
              refine ⟨186294735531153247588722485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124196490354102165059148323 186294735531153247588722485)
              ·
                refine ⟨17465131456045616961442733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186294735531153247588722485 17465131456045616961442733)
                ·
                  refine ⟨6549424296017106360541025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17465131456045616961442733 6549424296017106360541025)
                  ·
                    refine ⟨4912068222012829770405769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549424296017106360541025 4912068222012829770405769)
                    ·
                      refine ⟨3684051166509622327804327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912068222012829770405769 3684051166509622327804327)
                      ·
                        rfl

theorem cell23_7174664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_7174664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174664 prefixEnd_7174664 := by exact prefixLift 7174664
  have htrace : WordTrace (prefixWord ++ tailWord_7174664) baseStart_7174664 baseEnd_7174664 := by
    simpa [prefixWord, tailWord_7174664, baseEnd_7174664] using wordTrace_append hprefix tailTrace_7174664
  have hstable : (prefixWord ++ tailWord_7174664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174664).length < 2 ^ (prefixWord ++ tailWord_7174664).sum := by decide
  have hdescent : baseEnd_7174664 < baseStart_7174664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174667 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3]
def baseStart_7174667 : Nat := 118140960795 + 7174667 * 2 ^ 59
def prefixEnd_7174667 : Nat := 4983230072969 + 3 ^ 40 * 7174667 * 2
def baseEnd_7174667 : Nat := 3684052706951585816066813

theorem tailTrace_7174667 : CollatzResearch.WordTrace tailWord_7174667 prefixEnd_7174667 3684052706951585816066813 := by
  unfold tailWord_7174667
  simp only [CollatzResearch.WordTrace]
  refine ⟨261681603498414269414762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174454402332276179609841503 261681603498414269414762255)
  ·
    refine ⟨392522405247621404122143383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261681603498414269414762255 392522405247621404122143383)
    ·
      refine ⟨588783607871432106183215075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392522405247621404122143383 588783607871432106183215075)
      ·
        refine ⟨883175411807148159274822613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588783607871432106183215075 883175411807148159274822613)
        ·
          refine ⟨20699423714230034983003655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 883175411807148159274822613 20699423714230034983003655)
          ·
            refine ⟨31049135571345052474505483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699423714230034983003655 31049135571345052474505483)
            ·
              refine ⟨46573703357017578711758225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31049135571345052474505483 46573703357017578711758225)
              ·
                refine ⟨34930277517763184033818669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46573703357017578711758225 34930277517763184033818669)
                ·
                  refine ⟨13098854069161194012682001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34930277517763184033818669 13098854069161194012682001)
                  ·
                    refine ⟨9824140551870895509511501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13098854069161194012682001 9824140551870895509511501)
                    ·
                      refine ⟨3684052706951585816066813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824140551870895509511501 3684052706951585816066813)
                      ·
                        rfl

theorem cell23_7174667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].length) (baseStart_7174667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174667 prefixEnd_7174667 := by exact prefixLift 7174667
  have htrace : WordTrace (prefixWord ++ tailWord_7174667) baseStart_7174667 baseEnd_7174667 := by
    simpa [prefixWord, tailWord_7174667, baseEnd_7174667] using wordTrace_append hprefix tailTrace_7174667
  have hstable : (prefixWord ++ tailWord_7174667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174667).length < 2 ^ (prefixWord ++ tailWord_7174667).sum := by decide
  have hdescent : baseEnd_7174667 < baseStart_7174667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174677 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_7174677 : Nat := 118140960795 + 7174677 * 2 ^ 59
def prefixEnd_7174677 : Nat := 4983230072969 + 3 ^ 40 * 7174677 * 2
def baseEnd_7174677 : Nat := 3684057841758130776941767

theorem tailTrace_7174677 : CollatzResearch.WordTrace tailWord_7174677 prefixEnd_7174677 3684057841758130776941767 := by
  unfold tailWord_7174677
  simp only [CollatzResearch.WordTrace]
  refine ⟨261681968228378041122626285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174454645485585360748417523 261681968228378041122626285)
  ·
    refine ⟨98130738085641765420984857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261681968228378041122626285 98130738085641765420984857)
    ·
      refine ⟨73598053564231324065738643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98130738085641765420984857 73598053564231324065738643)
      ·
        refine ⟨110397080346346986098607965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73598053564231324065738643 110397080346346986098607965)
        ·
          refine ⟨41398905129880119786977987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110397080346346986098607965 41398905129880119786977987)
          ·
            refine ⟨62098357694820179680466981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41398905129880119786977987 62098357694820179680466981)
            ·
              refine ⟨11643442067778783690087559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62098357694820179680466981 11643442067778783690087559)
              ·
                refine ⟨17465163101668175535131339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11643442067778783690087559 17465163101668175535131339)
                ·
                  refine ⟨26197744652502263302697009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17465163101668175535131339 26197744652502263302697009)
                  ·
                    refine ⟨19648308489376697477022757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26197744652502263302697009 19648308489376697477022757)
                    ·
                      refine ⟨3684057841758130776941767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19648308489376697477022757 3684057841758130776941767)
                      ·
                        rfl

theorem cell23_7174677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_7174677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174677 prefixEnd_7174677 := by exact prefixLift 7174677
  have htrace : WordTrace (prefixWord ++ tailWord_7174677) baseStart_7174677 baseEnd_7174677 := by
    simpa [prefixWord, tailWord_7174677, baseEnd_7174677] using wordTrace_append hprefix tailTrace_7174677
  have hstable : (prefixWord ++ tailWord_7174677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174677).length < 2 ^ (prefixWord ++ tailWord_7174677).sum := by decide
  have hdescent : baseEnd_7174677 < baseStart_7174677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174695 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7174695 : Nat := 118140960795 + 7174695 * 2 ^ 59
def prefixEnd_7174695 : Nat := 4983230072969 + 3 ^ 40 * 7174695 * 2
def baseEnd_7174695 : Nat := 1228022361469970568838895

theorem tailTrace_7174695 : CollatzResearch.WordTrace tailWord_7174695 prefixEnd_7174695 1228022361469970568838895 := by
  unfold tailWord_7174695
  simp only [CollatzResearch.WordTrace]
  refine ⟨261682624742312830196781539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174455083161541886797854359 261682624742312830196781539)
  ·
    refine ⟨392523937113469245295172309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261682624742312830196781539 392523937113469245295172309)
    ·
      refine ⟨9199779776096935436605601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 392523937113469245295172309 9199779776096935436605601)
      ·
        refine ⟨6899834832072701577454201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9199779776096935436605601 6899834832072701577454201)
        ·
          refine ⟨5174876124054526183090651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899834832072701577454201 5174876124054526183090651)
          ·
            refine ⟨7762314186081789274635977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174876124054526183090651 7762314186081789274635977)
            ·
              refine ⟨5821735639561341955976983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762314186081789274635977 5821735639561341955976983)
              ·
                refine ⟨8732603459342012933965475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821735639561341955976983 8732603459342012933965475)
                ·
                  refine ⟨13098905189013019400948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8732603459342012933965475 13098905189013019400948213)
                  ·
                    refine ⟨1228022361469970568838895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13098905189013019400948213 1228022361469970568838895)
                    ·
                      rfl

theorem cell23_7174695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7174695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174695 prefixEnd_7174695 := by exact prefixLift 7174695
  have htrace : WordTrace (prefixWord ++ tailWord_7174695) baseStart_7174695 baseEnd_7174695 := by
    simpa [prefixWord, tailWord_7174695, baseEnd_7174695] using wordTrace_append hprefix tailTrace_7174695
  have hstable : (prefixWord ++ tailWord_7174695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174695).length < 2 ^ (prefixWord ++ tailWord_7174695).sum := by decide
  have hdescent : baseEnd_7174695 < baseStart_7174695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174698 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7174698 : Nat := 118140960795 + 7174698 * 2 ^ 59
def prefixEnd_7174698 : Nat := 4983230072969 + 3 ^ 40 * 7174698 * 2
def baseEnd_7174698 : Nat := 3684068624851875194779171

theorem tailTrace_7174698 : CollatzResearch.WordTrace tailWord_7174698 prefixEnd_7174698 3684068624851875194779171 := by
  unfold tailWord_7174698
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420683540325490427285187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174455156107534641139427165 65420683540325490427285187)
  ·
    refine ⟨98131025310488235640927781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420683540325490427285187 98131025310488235640927781)
    ·
      refine ⟨18399567245716544182673959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98131025310488235640927781 18399567245716544182673959)
      ·
        refine ⟨27599350868574816274010939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18399567245716544182673959 27599350868574816274010939)
        ·
          refine ⟨41399026302862224411016409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27599350868574816274010939 41399026302862224411016409)
          ·
            refine ⟨31049269727146668308262307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41399026302862224411016409 31049269727146668308262307)
            ·
              refine ⟨46573904590720002462393461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31049269727146668308262307 46573904590720002462393461)
              ·
                refine ⟨4366303555380000230849387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46573904590720002462393461 4366303555380000230849387)
                ·
                  refine ⟨6549455333070000346274081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366303555380000230849387 6549455333070000346274081)
                  ·
                    refine ⟨4912091499802500259705561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549455333070000346274081 4912091499802500259705561)
                    ·
                      refine ⟨3684068624851875194779171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912091499802500259705561 3684068624851875194779171)
                      ·
                        rfl

theorem cell23_7174698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7174698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174698 prefixEnd_7174698 := by exact prefixLift 7174698
  have htrace : WordTrace (prefixWord ++ tailWord_7174698) baseStart_7174698 baseEnd_7174698 := by
    simpa [prefixWord, tailWord_7174698, baseEnd_7174698] using wordTrace_append hprefix tailTrace_7174698
  have hstable : (prefixWord ++ tailWord_7174698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174698).length < 2 ^ (prefixWord ++ tailWord_7174698).sum := by decide
  have hdescent : baseEnd_7174698 < baseStart_7174698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174714 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_7174714 : Nat := 118140960795 + 7174714 * 2 ^ 59
def prefixEnd_7174714 : Nat := 4983230072969 + 3 ^ 40 * 7174714 * 2
def baseEnd_7174714 : Nat := 3684076840542347132179097

theorem tailTrace_7174714 : CollatzResearch.WordTrace tailWord_7174714 prefixEnd_7174714 3684076840542347132179097 := by
  unfold tailWord_7174714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420829432310999110430799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174455545152829330961148797 65420829432310999110430799)
  ·
    refine ⟨98131244148466498665646199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420829432310999110430799 98131244148466498665646199)
    ·
      refine ⟨147196866222699747998469299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98131244148466498665646199 147196866222699747998469299)
      ·
        refine ⟨220795299334049621997703949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147196866222699747998469299 220795299334049621997703949)
        ·
          refine ⟨82798237250268608249138981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220795299334049621997703949 82798237250268608249138981)
          ·
            refine ⟨15524669484425364046713559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82798237250268608249138981 15524669484425364046713559)
            ·
              refine ⟨23287004226638046070070339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524669484425364046713559 23287004226638046070070339)
              ·
                refine ⟨34930506339957069105105509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23287004226638046070070339 34930506339957069105105509)
                ·
                  refine ⟨6549469938741950457207283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34930506339957069105105509 6549469938741950457207283)
                  ·
                    refine ⟨9824204908112925685810925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549469938741950457207283 9824204908112925685810925)
                    ·
                      refine ⟨3684076840542347132179097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824204908112925685810925 3684076840542347132179097)
                      ·
                        rfl

theorem cell23_7174714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_7174714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174714 prefixEnd_7174714 := by exact prefixLift 7174714
  have htrace : WordTrace (prefixWord ++ tailWord_7174714) baseStart_7174714 baseEnd_7174714 := by
    simpa [prefixWord, tailWord_7174714, baseEnd_7174714] using wordTrace_append hprefix tailTrace_7174714
  have hstable : (prefixWord ++ tailWord_7174714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174714).length < 2 ^ (prefixWord ++ tailWord_7174714).sum := by decide
  have hdescent : baseEnd_7174714 < baseStart_7174714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174720 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_7174720 : Nat := 118140960795 + 7174720 * 2 ^ 59
def prefixEnd_7174720 : Nat := 4983230072969 + 3 ^ 40 * 7174720 * 2
def baseEnd_7174720 : Nat := 3684079921426274108704069

theorem tailTrace_7174720 : CollatzResearch.WordTrace tailWord_7174720 prefixEnd_7174720 3684079921426274108704069 := by
  unfold tailWord_7174720
  simp only [CollatzResearch.WordTrace]
  refine ⟨130841768283611129733220807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174455691044814839644294409 130841768283611129733220807)
  ·
    refine ⟨196262652425416694599831211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130841768283611129733220807 196262652425416694599831211)
    ·
      refine ⟨294393978638125041899746817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196262652425416694599831211 294393978638125041899746817)
      ·
        refine ⟨220795483978593781424810113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294393978638125041899746817 220795483978593781424810113)
        ·
          refine ⟨165596612983945336068607585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220795483978593781424810113 165596612983945336068607585)
          ·
            refine ⟨124197459737959002051455689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165596612983945336068607585 124197459737959002051455689)
            ·
              refine ⟨93148094803469251538591767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124197459737959002051455689 93148094803469251538591767)
              ·
                refine ⟨139722142205203877307887651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93148094803469251538591767 139722142205203877307887651)
                ·
                  refine ⟨209583213307805815961831477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139722142205203877307887651 209583213307805815961831477)
                  ·
                    refine ⟨19648426247606795246421701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209583213307805815961831477 19648426247606795246421701)
                    ·
                      refine ⟨3684079921426274108704069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19648426247606795246421701 3684079921426274108704069)
                      ·
                        rfl

theorem cell23_7174720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_7174720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174720 prefixEnd_7174720 := by exact prefixLift 7174720
  have htrace : WordTrace (prefixWord ++ tailWord_7174720) baseStart_7174720 baseEnd_7174720 := by
    simpa [prefixWord, tailWord_7174720, baseEnd_7174720] using wordTrace_append hprefix tailTrace_7174720
  have hstable : (prefixWord ++ tailWord_7174720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174720).length < 2 ^ (prefixWord ++ tailWord_7174720).sum := by decide
  have hdescent : baseEnd_7174720 < baseStart_7174720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174777 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 7]
def baseStart_7174777 : Nat := 118140960795 + 7174777 * 2 ^ 59
def prefixEnd_7174777 : Nat := 4983230072969 + 3 ^ 40 * 7174777 * 2
def baseEnd_7174777 : Nat := 409345465535953376187923

theorem tailTrace_7174777 : CollatzResearch.WordTrace tailWord_7174777 prefixEnd_7174777 409345465535953376187923 := by
  unfold tailWord_7174777
  simp only [CollatzResearch.WordTrace]
  refine ⟨261685615528015758201266585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174457077018677172134177723 261685615528015758201266585)
  ·
    refine ⟨196264211646011818650949939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261685615528015758201266585 196264211646011818650949939)
    ·
      refine ⟨294396317469017727976424909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196264211646011818650949939 294396317469017727976424909)
      ·
        refine ⟨110398619050881647991159341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294396317469017727976424909 110398619050881647991159341)
        ·
          refine ⟨41399482144080617996684753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110398619050881647991159341 41399482144080617996684753)
          ·
            refine ⟨31049611608060463497513565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41399482144080617996684753 31049611608060463497513565)
            ·
              refine ⟨11643604353022673811567587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31049611608060463497513565 11643604353022673811567587)
              ·
                refine ⟨17465406529534010717351381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11643604353022673811567587 17465406529534010717351381)
                ·
                  refine ⟨409345465535953376187923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17465406529534010717351381 409345465535953376187923)
                  ·
                    rfl

theorem cell23_7174777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_7174777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174777 prefixEnd_7174777 := by exact prefixLift 7174777
  have htrace : WordTrace (prefixWord ++ tailWord_7174777) baseStart_7174777 baseEnd_7174777 := by
    simpa [prefixWord, tailWord_7174777, baseEnd_7174777] using wordTrace_append hprefix tailTrace_7174777
  have hstable : (prefixWord ++ tailWord_7174777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174777).length < 2 ^ (prefixWord ++ tailWord_7174777).sum := by decide
  have hdescent : baseEnd_7174777 < baseStart_7174777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174787 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3]
def baseStart_7174787 : Nat := 118140960795 + 7174787 * 2 ^ 59
def prefixEnd_7174787 : Nat := 4983230072969 + 3 ^ 40 * 7174787 * 2
def baseEnd_7174787 : Nat := 3684114324630125346566261

theorem tailTrace_7174787 : CollatzResearch.WordTrace tailWord_7174787 prefixEnd_7174787 3684114324630125346566261 := by
  unfold tailWord_7174787
  simp only [CollatzResearch.WordTrace]
  refine ⟨261685980257979529909130615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174457320171986353272753743 261685980257979529909130615)
  ·
    refine ⟨392528970386969294863695923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261685980257979529909130615 392528970386969294863695923)
    ·
      refine ⟨588793455580453942295543885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392528970386969294863695923 588793455580453942295543885)
      ·
        refine ⟨220797545842670228360828957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588793455580453942295543885 220797545842670228360828957)
        ·
          refine ⟨82799079691001335635310859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220797545842670228360828957 82799079691001335635310859)
          ·
            refine ⟨124198619536502003452966289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82799079691001335635310859 124198619536502003452966289)
            ·
              refine ⟨93148964652376502589724717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124198619536502003452966289 93148964652376502589724717)
              ·
                refine ⟨34930861744641188471146769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93148964652376502589724717 34930861744641188471146769)
                ·
                  refine ⟨26198146308480891353360077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34930861744641188471146769 26198146308480891353360077)
                  ·
                    refine ⟨9824304865680334257510029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26198146308480891353360077 9824304865680334257510029)
                    ·
                      refine ⟨3684114324630125346566261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824304865680334257510029 3684114324630125346566261)
                      ·
                        rfl

theorem cell23_7174787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_7174787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174787 prefixEnd_7174787 := by exact prefixLift 7174787
  have htrace : WordTrace (prefixWord ++ tailWord_7174787) baseStart_7174787 baseEnd_7174787 := by
    simpa [prefixWord, tailWord_7174787, baseEnd_7174787] using wordTrace_append hprefix tailTrace_7174787
  have hstable : (prefixWord ++ tailWord_7174787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174787).length < 2 ^ (prefixWord ++ tailWord_7174787).sum := by decide
  have hdescent : baseEnd_7174787 < baseStart_7174787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174788 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_7174788 : Nat := 118140960795 + 7174788 * 2 ^ 59
def prefixEnd_7174788 : Nat := 4983230072969 + 3 ^ 40 * 7174788 * 2
def baseEnd_7174788 : Nat := 3684114838110779842653757

theorem tailTrace_7174788 : CollatzResearch.WordTrace tailWord_7174788 prefixEnd_7174788 3684114838110779842653757 := by
  unfold tailWord_7174788
  simp only [CollatzResearch.WordTrace]
  refine ⟨130843008365487953539958509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174457344487317271386611345 130843008365487953539958509)
  ·
    refine ⟨49066128137057982577484441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130843008365487953539958509 49066128137057982577484441)
    ·
      refine ⟨36799596102793486933113331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49066128137057982577484441 36799596102793486933113331)
      ·
        refine ⟨55199394154190230399669997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36799596102793486933113331 55199394154190230399669997)
        ·
          refine ⟨20699772807821336399876249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55199394154190230399669997 20699772807821336399876249)
          ·
            refine ⟨15524829605866002299907187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20699772807821336399876249 15524829605866002299907187)
            ·
              refine ⟨23287244408799003449860781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524829605866002299907187 23287244408799003449860781)
              ·
                refine ⟨8732716653299626293697793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23287244408799003449860781 8732716653299626293697793)
                ·
                  refine ⟨6549537489974719720273345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732716653299626293697793 6549537489974719720273345)
                  ·
                    refine ⟨4912153117481039790205009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549537489974719720273345 4912153117481039790205009)
                    ·
                      refine ⟨3684114838110779842653757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912153117481039790205009 3684114838110779842653757)
                      ·
                        rfl

theorem cell23_7174788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_7174788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174788 prefixEnd_7174788 := by exact prefixLift 7174788
  have htrace : WordTrace (prefixWord ++ tailWord_7174788) baseStart_7174788 baseEnd_7174788 := by
    simpa [prefixWord, tailWord_7174788, baseEnd_7174788] using wordTrace_append hprefix tailTrace_7174788
  have hstable : (prefixWord ++ tailWord_7174788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174788).length < 2 ^ (prefixWord ++ tailWord_7174788).sum := by decide
  have hdescent : baseEnd_7174788 < baseStart_7174788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174838 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7174838 : Nat := 118140960795 + 7174838 * 2 ^ 59
def prefixEnd_7174838 : Nat := 4983230072969 + 3 ^ 40 * 7174838 * 2
def baseEnd_7174838 : Nat := 3684140512143504647028527

theorem tailTrace_7174838 : CollatzResearch.WordTrace tailWord_7174838 prefixEnd_7174838 3684140512143504647028527 := by
  unfold tailWord_7174838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355490023799672851202323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174458560253863177079491445 16355490023799672851202323)
  ·
    refine ⟨24533235035699509276803485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355490023799672851202323 24533235035699509276803485)
    ·
      refine ⟨9199963138387315978801307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24533235035699509276803485 9199963138387315978801307)
      ·
        refine ⟨13799944707580973968201961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199963138387315978801307 13799944707580973968201961)
        ·
          refine ⟨10349958530685730476151471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799944707580973968201961 10349958530685730476151471)
          ·
            refine ⟨15524937796028595714227207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349958530685730476151471 15524937796028595714227207)
            ·
              refine ⟨23287406694042893571340811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524937796028595714227207 23287406694042893571340811)
              ·
                refine ⟨34931110041064340357011217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23287406694042893571340811 34931110041064340357011217)
                ·
                  refine ⟨26198332530798255267758413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34931110041064340357011217 26198332530798255267758413)
                  ·
                    refine ⟨9824374699049345725409405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26198332530798255267758413 9824374699049345725409405)
                    ·
                      refine ⟨3684140512143504647028527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824374699049345725409405 3684140512143504647028527)
                      ·
                        rfl

theorem cell23_7174838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7174838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174838 prefixEnd_7174838 := by exact prefixLift 7174838
  have htrace : WordTrace (prefixWord ++ tailWord_7174838) baseStart_7174838 baseEnd_7174838 := by
    simpa [prefixWord, tailWord_7174838, baseEnd_7174838] using wordTrace_append hprefix tailTrace_7174838
  have hstable : (prefixWord ++ tailWord_7174838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174838).length < 2 ^ (prefixWord ++ tailWord_7174838).sum := by decide
  have hdescent : baseEnd_7174838 < baseStart_7174838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174871 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 1, 4]
def baseStart_7174871 : Nat := 118140960795 + 7174871 * 2 ^ 59
def prefixEnd_7174871 : Nat := 4983230072969 + 3 ^ 40 * 7174871 * 2
def baseEnd_7174871 : Nat := 1228052485668367672638625

theorem tailTrace_7174871 : CollatzResearch.WordTrace tailWord_7174871 prefixEnd_7174871 1228052485668367672638625 := by
  unfold tailWord_7174871
  simp only [CollatzResearch.WordTrace]
  refine ⟨261689043989675212255188467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174459362659783474836792311 261689043989675212255188467)
  ·
    refine ⟨392533565984512818382782701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261689043989675212255188467 392533565984512818382782701)
    ·
      refine ⟨147200087244192306893543513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392533565984512818382782701 147200087244192306893543513)
      ·
        refine ⟨110400065433144230170157635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147200087244192306893543513 110400065433144230170157635)
        ·
          refine ⟨165600098149716345255236453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110400065433144230170157635 165600098149716345255236453)
          ·
            refine ⟨31050018403071814735356835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165600098149716345255236453 31050018403071814735356835)
            ·
              refine ⟨46575027604607722103035253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31050018403071814735356835 46575027604607722103035253)
              ·
                refine ⟨4366408837931973947159555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46575027604607722103035253 4366408837931973947159555)
                ·
                  refine ⟨6549613256897960920739333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366408837931973947159555 6549613256897960920739333)
                  ·
                    refine ⟨1228052485668367672638625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549613256897960920739333 1228052485668367672638625)
                    ·
                      rfl

theorem cell23_7174871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_7174871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174871 prefixEnd_7174871 := by exact prefixLift 7174871
  have htrace : WordTrace (prefixWord ++ tailWord_7174871) baseStart_7174871 baseEnd_7174871 := by
    simpa [prefixWord, tailWord_7174871, baseEnd_7174871] using wordTrace_append hprefix tailTrace_7174871
  have hstable : (prefixWord ++ tailWord_7174871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174871).length < 2 ^ (prefixWord ++ tailWord_7174871).sum := by decide
  have hdescent : baseEnd_7174871 < baseStart_7174871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174884 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 6]
def baseStart_7174884 : Nat := 118140960795 + 7174884 * 2 ^ 59
def prefixEnd_7174884 : Nat := 4983230072969 + 3 ^ 40 * 7174884 * 2
def baseEnd_7174884 : Nat := 409351570250401274117035

theorem tailTrace_7174884 : CollatzResearch.WordTrace tailWord_7174884 prefixEnd_7174884 409351570250401274117035 := by
  unfold tailWord_7174884
  simp only [CollatzResearch.WordTrace]
  refine ⟨130844759069314057737705853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174459678759085410316941137 130844759069314057737705853)
  ·
    refine ⟨49066784650992771651639695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130844759069314057737705853 49066784650992771651639695)
    ·
      refine ⟨73600176976489157477459543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49066784650992771651639695 73600176976489157477459543)
      ·
        refine ⟨110400265464733736216189315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73600176976489157477459543 110400265464733736216189315)
        ·
          refine ⟨165600398197100604324283973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110400265464733736216189315 165600398197100604324283973)
          ·
            refine ⟨31050074661956363310803245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165600398197100604324283973 31050074661956363310803245)
            ·
              refine ⟨11643777998233636241551217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31050074661956363310803245 11643777998233636241551217)
              ·
                refine ⟨8732833498675227181163413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11643777998233636241551217 8732833498675227181163413)
                ·
                  refine ⟨409351570250401274117035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8732833498675227181163413 409351570250401274117035)
                  ·
                    rfl

theorem cell23_7174884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_7174884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174884 prefixEnd_7174884 := by exact prefixLift 7174884
  have htrace : WordTrace (prefixWord ++ tailWord_7174884) baseStart_7174884 baseEnd_7174884 := by
    simpa [prefixWord, tailWord_7174884, baseEnd_7174884] using wordTrace_append hprefix tailTrace_7174884
  have hstable : (prefixWord ++ tailWord_7174884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174884).length < 2 ^ (prefixWord ++ tailWord_7174884).sum := by decide
  have hdescent : baseEnd_7174884 < baseStart_7174884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174904 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_7174904 : Nat := 118140960795 + 7174904 * 2 ^ 59
def prefixEnd_7174904 : Nat := 4983230072969 + 3 ^ 40 * 7174904 * 2
def baseEnd_7174904 : Nat := 3684174401866701388803223

theorem tailTrace_7174904 : CollatzResearch.WordTrace tailWord_7174904 prefixEnd_7174904 3684174401866701388803223 := by
  unfold tailWord_7174904
  simp only [CollatzResearch.WordTrace]
  refine ⟨130845123799277829445569883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174460165065703772594093177 130845123799277829445569883)
  ·
    refine ⟨196267685698916744168354825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130845123799277829445569883 196267685698916744168354825)
    ·
      refine ⟨147200764274187558126266119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196267685698916744168354825 147200764274187558126266119)
      ·
        refine ⟨220801146411281337189399179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147200764274187558126266119 220801146411281337189399179)
        ·
          refine ⟨331201719616922005784098769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220801146411281337189399179 331201719616922005784098769)
          ·
            refine ⟨248401289712691504338074077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331201719616922005784098769 248401289712691504338074077)
            ·
              refine ⟨93150483642259314126777779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248401289712691504338074077 93150483642259314126777779)
              ·
                refine ⟨139725725463388971190166669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93150483642259314126777779 139725725463388971190166669)
                ·
                  refine ⟨52397147048770864196312501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139725725463388971190166669 52397147048770864196312501)
                  ·
                    refine ⟨4912232535822268518404297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52397147048770864196312501 4912232535822268518404297)
                    ·
                      refine ⟨3684174401866701388803223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912232535822268518404297 3684174401866701388803223)
                      ·
                        rfl

theorem cell23_7174904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_7174904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174904 prefixEnd_7174904 := by exact prefixLift 7174904
  have htrace : WordTrace (prefixWord ++ tailWord_7174904) baseStart_7174904 baseEnd_7174904 := by
    simpa [prefixWord, tailWord_7174904, baseEnd_7174904] using wordTrace_append hprefix tailTrace_7174904
  have hstable : (prefixWord ++ tailWord_7174904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174904).length < 2 ^ (prefixWord ++ tailWord_7174904).sum := by decide
  have hdescent : baseEnd_7174904 < baseStart_7174904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174917 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_7174917 : Nat := 118140960795 + 7174917 * 2 ^ 59
def prefixEnd_7174917 : Nat := 4983230072969 + 3 ^ 40 * 7174917 * 2
def baseEnd_7174917 : Nat := 3684181077115209837940663

theorem tailTrace_7174917 : CollatzResearch.WordTrace tailWord_7174917 prefixEnd_7174917 3684181077115209837940663 := by
  unfold tailWord_7174917
  simp only [CollatzResearch.WordTrace]
  refine ⟨261690721747508562111363005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174460481165005708074242003 261690721747508562111363005)
  ·
    refine ⟨98134020655315710791761127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261690721747508562111363005 98134020655315710791761127)
    ·
      refine ⟨147201030982973566187641691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98134020655315710791761127 147201030982973566187641691)
      ·
        refine ⟨220801546474460349281462537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147201030982973566187641691 220801546474460349281462537)
        ·
          refine ⟨165601159855845261961096903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220801546474460349281462537 165601159855845261961096903)
          ·
            refine ⟨248401739783767892941645355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165601159855845261961096903 248401739783767892941645355)
            ·
              refine ⟨372602609675651839412468033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248401739783767892941645355 372602609675651839412468033)
              ·
                refine ⟨279451957256738879559351025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372602609675651839412468033 279451957256738879559351025)
                ·
                  refine ⟨209588967942554159669513269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279451957256738879559351025 209588967942554159669513269)
                  ·
                    refine ⟨19648965744614452469016869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209588967942554159669513269 19648965744614452469016869)
                    ·
                      refine ⟨3684181077115209837940663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19648965744614452469016869 3684181077115209837940663)
                      ·
                        rfl

theorem cell23_7174917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_7174917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174917 prefixEnd_7174917 := by exact prefixLift 7174917
  have htrace : WordTrace (prefixWord ++ tailWord_7174917) baseStart_7174917 baseEnd_7174917 := by
    simpa [prefixWord, tailWord_7174917, baseEnd_7174917] using wordTrace_append hprefix tailTrace_7174917
  have hstable : (prefixWord ++ tailWord_7174917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174917).length < 2 ^ (prefixWord ++ tailWord_7174917).sum := by decide
  have hdescent : baseEnd_7174917 < baseStart_7174917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174927 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 6]
def baseStart_7174927 : Nat := 118140960795 + 7174927 * 2 ^ 59
def prefixEnd_7174927 : Nat := 4983230072969 + 3 ^ 40 * 7174927 * 2
def baseEnd_7174927 : Nat := 1228062070640584932938539

theorem tailTrace_7174927 : CollatzResearch.WordTrace tailWord_7174927 prefixEnd_7174927 1228062070640584932938539 := by
  unfold tailWord_7174927
  simp only [CollatzResearch.WordTrace]
  refine ⟨261691086477472333819227035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174460724318314889212818023 261691086477472333819227035)
  ·
    refine ⟨392536629716208500728840553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261691086477472333819227035 392536629716208500728840553)
    ·
      refine ⟨294402472287156375546630415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392536629716208500728840553 294402472287156375546630415)
      ·
        refine ⟨441603708430734563319945623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294402472287156375546630415 441603708430734563319945623)
        ·
          refine ⟨662405562646101844979918435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441603708430734563319945623 662405562646101844979918435)
          ·
            refine ⟨993608343969152767469877653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662405562646101844979918435 993608343969152767469877653)
            ·
              refine ⟨46575391123554035975150515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 993608343969152767469877653 46575391123554035975150515)
              ·
                refine ⟨69863086685331053962725773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46575391123554035975150515 69863086685331053962725773)
                ·
                  refine ⟨26198657506999145236022165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69863086685331053962725773 26198657506999145236022165)
                  ·
                    refine ⟨1228062070640584932938539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26198657506999145236022165 1228062070640584932938539)
                    ·
                      rfl

theorem cell23_7174927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_7174927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174927 prefixEnd_7174927 := by exact prefixLift 7174927
  have htrace : WordTrace (prefixWord ++ tailWord_7174927) baseStart_7174927 baseEnd_7174927 := by
    simpa [prefixWord, tailWord_7174927, baseEnd_7174927] using wordTrace_append hprefix tailTrace_7174927
  have hstable : (prefixWord ++ tailWord_7174927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174927).length < 2 ^ (prefixWord ++ tailWord_7174927).sum := by decide
  have hdescent : baseEnd_7174927 < baseStart_7174927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174945 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7174945 : Nat := 118140960795 + 7174945 * 2 ^ 59
def prefixEnd_7174945 : Nat := 4983230072969 + 3 ^ 40 * 7174945 * 2
def baseEnd_7174945 : Nat := 3684195454573535728390535

theorem tailTrace_7174945 : CollatzResearch.WordTrace tailWord_7174945 prefixEnd_7174945 3684195454573535728390535 := by
  unfold tailWord_7174945
  simp only [CollatzResearch.WordTrace]
  refine ⟨261691742991407122893382289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174461161994271415262254859 261691742991407122893382289)
  ·
    refine ⟨196268807243555342170036717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261691742991407122893382289 196268807243555342170036717)
    ·
      refine ⟨73600802716333253313763769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196268807243555342170036717 73600802716333253313763769)
      ·
        refine ⟨55200602037249939985322827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73600802716333253313763769 55200602037249939985322827)
        ·
          refine ⟨82800903055874909977984241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55200602037249939985322827 82800903055874909977984241)
          ·
            refine ⟨62100677291906182483488181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82800903055874909977984241 62100677291906182483488181)
            ·
              refine ⟨5821938496116204607827017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62100677291906182483488181 5821938496116204607827017)
              ·
                refine ⟨4366453872087153455870263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821938496116204607827017 4366453872087153455870263)
                ·
                  refine ⟨6549680808130730183805395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366453872087153455870263 6549680808130730183805395)
                  ·
                    refine ⟨9824521212196095275708093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549680808130730183805395 9824521212196095275708093)
                    ·
                      refine ⟨3684195454573535728390535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824521212196095275708093 3684195454573535728390535)
                      ·
                        rfl

theorem cell23_7174945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7174945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174945 prefixEnd_7174945 := by exact prefixLift 7174945
  have htrace : WordTrace (prefixWord ++ tailWord_7174945) baseStart_7174945 baseEnd_7174945 := by
    simpa [prefixWord, tailWord_7174945, baseEnd_7174945] using wordTrace_append hprefix tailTrace_7174945
  have hstable : (prefixWord ++ tailWord_7174945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174945).length < 2 ^ (prefixWord ++ tailWord_7174945).sum := by decide
  have hdescent : baseEnd_7174945 < baseStart_7174945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174961 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_7174961 : Nat := 118140960795 + 7174961 * 2 ^ 59
def prefixEnd_7174961 : Nat := 4983230072969 + 3 ^ 40 * 7174961 * 2
def baseEnd_7174961 : Nat := 1228067890088002555263487

theorem tailTrace_7174961 : CollatzResearch.WordTrace tailWord_7174961 prefixEnd_7174961 1228067890088002555263487 := by
  unfold tailWord_7174961
  simp only [CollatzResearch.WordTrace]
  refine ⟨261692326559349157625964737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174461551039566105083976491 261692326559349157625964737)
  ·
    refine ⟨196269244919511868219473553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261692326559349157625964737 196269244919511868219473553)
    ·
      refine ⟨147201933689633901164605165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196269244919511868219473553 147201933689633901164605165)
      ·
        refine ⟨55200725133612712936726937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147201933689633901164605165 55200725133612712936726937)
        ·
          refine ⟨41400543850209534702545203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55200725133612712936726937 41400543850209534702545203)
          ·
            refine ⟨62100815775314302053817805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41400543850209534702545203 62100815775314302053817805)
            ·
              refine ⟨23287805915742863270181677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62100815775314302053817805 23287805915742863270181677)
              ·
                refine ⟨8732927218403573726318129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23287805915742863270181677 8732927218403573726318129)
                ·
                  refine ⟨6549695413802680294738597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732927218403573726318129 6549695413802680294738597)
                  ·
                    refine ⟨1228067890088002555263487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549695413802680294738597 1228067890088002555263487)
                    ·
                      rfl

theorem cell23_7174961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_7174961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174961 prefixEnd_7174961 := by exact prefixLift 7174961
  have htrace : WordTrace (prefixWord ++ tailWord_7174961) baseStart_7174961 baseEnd_7174961 := by
    simpa [prefixWord, tailWord_7174961, baseEnd_7174961] using wordTrace_append hprefix tailTrace_7174961
  have hstable : (prefixWord ++ tailWord_7174961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174961).length < 2 ^ (prefixWord ++ tailWord_7174961).sum := by decide
  have hdescent : baseEnd_7174961 < baseStart_7174961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174982 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7174982 : Nat := 118140960795 + 7174982 * 2 ^ 59
def prefixEnd_7174982 : Nat := 4983230072969 + 3 ^ 40 * 7174982 * 2
def baseEnd_7174982 : Nat := 1228071484452584027875955

theorem tailTrace_7174982 : CollatzResearch.WordTrace tailWord_7174982 prefixEnd_7174982 1228071484452584027875955 := by
  unfold tailWord_7174982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177909140383533694139975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174462061661515385474986133 8177909140383533694139975)
  ·
    refine ⟨12266863710575300541209963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8177909140383533694139975 12266863710575300541209963)
    ·
      refine ⟨18400295565862950811814945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12266863710575300541209963 18400295565862950811814945)
      ·
        refine ⟨13800221674397213108861209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18400295565862950811814945 13800221674397213108861209)
        ·
          refine ⟨10350166255797909831645907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13800221674397213108861209 10350166255797909831645907)
          ·
            refine ⟨15525249383696864747468861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350166255797909831645907 15525249383696864747468861)
            ·
              refine ⟨5821968518886324280300823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15525249383696864747468861 5821968518886324280300823)
              ·
                refine ⟨8732952778329486420451235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821968518886324280300823 8732952778329486420451235)
                ·
                  refine ⟨13099429167494229630676853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8732952778329486420451235 13099429167494229630676853)
                  ·
                    refine ⟨1228071484452584027875955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13099429167494229630676853 1228071484452584027875955)
                    ·
                      rfl

theorem cell23_7174982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7174982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174982 prefixEnd_7174982 := by exact prefixLift 7174982
  have htrace : WordTrace (prefixWord ++ tailWord_7174982) baseStart_7174982 baseEnd_7174982 := by
    simpa [prefixWord, tailWord_7174982, baseEnd_7174982] using wordTrace_append hprefix tailTrace_7174982
  have hstable : (prefixWord ++ tailWord_7174982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174982).length < 2 ^ (prefixWord ++ tailWord_7174982).sum := by decide
  have hdescent : baseEnd_7174982 < baseStart_7174982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7174987 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 7]
def baseStart_7174987 : Nat := 118140960795 + 7174987 * 2 ^ 59
def prefixEnd_7174987 : Nat := 4983230072969 + 3 ^ 40 * 7174987 * 2
def baseEnd_7174987 : Nat := 1228072340253674854688447

theorem tailTrace_7174987 : CollatzResearch.WordTrace tailWord_7174987 prefixEnd_7174987 1228072340253674854688447 := by
  unfold tailWord_7174987
  simp only [CollatzResearch.WordTrace]
  refine ⟨261693274857254964066411215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174462183238169976044274143 261693274857254964066411215)
  ·
    refine ⟨392539912285882446099616823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261693274857254964066411215 392539912285882446099616823)
    ·
      refine ⟨588809868428823669149425235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392539912285882446099616823 588809868428823669149425235)
      ·
        refine ⟨883214802643235503724137853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588809868428823669149425235 883214802643235503724137853)
        ·
          refine ⟨331205550991213313896551695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 883214802643235503724137853 331205550991213313896551695)
          ·
            refine ⟨496808326486819970844827543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331205550991213313896551695 496808326486819970844827543)
            ·
              refine ⟨745212489730229956267241315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496808326486819970844827543 745212489730229956267241315)
              ·
                refine ⟨1117818734595344934400861973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745212489730229956267241315 1117818734595344934400861973)
                ·
                  refine ⟨52397753184156793800040405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1117818734595344934400861973 52397753184156793800040405)
                  ·
                    refine ⟨1228072340253674854688447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52397753184156793800040405 1228072340253674854688447)
                    ·
                      rfl

theorem cell23_7174987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_7174987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7174987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7174987 prefixEnd_7174987 := by exact prefixLift 7174987
  have htrace : WordTrace (prefixWord ++ tailWord_7174987) baseStart_7174987 baseEnd_7174987 := by
    simpa [prefixWord, tailWord_7174987, baseEnd_7174987] using wordTrace_append hprefix tailTrace_7174987
  have hstable : (prefixWord ++ tailWord_7174987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7174987).length < 2 ^ (prefixWord ++ tailWord_7174987).sum := by decide
  have hdescent : baseEnd_7174987 < baseStart_7174987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7174987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175002 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_7175002 : Nat := 118140960795 + 7175002 * 2 ^ 59
def prefixEnd_7175002 : Nat := 4983230072969 + 3 ^ 40 * 7175002 * 2
def baseEnd_7175002 : Nat := 3684224722970842005377773

theorem tailTrace_7175002 : CollatzResearch.WordTrace tailWord_7175002 prefixEnd_7175002 3684224722970842005377773 := by
  unfold tailWord_7175002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65423455488050155407051815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174462547968133747752138173 65423455488050155407051815)
  ·
    refine ⟨98135183232075233110577723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65423455488050155407051815 98135183232075233110577723)
    ·
      refine ⟨147202774848112849665866585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98135183232075233110577723 147202774848112849665866585)
      ·
        refine ⟨110402081136084637249399939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147202774848112849665866585 110402081136084637249399939)
        ·
          refine ⟨165603121704126955874099909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110402081136084637249399939 165603121704126955874099909)
          ·
            refine ⟨31050585319523804226393733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165603121704126955874099909 31050585319523804226393733)
            ·
              refine ⟨5821984747410713292448825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31050585319523804226393733 5821984747410713292448825)
              ·
                refine ⟨4366488560558034969336619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821984747410713292448825 4366488560558034969336619)
                ·
                  refine ⟨6549732840837052454004929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366488560558034969336619 6549732840837052454004929)
                  ·
                    refine ⟨4912299630627789340503697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549732840837052454004929 4912299630627789340503697)
                    ·
                      refine ⟨3684224722970842005377773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912299630627789340503697 3684224722970842005377773)
                      ·
                        rfl

theorem cell23_7175002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_7175002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175002 prefixEnd_7175002 := by exact prefixLift 7175002
  have htrace : WordTrace (prefixWord ++ tailWord_7175002) baseStart_7175002 baseEnd_7175002 := by
    simpa [prefixWord, tailWord_7175002, baseEnd_7175002] using wordTrace_append hprefix tailTrace_7175002
  have hstable : (prefixWord ++ tailWord_7175002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175002).length < 2 ^ (prefixWord ++ tailWord_7175002).sum := by decide
  have hdescent : baseEnd_7175002 < baseStart_7175002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
