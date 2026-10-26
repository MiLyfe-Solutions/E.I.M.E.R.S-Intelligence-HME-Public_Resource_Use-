import V185TrunkScan23Chunk1354

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8024349 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_8024349 : Nat := 118140960795 + 8024349 * 2 ^ 59
def prefixEnd_8024349 : Nat := 4983230072969 + 3 ^ 40 * 8024349 * 2
def baseEnd_8024349 : Nat := 1373449325475043477111399

theorem tailTrace_8024349 : CollatzResearch.WordTrace tailWord_8024349 prefixEnd_8024349 1373449325475043477111399 := by
  unfold tailWord_8024349
  simp only [CollatzResearch.WordTrace]
  refine ⟨292672052006161497547236101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195114701337440998364824067 292672052006161497547236101)
  ·
    refine ⟨54876009751155280790106769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292672052006161497547236101 54876009751155280790106769)
    ·
      refine ⟨41157007313366460592580077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54876009751155280790106769 41157007313366460592580077)
      ·
        refine ⟨15433877742512422722217529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41157007313366460592580077 15433877742512422722217529)
        ·
          refine ⟨11575408306884317041663147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15433877742512422722217529 11575408306884317041663147)
          ·
            refine ⟨17363112460326475562494721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575408306884317041663147 17363112460326475562494721)
            ·
              refine ⟨13022334345244856671871041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17363112460326475562494721 13022334345244856671871041)
              ·
                refine ⟨9766750758933642503903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13022334345244856671871041 9766750758933642503903281)
                ·
                  refine ⟨7325063069200231877927461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766750758933642503903281 7325063069200231877927461)
                  ·
                    refine ⟨1373449325475043477111399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325063069200231877927461 1373449325475043477111399)
                    ·
                      rfl

theorem cell23_8024349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_8024349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024349 prefixEnd_8024349 := by exact prefixLift 8024349
  have htrace : WordTrace (prefixWord ++ tailWord_8024349) baseStart_8024349 baseEnd_8024349 := by
    simpa [prefixWord, tailWord_8024349, baseEnd_8024349] using wordTrace_append hprefix tailTrace_8024349
  have hstable : (prefixWord ++ tailWord_8024349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024349).length < 2 ^ (prefixWord ++ tailWord_8024349).sum := by decide
  have hdescent : baseEnd_8024349 < baseStart_8024349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024350 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_8024350 : Nat := 118140960795 + 8024350 * 2 ^ 59
def prefixEnd_8024350 : Nat := 4983230072969 + 3 ^ 40 * 8024350 * 2
def baseEnd_8024350 : Nat := 4120348489905784927421693

theorem tailTrace_8024350 : CollatzResearch.WordTrace tailWord_8024350 prefixEnd_8024350 4120348489905784927421693 := by
  unfold tailWord_8024350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584011059894734339752813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195114725652771916478681669 36584011059894734339752813)
  ·
    refine ⟨13719004147460525377407305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36584011059894734339752813 13719004147460525377407305)
    ·
      refine ⟨10289253110595394033055479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13719004147460525377407305 10289253110595394033055479)
      ·
        refine ⟨15433879665893091049583219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10289253110595394033055479 15433879665893091049583219)
        ·
          refine ⟨23150819498839636574374829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15433879665893091049583219 23150819498839636574374829)
          ·
            refine ⟨8681557312064863715390561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23150819498839636574374829 8681557312064863715390561)
            ·
              refine ⟨6511167984048647786542921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681557312064863715390561 6511167984048647786542921)
              ·
                refine ⟨4883375988036485839907191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511167984048647786542921 4883375988036485839907191)
                ·
                  refine ⟨7325063982054728759860787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883375988036485839907191 7325063982054728759860787)
                  ·
                    refine ⟨10987595973082093139791181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325063982054728759860787 10987595973082093139791181)
                    ·
                      refine ⟨4120348489905784927421693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987595973082093139791181 4120348489905784927421693)
                      ·
                        rfl

theorem cell23_8024350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_8024350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024350 prefixEnd_8024350 := by exact prefixLift 8024350
  have htrace : WordTrace (prefixWord ++ tailWord_8024350) baseStart_8024350 baseEnd_8024350 := by
    simpa [prefixWord, tailWord_8024350, baseEnd_8024350] using wordTrace_append hprefix tailTrace_8024350
  have hstable : (prefixWord ++ tailWord_8024350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024350).length < 2 ^ (prefixWord ++ tailWord_8024350).sum := by decide
  have hdescent : baseEnd_8024350 < baseStart_8024350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024356 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_8024356 : Nat := 118140960795 + 8024356 * 2 ^ 59
def prefixEnd_8024356 : Nat := 4983230072969 + 3 ^ 40 * 8024356 * 2
def baseEnd_8024356 : Nat := 4120351570789711903946665

theorem tailTrace_8024356 : CollatzResearch.WordTrace tailWord_8024356 prefixEnd_8024356 4120351570789711903946665 := by
  unfold tailWord_8024356
  simp only [CollatzResearch.WordTrace]
  refine ⟨146336153658568068871370461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195114871544757425161827281 146336153658568068871370461)
  ·
    refine ⟨54876057621963025826763923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146336153658568068871370461 54876057621963025826763923)
    ·
      refine ⟨82314086432944538740145885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54876057621963025826763923 82314086432944538740145885)
      ·
        refine ⟨30867782412354202027554707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82314086432944538740145885 30867782412354202027554707)
        ·
          refine ⟨46301673618531303041332061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30867782412354202027554707 46301673618531303041332061)
          ·
            refine ⟨17363127606949238640499523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46301673618531303041332061 17363127606949238640499523)
            ·
              refine ⟨26044691410423857960749285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17363127606949238640499523 26044691410423857960749285)
              ·
                refine ⟨4883379639454473367640491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26044691410423857960749285 4883379639454473367640491)
                ·
                  refine ⟨7325069459181710051460737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883379639454473367640491 7325069459181710051460737)
                  ·
                    refine ⟨5493802094386282538595553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325069459181710051460737 5493802094386282538595553)
                    ·
                      refine ⟨4120351570789711903946665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493802094386282538595553 4120351570789711903946665)
                      ·
                        rfl

theorem cell23_8024356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_8024356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024356 prefixEnd_8024356 := by exact prefixLift 8024356
  have htrace : WordTrace (prefixWord ++ tailWord_8024356) baseStart_8024356 baseEnd_8024356 := by
    simpa [prefixWord, tailWord_8024356, baseEnd_8024356] using wordTrace_append hprefix tailTrace_8024356
  have hstable : (prefixWord ++ tailWord_8024356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024356).length < 2 ^ (prefixWord ++ tailWord_8024356).sum := by decide
  have hdescent : baseEnd_8024356 < baseStart_8024356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024362 : List Nat := [3, 1, 4, 2, 2, 2, 1, 8]
def baseStart_8024362 : Nat := 118140960795 + 8024362 * 2 ^ 59
def prefixEnd_8024362 : Nat := 4983230072969 + 3 ^ 40 * 8024362 * 2
def baseEnd_8024362 : Nat := 152605727839764402980431

theorem tailTrace_8024362 : CollatzResearch.WordTrace tailWord_8024362 prefixEnd_8024362 152605727839764402980431 := by
  unfold tailWord_8024362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73168131538778600191864835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195115017436742933844972893 73168131538778600191864835)
  ·
    refine ⟨109752197308167900287797253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73168131538778600191864835 109752197308167900287797253)
    ·
      refine ⟨20578536995281481303961985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109752197308167900287797253 20578536995281481303961985)
      ·
        refine ⟨15433902746461110977971489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20578536995281481303961985 15433902746461110977971489)
        ·
          refine ⟨11575427059845833233478617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15433902746461110977971489 11575427059845833233478617)
          ·
            refine ⟨8681570294884374925108963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575427059845833233478617 8681570294884374925108963)
            ·
              refine ⟨13022355442326562387663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681570294884374925108963 13022355442326562387663445)
              ·
                refine ⟨152605727839764402980431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13022355442326562387663445 152605727839764402980431)
                ·
                  rfl

theorem cell23_8024362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_8024362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024362 prefixEnd_8024362 := by exact prefixLift 8024362
  have htrace : WordTrace (prefixWord ++ tailWord_8024362) baseStart_8024362 baseEnd_8024362 := by
    simpa [prefixWord, tailWord_8024362, baseEnd_8024362] using wordTrace_append hprefix tailTrace_8024362
  have hstable : (prefixWord ++ tailWord_8024362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024362).length < 2 ^ (prefixWord ++ tailWord_8024362).sum := by decide
  have hdescent : baseEnd_8024362 < baseStart_8024362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024372 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_8024372 : Nat := 118140960795 + 8024372 * 2 ^ 59
def prefixEnd_8024372 : Nat := 4983230072969 + 3 ^ 40 * 8024372 * 2
def baseEnd_8024372 : Nat := 4120359786480183841346591

theorem tailTrace_8024372 : CollatzResearch.WordTrace tailWord_8024372 prefixEnd_8024372 4120359786480183841346591 := by
  unfold tailWord_8024372
  simp only [CollatzResearch.WordTrace]
  refine ⟨146336445442539086237661685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195115260590052114983548913 146336445442539086237661685)
  ·
    refine ⟨13719041760238039334780783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146336445442539086237661685 13719041760238039334780783)
    ·
      refine ⟨20578562640357059002171175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719041760238039334780783 20578562640357059002171175)
      ·
        refine ⟨30867843960535588503256763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20578562640357059002171175 30867843960535588503256763)
        ·
          refine ⟨46301765940803382754885145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30867843960535588503256763 46301765940803382754885145)
          ·
            refine ⟨34726324455602537066163859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46301765940803382754885145 34726324455602537066163859)
            ·
              refine ⟨52089486683403805599245789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34726324455602537066163859 52089486683403805599245789)
              ·
                refine ⟨19533557506276427099717171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52089486683403805599245789 19533557506276427099717171)
                ·
                  refine ⟨29300336259414640649575757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19533557506276427099717171 29300336259414640649575757)
                  ·
                    refine ⟨10987626097280490243590909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29300336259414640649575757 10987626097280490243590909)
                    ·
                      refine ⟨4120359786480183841346591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987626097280490243590909 4120359786480183841346591)
                      ·
                        rfl

theorem cell23_8024372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_8024372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024372 prefixEnd_8024372 := by exact prefixLift 8024372
  have htrace : WordTrace (prefixWord ++ tailWord_8024372) baseStart_8024372 baseEnd_8024372 := by
    simpa [prefixWord, tailWord_8024372, baseEnd_8024372] using wordTrace_append hprefix tailTrace_8024372
  have hstable : (prefixWord ++ tailWord_8024372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024372).length < 2 ^ (prefixWord ++ tailWord_8024372).sum := by decide
  have hdescent : baseEnd_8024372 < baseStart_8024372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024395 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 4, 2]
def baseStart_8024395 : Nat := 118140960795 + 8024395 * 2 ^ 59
def prefixEnd_8024395 : Nat := 4983230072969 + 3 ^ 40 * 8024395 * 2
def baseEnd_8024395 : Nat := 4120371596535237251358985

theorem tailTrace_8024395 : CollatzResearch.WordTrace tailWord_8024395 prefixEnd_8024395 4120371596535237251358985 := by
  unfold tailWord_8024395
  simp only [CollatzResearch.WordTrace]
  refine ⟨292673729763994847403410639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195115819842663231602273759 292673729763994847403410639)
  ·
    refine ⟨439010594645992271105115959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292673729763994847403410639 439010594645992271105115959)
    ·
      refine ⟨658515891968988406657673939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439010594645992271105115959 658515891968988406657673939)
      ·
        refine ⟨987773837953482609986510909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658515891968988406657673939 987773837953482609986510909)
        ·
          refine ⟨370415189232555978744941591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987773837953482609986510909 370415189232555978744941591)
          ·
            refine ⟨555622783848833968117412387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370415189232555978744941591 555622783848833968117412387)
            ·
              refine ⟨833434175773250952176118581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555622783848833968117412387 833434175773250952176118581)
              ·
                refine ⟨78134453978742276766511117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833434175773250952176118581 78134453978742276766511117)
                ·
                  refine ⟨29300420242028353787441669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78134453978742276766511117 29300420242028353787441669)
                  ·
                    refine ⟨5493828795380316335145313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29300420242028353787441669 5493828795380316335145313)
                    ·
                      refine ⟨4120371596535237251358985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493828795380316335145313 4120371596535237251358985)
                      ·
                        rfl

theorem cell23_8024395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4, 2].length) (baseStart_8024395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024395 prefixEnd_8024395 := by exact prefixLift 8024395
  have htrace : WordTrace (prefixWord ++ tailWord_8024395) baseStart_8024395 baseEnd_8024395 := by
    simpa [prefixWord, tailWord_8024395, baseEnd_8024395] using wordTrace_append hprefix tailTrace_8024395
  have hstable : (prefixWord ++ tailWord_8024395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024395).length < 2 ^ (prefixWord ++ tailWord_8024395).sum := by decide
  have hdescent : baseEnd_8024395 < baseStart_8024395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024485 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_8024485 : Nat := 118140960795 + 8024485 * 2 ^ 59
def prefixEnd_8024485 : Nat := 4983230072969 + 3 ^ 40 * 8024485 * 2
def baseEnd_8024485 : Nat := 4120417809794141899233571

theorem tailTrace_8024485 : CollatzResearch.WordTrace tailWord_8024485 prefixEnd_8024485 4120417809794141899233571 := by
  unfold tailWord_8024485
  simp only [CollatzResearch.WordTrace]
  refine ⟨292677012333668792774186909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195118008222445861849457939 292677012333668792774186909)
  ·
    refine ⟨109753879625125797290320091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292677012333668792774186909 109753879625125797290320091)
    ·
      refine ⟨164630819437688695935480137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109753879625125797290320091 164630819437688695935480137)
      ·
        refine ⟨123473114578266521951610103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164630819437688695935480137 123473114578266521951610103)
        ·
          refine ⟨185209671867399782927415155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123473114578266521951610103 185209671867399782927415155)
          ·
            refine ⟨277814507801099674391122733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185209671867399782927415155 277814507801099674391122733)
            ·
              refine ⟨104180440425412377896671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277814507801099674391122733 104180440425412377896671025)
              ·
                refine ⟨78135330319059283422503269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104180440425412377896671025 78135330319059283422503269)
                ·
                  refine ⟨14650374434823615641719363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78135330319059283422503269 14650374434823615641719363)
                  ·
                    refine ⟨21975561652235423462579045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14650374434823615641719363 21975561652235423462579045)
                    ·
                      refine ⟨4120417809794141899233571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21975561652235423462579045 4120417809794141899233571)
                      ·
                        rfl

theorem cell23_8024485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_8024485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024485 prefixEnd_8024485 := by exact prefixLift 8024485
  have htrace : WordTrace (prefixWord ++ tailWord_8024485) baseStart_8024485 baseEnd_8024485 := by
    simpa [prefixWord, tailWord_8024485, baseEnd_8024485] using wordTrace_append hprefix tailTrace_8024485
  have hstable : (prefixWord ++ tailWord_8024485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024485).length < 2 ^ (prefixWord ++ tailWord_8024485).sum := by decide
  have hdescent : baseEnd_8024485 < baseStart_8024485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024522 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_8024522 : Nat := 118140960795 + 8024522 * 2 ^ 59
def prefixEnd_8024522 : Nat := 4983230072969 + 3 ^ 40 * 8024522 * 2
def baseEnd_8024522 : Nat := 4120436808578358254470901

theorem tailTrace_8024522 : CollatzResearch.WordTrace tailWord_8024522 prefixEnd_8024522 4120436808578358254470901 := by
  unfold tailWord_8024522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73169590458633687023320955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195118907889689832062189213 73169590458633687023320955)
  ·
    refine ⟨109754385687950530534981433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73169590458633687023320955 109754385687950530534981433)
    ·
      refine ⟨82315789265962897901236075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109754385687950530534981433 82315789265962897901236075)
      ·
        refine ⟨123473683898944346851854113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82315789265962897901236075 123473683898944346851854113)
        ·
          refine ⟨92605262924208260138890585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123473683898944346851854113 92605262924208260138890585)
          ·
            refine ⟨69453947193156195104167939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92605262924208260138890585 69453947193156195104167939)
            ·
              refine ⟨104180920789734292656251909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69453947193156195104167939 104180920789734292656251909)
              ·
                refine ⟨19533922648075179873047233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104180920789734292656251909 19533922648075179873047233)
                ·
                  refine ⟨14650441986056384904785425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19533922648075179873047233 14650441986056384904785425)
                  ·
                    refine ⟨10987831489542288678589069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14650441986056384904785425 10987831489542288678589069)
                    ·
                      refine ⟨4120436808578358254470901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987831489542288678589069 4120436808578358254470901)
                      ·
                        rfl

theorem cell23_8024522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_8024522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024522 prefixEnd_8024522 := by exact prefixLift 8024522
  have htrace : WordTrace (prefixWord ++ tailWord_8024522) baseStart_8024522 baseEnd_8024522 := by
    simpa [prefixWord, tailWord_8024522, baseEnd_8024522] using wordTrace_append hprefix tailTrace_8024522
  have hstable : (prefixWord ++ tailWord_8024522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024522).length < 2 ^ (prefixWord ++ tailWord_8024522).sum := by decide
  have hdescent : baseEnd_8024522 < baseStart_8024522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024535 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_8024535 : Nat := 118140960795 + 8024535 * 2 ^ 59
def prefixEnd_8024535 : Nat := 4983230072969 + 3 ^ 40 * 8024535 * 2
def baseEnd_8024535 : Nat := 4120443483826866703608341

theorem tailTrace_8024535 : CollatzResearch.WordTrace tailWord_8024535 prefixEnd_8024535 4120443483826866703608341 := by
  unfold tailWord_8024535
  simp only [CollatzResearch.WordTrace]
  refine ⟨292678835983487651313507059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195119223988991767542338039 292678835983487651313507059)
  ·
    refine ⟨439018253975231476970260589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292678835983487651313507059 439018253975231476970260589)
    ·
      refine ⟨164631845240711803863847721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439018253975231476970260589 164631845240711803863847721)
      ·
        refine ⟨123473883930533852897885791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164631845240711803863847721 123473883930533852897885791)
        ·
          refine ⟨185210825895800779346828687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123473883930533852897885791 185210825895800779346828687)
          ·
            refine ⟨277816238843701169020243031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185210825895800779346828687 277816238843701169020243031)
            ·
              refine ⟨416724358265551753530364547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277816238843701169020243031 416724358265551753530364547)
              ·
                refine ⟨625086537398327630295546821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416724358265551753530364547 625086537398327630295546821)
                ·
                  refine ⟨117203725762186430680415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625086537398327630295546821 117203725762186430680415029)
                  ·
                    refine ⟨10987849290204977876288909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117203725762186430680415029 10987849290204977876288909)
                    ·
                      refine ⟨4120443483826866703608341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987849290204977876288909 4120443483826866703608341)
                      ·
                        rfl

theorem cell23_8024535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_8024535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024535 prefixEnd_8024535 := by exact prefixLift 8024535
  have htrace : WordTrace (prefixWord ++ tailWord_8024535) baseStart_8024535 baseEnd_8024535 := by
    simpa [prefixWord, tailWord_8024535, baseEnd_8024535] using wordTrace_append hprefix tailTrace_8024535
  have hstable : (prefixWord ++ tailWord_8024535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024535).length < 2 ^ (prefixWord ++ tailWord_8024535).sum := by decide
  have hdescent : baseEnd_8024535 < baseStart_8024535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024555 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 3, 5]
def baseStart_8024555 : Nat := 118140960795 + 8024555 * 2 ^ 59
def prefixEnd_8024555 : Nat := 4983230072969 + 3 ^ 40 * 8024555 * 2
def baseEnd_8024555 : Nat := 1373484584479985541786083

theorem tailTrace_8024555 : CollatzResearch.WordTrace tailWord_8024555 prefixEnd_8024555 1373484584479985541786083 := by
  unfold tailWord_8024555
  simp only [CollatzResearch.WordTrace]
  refine ⟨292679565443415194729235119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195119710295610129819490079 292679565443415194729235119)
  ·
    refine ⟨439019348165122792093852679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292679565443415194729235119 439019348165122792093852679)
    ·
      refine ⟨658529022247684188140779019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439019348165122792093852679 658529022247684188140779019)
      ·
        refine ⟨987793533371526282211168529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658529022247684188140779019 987793533371526282211168529)
        ·
          refine ⟨740845150028644711658376397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987793533371526282211168529 740845150028644711658376397)
          ·
            refine ⟨277816931260741766871891149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740845150028644711658376397 277816931260741766871891149)
            ·
              refine ⟨104181349222778162576959181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277816931260741766871891149 104181349222778162576959181)
              ·
                refine ⟨39068005958541810966359693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104181349222778162576959181 39068005958541810966359693)
                ·
                  refine ⟨14650502234453179112384885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39068005958541810966359693 14650502234453179112384885)
                  ·
                    refine ⟨1373484584479985541786083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14650502234453179112384885 1373484584479985541786083)
                    ·
                      rfl

theorem cell23_8024555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].length) (baseStart_8024555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024555 prefixEnd_8024555 := by exact prefixLift 8024555
  have htrace : WordTrace (prefixWord ++ tailWord_8024555) baseStart_8024555 baseEnd_8024555 := by
    simpa [prefixWord, tailWord_8024555, baseEnd_8024555] using wordTrace_append hprefix tailTrace_8024555
  have hstable : (prefixWord ++ tailWord_8024555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024555).length < 2 ^ (prefixWord ++ tailWord_8024555).sum := by decide
  have hdescent : baseEnd_8024555 < baseStart_8024555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024586 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_8024586 : Nat := 118140960795 + 8024586 * 2 ^ 59
def prefixEnd_8024586 : Nat := 4983230072969 + 3 ^ 40 * 8024586 * 2
def baseEnd_8024586 : Nat := 4120469671340246004070607

theorem tailTrace_8024586 : CollatzResearch.WordTrace tailWord_8024586 prefixEnd_8024586 4120469671340246004070607 := by
  unfold tailWord_8024586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73170174026575721755903403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195120464070868591349075741 73170174026575721755903403)
  ·
    refine ⟨109755261039863582633855105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73170174026575721755903403 109755261039863582633855105)
    ·
      refine ⟨82316445779897686975391329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109755261039863582633855105 82316445779897686975391329)
      ·
        refine ⟨61737334334923265231543497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82316445779897686975391329 61737334334923265231543497)
        ·
          refine ⟨46303000751192448923657623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61737334334923265231543497 46303000751192448923657623)
          ·
            refine ⟨69454501126788673385486435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46303000751192448923657623 69454501126788673385486435)
            ·
              refine ⟨104181751690183010078229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69454501126788673385486435 104181751690183010078229653)
              ·
                refine ⟨4883519610477328597417015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104181751690183010078229653 4883519610477328597417015)
                ·
                  refine ⟨7325279415715992896125523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883519610477328597417015 7325279415715992896125523)
                  ·
                    refine ⟨10987919123573989344188285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325279415715992896125523 10987919123573989344188285)
                    ·
                      refine ⟨4120469671340246004070607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987919123573989344188285 4120469671340246004070607)
                      ·
                        rfl

theorem cell23_8024586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_8024586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024586 prefixEnd_8024586 := by exact prefixLift 8024586
  have htrace : WordTrace (prefixWord ++ tailWord_8024586) baseStart_8024586 baseEnd_8024586 := by
    simpa [prefixWord, tailWord_8024586, baseEnd_8024586] using wordTrace_append hprefix tailTrace_8024586
  have hstable : (prefixWord ++ tailWord_8024586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024586).length < 2 ^ (prefixWord ++ tailWord_8024586).sum := by decide
  have hdescent : baseEnd_8024586 < baseStart_8024586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024596 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_8024596 : Nat := 118140960795 + 8024596 * 2 ^ 59
def prefixEnd_8024596 : Nat := 4983230072969 + 3 ^ 40 * 8024596 * 2
def baseEnd_8024596 : Nat := 4120474806146790964945561

theorem tailTrace_8024596 : CollatzResearch.WordTrace tailWord_8024596 prefixEnd_8024596 4120474806146790964945561 := by
  unfold tailWord_8024596
  simp only [CollatzResearch.WordTrace]
  refine ⟨146340530418133329365738821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195120707224177772487651761 146340530418133329365738821)
  ·
    refine ⟨27438849453399999256076029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146340530418133329365738821 27438849453399999256076029)
    ·
      refine ⟨10289568545024999721028511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27438849453399999256076029 10289568545024999721028511)
      ·
        refine ⟨15434352817537499581542767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10289568545024999721028511 15434352817537499581542767)
        ·
          refine ⟨23151529226306249372314151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15434352817537499581542767 23151529226306249372314151)
          ·
            refine ⟨34727293839459374058471227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23151529226306249372314151 34727293839459374058471227)
            ·
              refine ⟨52090940759189061087706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34727293839459374058471227 52090940759189061087706841)
              ·
                refine ⟨39068205569391795815780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52090940759189061087706841 39068205569391795815780131)
                ·
                  refine ⟨58602308354087693723670197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39068205569391795815780131 58602308354087693723670197)
                  ·
                    refine ⟨5493966408195721286594081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58602308354087693723670197 5493966408195721286594081)
                    ·
                      refine ⟨4120474806146790964945561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493966408195721286594081 4120474806146790964945561)
                      ·
                        rfl

theorem cell23_8024596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_8024596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024596 prefixEnd_8024596 := by exact prefixLift 8024596
  have htrace : WordTrace (prefixWord ++ tailWord_8024596) baseStart_8024596 baseEnd_8024596 := by
    simpa [prefixWord, tailWord_8024596, baseEnd_8024596] using wordTrace_append hprefix tailTrace_8024596
  have hstable : (prefixWord ++ tailWord_8024596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024596).length < 2 ^ (prefixWord ++ tailWord_8024596).sum := by decide
  have hdescent : baseEnd_8024596 < baseStart_8024596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024602 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_8024602 : Nat := 118140960795 + 8024602 * 2 ^ 59
def prefixEnd_8024602 : Nat := 4983230072969 + 3 ^ 40 * 8024602 * 2
def baseEnd_8024602 : Nat := 1373492629010239313823511

theorem tailTrace_8024602 : CollatzResearch.WordTrace tailWord_8024602 prefixEnd_8024602 1373492629010239313823511 := by
  unfold tailWord_8024602
  simp only [CollatzResearch.WordTrace]
  refine ⟨73170319918561230439049015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195120853116163281170797373 73170319918561230439049015)
  ·
    refine ⟨109755479877841845658573523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73170319918561230439049015 109755479877841845658573523)
    ·
      refine ⟨164633219816762768487860285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109755479877841845658573523 164633219816762768487860285)
      ·
        refine ⟨61737457431286038182947607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164633219816762768487860285 61737457431286038182947607)
        ·
          refine ⟨92606186146929057274421411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61737457431286038182947607 92606186146929057274421411)
          ·
            refine ⟨138909279220393585911632117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92606186146929057274421411 138909279220393585911632117)
            ·
              refine ⟨13022744926911898679215511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138909279220393585911632117 13022744926911898679215511)
              ·
                refine ⟨19534117390367848018823267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13022744926911898679215511 19534117390367848018823267)
                ·
                  refine ⟨29301176085551772028234901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19534117390367848018823267 29301176085551772028234901)
                  ·
                    refine ⟨1373492629010239313823511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29301176085551772028234901 1373492629010239313823511)
                    ·
                      rfl

theorem cell23_8024602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_8024602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024602 prefixEnd_8024602 := by exact prefixLift 8024602
  have htrace : WordTrace (prefixWord ++ tailWord_8024602) baseStart_8024602 baseEnd_8024602 := by
    simpa [prefixWord, tailWord_8024602, baseEnd_8024602] using wordTrace_append hprefix tailTrace_8024602
  have hstable : (prefixWord ++ tailWord_8024602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024602).length < 2 ^ (prefixWord ++ tailWord_8024602).sum := by decide
  have hdescent : baseEnd_8024602 < baseStart_8024602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024609 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_8024609 : Nat := 118140960795 + 8024609 * 2 ^ 59
def prefixEnd_8024609 : Nat := 4983230072969 + 3 ^ 40 * 8024609 * 2
def baseEnd_8024609 : Nat := 4120481481395299414083001

theorem tailTrace_8024609 : CollatzResearch.WordTrace tailWord_8024609 prefixEnd_8024609 4120481481395299414083001 := by
  unfold tailWord_8024609
  simp only [CollatzResearch.WordTrace]
  refine ⟨292681534985219561951700881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195121023323479707967800587 292681534985219561951700881)
  ·
    refine ⟨219511151238914671463775661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292681534985219561951700881 219511151238914671463775661)
    ·
      refine ⟨82316681714593001798915873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219511151238914671463775661 82316681714593001798915873)
      ·
        refine ⟨61737511285944751349186905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82316681714593001798915873 61737511285944751349186905)
        ·
          refine ⟨46303133464458563511890179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61737511285944751349186905 46303133464458563511890179)
          ·
            refine ⟨69454700196687845267835269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46303133464458563511890179 69454700196687845267835269)
            ·
              refine ⟨13022756286878970987719113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69454700196687845267835269 13022756286878970987719113)
              ·
                refine ⟨9767067215159228240789335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13022756286878970987719113 9767067215159228240789335)
                ·
                  refine ⟨14650600822738842361184003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767067215159228240789335 14650600822738842361184003)
                  ·
                    refine ⟨21975901234108263541776005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14650600822738842361184003 21975901234108263541776005)
                    ·
                      refine ⟨4120481481395299414083001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21975901234108263541776005 4120481481395299414083001)
                      ·
                        rfl

theorem cell23_8024609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_8024609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024609 prefixEnd_8024609 := by exact prefixLift 8024609
  have htrace : WordTrace (prefixWord ++ tailWord_8024609) baseStart_8024609 baseEnd_8024609 := by
    simpa [prefixWord, tailWord_8024609, baseEnd_8024609] using wordTrace_append hprefix tailTrace_8024609
  have hstable : (prefixWord ++ tailWord_8024609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024609).length < 2 ^ (prefixWord ++ tailWord_8024609).sum := by decide
  have hdescent : baseEnd_8024609 < baseStart_8024609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024629 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_8024629 : Nat := 118140960795 + 8024629 * 2 ^ 59
def prefixEnd_8024629 : Nat := 4983230072969 + 3 ^ 40 * 8024629 * 2
def baseEnd_8024629 : Nat := 4120491751008389335832909

theorem tailTrace_8024629 : CollatzResearch.WordTrace tailWord_8024629 prefixEnd_8024629 4120491751008389335832909 := by
  unfold tailWord_8024629
  simp only [CollatzResearch.WordTrace]
  refine ⟨292682264445147105367428941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195121509630098070244952627 292682264445147105367428941)
  ·
    refine ⟨109755849166930164512785853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292682264445147105367428941 109755849166930164512785853)
    ·
      refine ⟨41158443437598811692294695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109755849166930164512785853 41158443437598811692294695)
      ·
        refine ⟨61737665156398217538442043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41158443437598811692294695 61737665156398217538442043)
        ·
          refine ⟨92606497734597326307663065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61737665156398217538442043 92606497734597326307663065)
          ·
            refine ⟨69454873300947994730747299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92606497734597326307663065 69454873300947994730747299)
            ·
              refine ⟨104182309951421992096120949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69454873300947994730747299 104182309951421992096120949)
              ·
                refine ⟨9767091557945811759011339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104182309951421992096120949 9767091557945811759011339)
                ·
                  refine ⟨14650637336918717638517009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767091557945811759011339 14650637336918717638517009)
                  ·
                    refine ⟨10987978002689038228887757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14650637336918717638517009 10987978002689038228887757)
                    ·
                      refine ⟨4120491751008389335832909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987978002689038228887757 4120491751008389335832909)
                      ·
                        rfl

theorem cell23_8024629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_8024629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024629 prefixEnd_8024629 := by exact prefixLift 8024629
  have htrace : WordTrace (prefixWord ++ tailWord_8024629) baseStart_8024629 baseEnd_8024629 := by
    simpa [prefixWord, tailWord_8024629, baseEnd_8024629] using wordTrace_append hprefix tailTrace_8024629
  have hstable : (prefixWord ++ tailWord_8024629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024629).length < 2 ^ (prefixWord ++ tailWord_8024629).sum := by decide
  have hdescent : baseEnd_8024629 < baseStart_8024629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024646 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8024646 : Nat := 118140960795 + 8024646 * 2 ^ 59
def prefixEnd_8024646 : Nat := 4983230072969 + 3 ^ 40 * 8024646 * 2
def baseEnd_8024646 : Nat := 4120500480179515769320331

theorem tailTrace_8024646 : CollatzResearch.WordTrace tailWord_8024646 prefixEnd_8024646 4120500480179515769320331 := by
  unfold tailWord_8024646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9146340140190172414712431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195121922990723678180531861 9146340140190172414712431)
  ·
    refine ⟨13719510210285258622068647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9146340140190172414712431 13719510210285258622068647)
    ·
      refine ⟨20579265315427887933102971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719510210285258622068647 20579265315427887933102971)
      ·
        refine ⟨30868897973141831899654457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579265315427887933102971 30868897973141831899654457)
        ·
          refine ⟨23151673479856373924740843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30868897973141831899654457 23151673479856373924740843)
          ·
            refine ⟨34727510219784560887111265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23151673479856373924740843 34727510219784560887111265)
            ·
              refine ⟨26045632664838420665333449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34727510219784560887111265 26045632664838420665333449)
              ·
                refine ⟨19534224498628815499000087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26045632664838420665333449 19534224498628815499000087)
                ·
                  refine ⟨29301336747943223248500131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19534224498628815499000087 29301336747943223248500131)
                  ·
                    refine ⟨43952005121914834872750197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29301336747943223248500131 43952005121914834872750197)
                    ·
                      refine ⟨4120500480179515769320331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43952005121914834872750197 4120500480179515769320331)
                      ·
                        rfl

theorem cell23_8024646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8024646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024646 prefixEnd_8024646 := by exact prefixLift 8024646
  have htrace : WordTrace (prefixWord ++ tailWord_8024646) baseStart_8024646 baseEnd_8024646 := by
    simpa [prefixWord, tailWord_8024646, baseEnd_8024646] using wordTrace_append hprefix tailTrace_8024646
  have hstable : (prefixWord ++ tailWord_8024646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024646).length < 2 ^ (prefixWord ++ tailWord_8024646).sum := by decide
  have hdescent : baseEnd_8024646 < baseStart_8024646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024653 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_8024653 : Nat := 118140960795 + 8024653 * 2 ^ 59
def prefixEnd_8024653 : Nat := 4983230072969 + 3 ^ 40 * 8024653 * 2
def baseEnd_8024653 : Nat := 1373501358181365747310933

theorem tailTrace_8024653 : CollatzResearch.WordTrace tailWord_8024653 prefixEnd_8024653 1373501358181365747310933 := by
  unfold tailWord_8024653
  simp only [CollatzResearch.WordTrace]
  refine ⟨292683139797060157466302613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195122093198040104977535075 292683139797060157466302613)
  ·
    refine ⟨13719522177987194881232935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292683139797060157466302613 13719522177987194881232935)
    ·
      refine ⟨20579283266980792321849403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719522177987194881232935 20579283266980792321849403)
      ·
        refine ⟨30868924900471188482774105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579283266980792321849403 30868924900471188482774105)
        ·
          refine ⟨23151693675353391362080579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30868924900471188482774105 23151693675353391362080579)
          ·
            refine ⟨34727540513030087043120869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23151693675353391362080579 34727540513030087043120869)
            ·
              refine ⟨6511413846193141320585163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34727540513030087043120869 6511413846193141320585163)
              ·
                refine ⟨9767120769289711980877745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511413846193141320585163 9767120769289711980877745)
                ·
                  refine ⟨7325340576967283985658309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9767120769289711980877745 7325340576967283985658309)
                  ·
                    refine ⟨1373501358181365747310933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325340576967283985658309 1373501358181365747310933)
                    ·
                      rfl

theorem cell23_8024653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_8024653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024653 prefixEnd_8024653 := by exact prefixLift 8024653
  have htrace : WordTrace (prefixWord ++ tailWord_8024653) baseStart_8024653 baseEnd_8024653 := by
    simpa [prefixWord, tailWord_8024653, baseEnd_8024653] using wordTrace_append hprefix tailTrace_8024653
  have hstable : (prefixWord ++ tailWord_8024653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024653).length < 2 ^ (prefixWord ++ tailWord_8024653).sum := by decide
  have hdescent : baseEnd_8024653 < baseStart_8024653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_8024665 : Nat := 118140960795 + 8024665 * 2 ^ 59
def prefixEnd_8024665 : Nat := 4983230072969 + 3 ^ 40 * 8024665 * 2
def baseEnd_8024665 : Nat := 4120510236311951194982743

theorem tailTrace_8024665 : CollatzResearch.WordTrace tailWord_8024665 prefixEnd_8024665 4120510236311951194982743 := by
  unfold tailWord_8024665
  simp only [CollatzResearch.WordTrace]
  refine ⟨292683577473016683515739449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195122384982011122343826299 292683577473016683515739449)
  ·
    refine ⟨219512683104762512636804587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292683577473016683515739449 219512683104762512636804587)
    ·
      refine ⟨329269024657143768955206881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219512683104762512636804587 329269024657143768955206881)
      ·
        refine ⟨246951768492857826716405161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329269024657143768955206881 246951768492857826716405161)
        ·
          refine ⟨185213826369643370037303871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246951768492857826716405161 185213826369643370037303871)
          ·
            refine ⟨277820739554465055055955807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185213826369643370037303871 277820739554465055055955807)
            ·
              refine ⟨416731109331697582583933711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277820739554465055055955807 416731109331697582583933711)
              ·
                refine ⟨625096663997546373875900567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416731109331697582583933711 625096663997546373875900567)
                ·
                  refine ⟨937644995996319560813850851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625096663997546373875900567 937644995996319560813850851)
                  ·
                    refine ⟨1406467493994479341220776277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937644995996319560813850851 1406467493994479341220776277)
                    ·
                      refine ⟨4120510236311951194982743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1406467493994479341220776277 4120510236311951194982743)
                      ·
                        rfl

theorem cell23_8024665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_8024665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024665 prefixEnd_8024665 := by exact prefixLift 8024665
  have htrace : WordTrace (prefixWord ++ tailWord_8024665) baseStart_8024665 baseEnd_8024665 := by
    simpa [prefixWord, tailWord_8024665, baseEnd_8024665] using wordTrace_append hprefix tailTrace_8024665
  have hstable : (prefixWord ++ tailWord_8024665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024665).length < 2 ^ (prefixWord ++ tailWord_8024665).sum := by decide
  have hdescent : baseEnd_8024665 < baseStart_8024665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024694 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_8024694 : Nat := 118140960795 + 8024694 * 2 ^ 59
def prefixEnd_8024694 : Nat := 4983230072969 + 3 ^ 40 * 8024694 * 2
def baseEnd_8024694 : Nat := 4120525127250931581520111

theorem tailTrace_8024694 : CollatzResearch.WordTrace tailWord_8024694 prefixEnd_8024694 4120525127250931581520111 := by
  unfold tailWord_8024694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292789699369476341784071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195123090126607747645696757 18292789699369476341784071)
  ·
    refine ⟨27439184549054214512676107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18292789699369476341784071 27439184549054214512676107)
    ·
      refine ⟨41158776823581321769014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27439184549054214512676107 41158776823581321769014161)
      ·
        refine ⟨30869082617685991326760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41158776823581321769014161 30869082617685991326760621)
        ·
          refine ⟨11575905981632246747535233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30869082617685991326760621 11575905981632246747535233)
          ·
            refine ⟨8681929486224185060651425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575905981632246747535233 8681929486224185060651425)
            ·
              refine ⟨6511447114668138795488569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681929486224185060651425 6511447114668138795488569)
              ·
                refine ⟨4883585336001104096616427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511447114668138795488569 4883585336001104096616427)
                ·
                  refine ⟨7325378004001656144924641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883585336001104096616427 7325378004001656144924641)
                  ·
                    refine ⟨5494033503001242108693481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325378004001656144924641 5494033503001242108693481)
                    ·
                      refine ⟨4120525127250931581520111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494033503001242108693481 4120525127250931581520111)
                      ·
                        rfl

theorem cell23_8024694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_8024694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024694 prefixEnd_8024694 := by exact prefixLift 8024694
  have htrace : WordTrace (prefixWord ++ tailWord_8024694) baseStart_8024694 baseEnd_8024694 := by
    simpa [prefixWord, tailWord_8024694, baseEnd_8024694] using wordTrace_append hprefix tailTrace_8024694
  have hstable : (prefixWord ++ tailWord_8024694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024694).length < 2 ^ (prefixWord ++ tailWord_8024694).sum := by decide
  have hdescent : baseEnd_8024694 < baseStart_8024694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024737 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_8024737 : Nat := 118140960795 + 8024737 * 2 ^ 59
def prefixEnd_8024737 : Nat := 4983230072969 + 3 ^ 40 * 8024737 * 2
def baseEnd_8024737 : Nat := 4120547206919074913282413

theorem tailTrace_8024737 : CollatzResearch.WordTrace tailWord_8024737 prefixEnd_8024737 4120547206919074913282413 := by
  unfold tailWord_8024737
  simp only [CollatzResearch.WordTrace]
  refine ⟨292686203528755839812360465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195124135685837226541573643 292686203528755839812360465)
  ·
    refine ⟨219514652646566879859270349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292686203528755839812360465 219514652646566879859270349)
    ·
      refine ⟨82317994742462579947226381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219514652646566879859270349 82317994742462579947226381)
      ·
        refine ⟨30869248028423467480209893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82317994742462579947226381 30869248028423467480209893)
        ·
          refine ⟨5787984005329400152539355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30869248028423467480209893 5787984005329400152539355)
          ·
            refine ⟨8681976007994100228809033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787984005329400152539355 8681976007994100228809033)
            ·
              refine ⟨6511482005995575171606775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681976007994100228809033 6511482005995575171606775)
              ·
                refine ⟨9767223008993362757410163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511482005995575171606775 9767223008993362757410163)
                ·
                  refine ⟨14650834513490044136115245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767223008993362757410163 14650834513490044136115245)
                  ·
                    refine ⟨5494062942558766551043217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14650834513490044136115245 5494062942558766551043217)
                    ·
                      refine ⟨4120547206919074913282413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494062942558766551043217 4120547206919074913282413)
                      ·
                        rfl

theorem cell23_8024737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_8024737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024737 prefixEnd_8024737 := by exact prefixLift 8024737
  have htrace : WordTrace (prefixWord ++ tailWord_8024737) baseStart_8024737 baseEnd_8024737 := by
    simpa [prefixWord, tailWord_8024737, baseEnd_8024737] using wordTrace_append hprefix tailTrace_8024737
  have hstable : (prefixWord ++ tailWord_8024737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024737).length < 2 ^ (prefixWord ++ tailWord_8024737).sum := by decide
  have hdescent : baseEnd_8024737 < baseStart_8024737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024750 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_8024750 : Nat := 118140960795 + 8024750 * 2 ^ 59
def prefixEnd_8024750 : Nat := 4983230072969 + 3 ^ 40 * 8024750 * 2
def baseEnd_8024750 : Nat := 4120553882167583362419853

theorem tailTrace_8024750 : CollatzResearch.WordTrace tailWord_8024750 prefixEnd_8024750 4120553882167583362419853 := by
  unfold tailWord_8024750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36585834709713592879072963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195124451785139162021722469 36585834709713592879072963)
  ·
    refine ⟨54878752064570389318609445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36585834709713592879072963 54878752064570389318609445)
    ·
      refine ⟨10289766012106947997239271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54878752064570389318609445 10289766012106947997239271)
      ·
        refine ⟨15434649018160421995858907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10289766012106947997239271 15434649018160421995858907)
        ·
          refine ⟨23151973527240632993788361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15434649018160421995858907 23151973527240632993788361)
          ·
            refine ⟨17363980145430474745341271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23151973527240632993788361 17363980145430474745341271)
            ·
              refine ⟨26045970218145712118011907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17363980145430474745341271 26045970218145712118011907)
              ·
                refine ⟨39068955327218568177017861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26045970218145712118011907 39068955327218568177017861)
                ·
                  refine ⟨7325429123853481533190849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39068955327218568177017861 7325429123853481533190849)
                  ·
                    refine ⟨5494071842890111149893137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325429123853481533190849 5494071842890111149893137)
                    ·
                      refine ⟨4120553882167583362419853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494071842890111149893137 4120553882167583362419853)
                      ·
                        rfl

theorem cell23_8024750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_8024750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024750 prefixEnd_8024750 := by exact prefixLift 8024750
  have htrace : WordTrace (prefixWord ++ tailWord_8024750) baseStart_8024750 baseEnd_8024750 := by
    simpa [prefixWord, tailWord_8024750, baseEnd_8024750] using wordTrace_append hprefix tailTrace_8024750
  have hstable : (prefixWord ++ tailWord_8024750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024750).length < 2 ^ (prefixWord ++ tailWord_8024750).sum := by decide
  have hdescent : baseEnd_8024750 < baseStart_8024750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024752 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_8024752 : Nat := 118140960795 + 8024752 * 2 ^ 59
def prefixEnd_8024752 : Nat := 4983230072969 + 3 ^ 40 * 8024752 * 2
def baseEnd_8024752 : Nat := 1373518303042964118198281

theorem tailTrace_8024752 : CollatzResearch.WordTrace tailWord_8024752 prefixEnd_8024752 1373518303042964118198281 := by
  unfold tailWord_8024752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146343375311850748687078255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195124500415800998249437673 146343375311850748687078255)
  ·
    refine ⟨219515062967776123030617383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146343375311850748687078255 219515062967776123030617383)
    ·
      refine ⟨329272594451664184545926075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219515062967776123030617383 329272594451664184545926075)
      ·
        refine ⟨493908891677496276818889113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329272594451664184545926075 493908891677496276818889113)
        ·
          refine ⟨370431668758122207614166835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493908891677496276818889113 370431668758122207614166835)
          ·
            refine ⟨555647503137183311421250253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370431668758122207614166835 555647503137183311421250253)
            ·
              refine ⟨208367813676443741782968845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555647503137183311421250253 208367813676443741782968845)
              ·
                refine ⟨78137930128666403168613317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208367813676443741782968845 78137930128666403168613317)
                ·
                  refine ⟨14650861899124950594114997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78137930128666403168613317 14650861899124950594114997)
                  ·
                    refine ⟨1373518303042964118198281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14650861899124950594114997 1373518303042964118198281)
                    ·
                      rfl

theorem cell23_8024752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_8024752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024752 prefixEnd_8024752 := by exact prefixLift 8024752
  have htrace : WordTrace (prefixWord ++ tailWord_8024752) baseStart_8024752 baseEnd_8024752 := by
    simpa [prefixWord, tailWord_8024752, baseEnd_8024752] using wordTrace_append hprefix tailTrace_8024752
  have hstable : (prefixWord ++ tailWord_8024752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024752).length < 2 ^ (prefixWord ++ tailWord_8024752).sum := by decide
  have hdescent : baseEnd_8024752 < baseStart_8024752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024762 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_8024762 : Nat := 118140960795 + 8024762 * 2 ^ 59
def prefixEnd_8024762 : Nat := 4983230072969 + 3 ^ 40 * 8024762 * 2
def baseEnd_8024762 : Nat := 4120560043935437315469797

theorem tailTrace_8024762 : CollatzResearch.WordTrace tailWord_8024762 prefixEnd_8024762 4120560043935437315469797 := by
  unfold tailWord_8024762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73171778838416317270505135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195124743569110179388013693 73171778838416317270505135)
  ·
    refine ⟨109757668257624475905757703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73171778838416317270505135 109757668257624475905757703)
    ·
      refine ⟨164636502386436713858636555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109757668257624475905757703 164636502386436713858636555)
      ·
        refine ⟨246954753579655070787954833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164636502386436713858636555 246954753579655070787954833)
        ·
          refine ⟨185216065184741303090966125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246954753579655070787954833 185216065184741303090966125)
          ·
            refine ⟨69456024444277988659112297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185216065184741303090966125 69456024444277988659112297)
            ·
              refine ⟨52092018333208491494334223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69456024444277988659112297 52092018333208491494334223)
              ·
                refine ⟨78138027499812737241501335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52092018333208491494334223 78138027499812737241501335)
                ·
                  refine ⟨117207041249719105862252003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78138027499812737241501335 117207041249719105862252003)
                  ·
                    refine ⟨175810561874578658793378005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117207041249719105862252003 175810561874578658793378005)
                    ·
                      refine ⟨4120560043935437315469797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175810561874578658793378005 4120560043935437315469797)
                      ·
                        rfl

theorem cell23_8024762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_8024762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024762 prefixEnd_8024762 := by exact prefixLift 8024762
  have htrace : WordTrace (prefixWord ++ tailWord_8024762) baseStart_8024762 baseEnd_8024762 := by
    simpa [prefixWord, tailWord_8024762, baseEnd_8024762] using wordTrace_append hprefix tailTrace_8024762
  have hstable : (prefixWord ++ tailWord_8024762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024762).length < 2 ^ (prefixWord ++ tailWord_8024762).sum := by decide
  have hdescent : baseEnd_8024762 < baseStart_8024762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024809 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_8024809 : Nat := 118140960795 + 8024809 * 2 ^ 59
def prefixEnd_8024809 : Nat := 4983230072969 + 3 ^ 40 * 8024809 * 2
def baseEnd_8024809 : Nat := 4120584177526198631582081

theorem tailTrace_8024809 : CollatzResearch.WordTrace tailWord_8024809 prefixEnd_8024809 4120584177526198631582081 := by
  unfold tailWord_8024809
  simp only [CollatzResearch.WordTrace]
  refine ⟨292688829584494996108981481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195125886389663330739320987 292688829584494996108981481)
  ·
    refine ⟨219516622188371247081736111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292688829584494996108981481 219516622188371247081736111)
    ·
      refine ⟨329274933282556870622604167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219516622188371247081736111 329274933282556870622604167)
      ·
        refine ⟨493912399923835305933906251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329274933282556870622604167 493912399923835305933906251)
        ·
          refine ⟨740868599885752958900859377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493912399923835305933906251 740868599885752958900859377)
          ·
            refine ⟨555651449914314719175644533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740868599885752958900859377 555651449914314719175644533)
            ·
              refine ⟨52092323429467004922716675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 555651449914314719175644533 52092323429467004922716675)
              ·
                refine ⟨78138485144200507384075013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52092323429467004922716675 78138485144200507384075013)
                ·
                  refine ⟨14650965964537595134514065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78138485144200507384075013 14650965964537595134514065)
                  ·
                    refine ⟨10988224473403196350885549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14650965964537595134514065 10988224473403196350885549)
                    ·
                      refine ⟨4120584177526198631582081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988224473403196350885549 4120584177526198631582081)
                      ·
                        rfl

theorem cell23_8024809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_8024809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024809 prefixEnd_8024809 := by exact prefixLift 8024809
  have htrace : WordTrace (prefixWord ++ tailWord_8024809) baseStart_8024809 baseEnd_8024809 := by
    simpa [prefixWord, tailWord_8024809, baseEnd_8024809] using wordTrace_append hprefix tailTrace_8024809
  have hstable : (prefixWord ++ tailWord_8024809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024809).length < 2 ^ (prefixWord ++ tailWord_8024809).sum := by decide
  have hdescent : baseEnd_8024809 < baseStart_8024809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024829 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 6]
def baseStart_8024829 : Nat := 118140960795 + 8024829 * 2 ^ 59
def prefixEnd_8024829 : Nat := 4983230072969 + 3 ^ 40 * 8024829 * 2
def baseEnd_8024829 : Nat := 457843827459920950370221

theorem tailTrace_8024829 : CollatzResearch.WordTrace tailWord_8024829 prefixEnd_8024829 457843827459920950370221 := by
  unfold tailWord_8024829
  simp only [CollatzResearch.WordTrace]
  refine ⟨292689559044422539524709541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195126372696281693016473027 292689559044422539524709541)
  ·
    refine ⟨54879292320829226160883039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292689559044422539524709541 54879292320829226160883039)
    ·
      refine ⟨82318938481243839241324559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54879292320829226160883039 82318938481243839241324559)
      ·
        refine ⟨123478407721865758861986839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82318938481243839241324559 123478407721865758861986839)
        ·
          refine ⟨185217611582798638292980259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123478407721865758861986839 185217611582798638292980259)
          ·
            refine ⟨277826417374197957439470389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185217611582798638292980259 277826417374197957439470389)
            ·
              refine ⟨26046226628831058509950349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277826417374197957439470389 26046226628831058509950349)
              ·
                refine ⟨9767334985811646941231381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26046226628831058509950349 9767334985811646941231381)
                ·
                  refine ⟨457843827459920950370221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9767334985811646941231381 457843827459920950370221)
                  ·
                    rfl

theorem cell23_8024829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_8024829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024829 prefixEnd_8024829 := by exact prefixLift 8024829
  have htrace : WordTrace (prefixWord ++ tailWord_8024829) baseStart_8024829 baseEnd_8024829 := by
    simpa [prefixWord, tailWord_8024829, baseEnd_8024829] using wordTrace_append hprefix tailTrace_8024829
  have hstable : (prefixWord ++ tailWord_8024829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024829).length < 2 ^ (prefixWord ++ tailWord_8024829).sum := by decide
  have hdescent : baseEnd_8024829 < baseStart_8024829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 1, 1, 3]
def baseStart_8024873 : Nat := 118140960795 + 8024873 * 2 ^ 59
def prefixEnd_8024873 : Nat := 4983230072969 + 3 ^ 40 * 8024873 * 2
def baseEnd_8024873 : Nat := 4120617040288086381181787

theorem tailTrace_8024873 : CollatzResearch.WordTrace tailWord_8024873 prefixEnd_8024873 4120617040288086381181787 := by
  unfold tailWord_8024873
  simp only [CollatzResearch.WordTrace]
  refine ⟨292691163856263135039311273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195127442570842090026207515 292691163856263135039311273)
  ·
    refine ⟨219518372892197351279483455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292691163856263135039311273 219518372892197351279483455)
    ·
      refine ⟨329277559338296026919225183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219518372892197351279483455 329277559338296026919225183)
      ·
        refine ⟨493916339007444040378837775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329277559338296026919225183 493916339007444040378837775)
        ·
          refine ⟨740874508511166060568256663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493916339007444040378837775 740874508511166060568256663)
          ·
            refine ⟨1111311762766749090852384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740874508511166060568256663 1111311762766749090852384995)
            ·
              refine ⟨1666967644150123636278577493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111311762766749090852384995 1666967644150123636278577493)
              ·
                refine ⟨4883694269971065340659895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1666967644150123636278577493 4883694269971065340659895)
                ·
                  refine ⟨7325541404956598010989843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883694269971065340659895 7325541404956598010989843)
                  ·
                    refine ⟨10988312107434897016484765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325541404956598010989843 10988312107434897016484765)
                    ·
                      refine ⟨4120617040288086381181787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988312107434897016484765 4120617040288086381181787)
                      ·
                        rfl

theorem cell23_8024873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 1, 3].length) (baseStart_8024873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024873 prefixEnd_8024873 := by exact prefixLift 8024873
  have htrace : WordTrace (prefixWord ++ tailWord_8024873) baseStart_8024873 baseEnd_8024873 := by
    simpa [prefixWord, tailWord_8024873, baseEnd_8024873] using wordTrace_append hprefix tailTrace_8024873
  have hstable : (prefixWord ++ tailWord_8024873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024873).length < 2 ^ (prefixWord ++ tailWord_8024873).sum := by decide
  have hdescent : baseEnd_8024873 < baseStart_8024873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024913 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_8024913 : Nat := 118140960795 + 8024913 * 2 ^ 59
def prefixEnd_8024913 : Nat := 4983230072969 + 3 ^ 40 * 8024913 * 2
def baseEnd_8024913 : Nat := 4120637579514266224681603

theorem tailTrace_8024913 : CollatzResearch.WordTrace tailWord_8024913 prefixEnd_8024913 4120637579514266224681603 := by
  unfold tailWord_8024913
  simp only [CollatzResearch.WordTrace]
  refine ⟨292692622776118221870767393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195128415184078814580511595 292692622776118221870767393)
  ·
    refine ⟨219519467082088666403075545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292692622776118221870767393 219519467082088666403075545)
    ·
      refine ⟨164639600311566499802306659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219519467082088666403075545 164639600311566499802306659)
      ·
        refine ⟨246959400467349749703459989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164639600311566499802306659 246959400467349749703459989)
        ·
          refine ⟨11576221896907019517349687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246959400467349749703459989 11576221896907019517349687)
          ·
            refine ⟨17364332845360529276024531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576221896907019517349687 17364332845360529276024531)
            ·
              refine ⟨26046499268040793914036797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17364332845360529276024531 26046499268040793914036797)
              ·
                refine ⟨9767437225515297717763799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26046499268040793914036797 9767437225515297717763799)
                ·
                  refine ⟨14651155838272946576645699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767437225515297717763799 14651155838272946576645699)
                  ·
                    refine ⟨21976733757409419864968549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14651155838272946576645699 21976733757409419864968549)
                    ·
                      refine ⟨4120637579514266224681603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21976733757409419864968549 4120637579514266224681603)
                      ·
                        rfl

theorem cell23_8024913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_8024913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024913 prefixEnd_8024913 := by exact prefixLift 8024913
  have htrace : WordTrace (prefixWord ++ tailWord_8024913) baseStart_8024913 baseEnd_8024913 := by
    simpa [prefixWord, tailWord_8024913, baseEnd_8024913] using wordTrace_append hprefix tailTrace_8024913
  have hstable : (prefixWord ++ tailWord_8024913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024913).length < 2 ^ (prefixWord ++ tailWord_8024913).sum := by decide
  have hdescent : baseEnd_8024913 < baseStart_8024913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024919 : List Nat := [1, 1, 3, 2, 4, 2, 10]
def baseStart_8024919 : Nat := 118140960795 + 8024919 * 2 ^ 59
def prefixEnd_8024919 : Nat := 4983230072969 + 3 ^ 40 * 8024919 * 2
def baseEnd_8024919 : Nat := 50872106918496212360575

theorem tailTrace_8024919 : CollatzResearch.WordTrace tailWord_8024919 prefixEnd_8024919 50872106918496212360575 := by
  unfold tailWord_8024919
  simp only [CollatzResearch.WordTrace]
  refine ⟨292692841614096484895485811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195128561076064323263657207 292692841614096484895485811)
  ·
    refine ⟨439039262421144727343228717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292692841614096484895485811 439039262421144727343228717)
    ·
      refine ⟨164639723407929272753710769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439039262421144727343228717 164639723407929272753710769)
      ·
        refine ⟨123479792555946954565283077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164639723407929272753710769 123479792555946954565283077)
        ·
          refine ⟨23152461104240053980990577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123479792555946954565283077 23152461104240053980990577)
          ·
            refine ⟨17364345828180040485742933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23152461104240053980990577 17364345828180040485742933)
            ·
              refine ⟨50872106918496212360575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17364345828180040485742933 50872106918496212360575)
              ·
                rfl

theorem cell23_8024919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 10].length) (baseStart_8024919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024919 prefixEnd_8024919 := by exact prefixLift 8024919
  have htrace : WordTrace (prefixWord ++ tailWord_8024919) baseStart_8024919 baseEnd_8024919 := by
    simpa [prefixWord, tailWord_8024919, baseEnd_8024919] using wordTrace_append hprefix tailTrace_8024919
  have hstable : (prefixWord ++ tailWord_8024919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024919).length < 2 ^ (prefixWord ++ tailWord_8024919).sum := by decide
  have hdescent : baseEnd_8024919 < baseStart_8024919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024950 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_8024950 : Nat := 118140960795 + 8024950 * 2 ^ 59
def prefixEnd_8024950 : Nat := 4983230072969 + 3 ^ 40 * 8024950 * 2
def baseEnd_8024950 : Nat := 4120656578298482579918933

theorem tailTrace_8024950 : CollatzResearch.WordTrace tailWord_8024950 prefixEnd_8024950 4120656578298482579918933 := by
  unfold tailWord_8024950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293373267311511074366519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195129314851322784793242869 18293373267311511074366519)
  ·
    refine ⟨27440059900967266611549779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293373267311511074366519 27440059900967266611549779)
    ·
      refine ⟨41160089851450899917324669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440059900967266611549779 41160089851450899917324669)
      ·
        refine ⟨15435033694294087468996751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41160089851450899917324669 15435033694294087468996751)
        ·
          refine ⟨23152550541441131203495127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435033694294087468996751 23152550541441131203495127)
          ·
            refine ⟨34728825812161696805242691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23152550541441131203495127 34728825812161696805242691)
            ·
              refine ⟨52093238718242545207864037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34728825812161696805242691 52093238718242545207864037)
              ·
                refine ⟨9767482259670477226474507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52093238718242545207864037 9767482259670477226474507)
                ·
                  refine ⟨14651223389505715839711761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767482259670477226474507 14651223389505715839711761)
                  ·
                    refine ⟨10988417542129286879783821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14651223389505715839711761 10988417542129286879783821)
                    ·
                      refine ⟨4120656578298482579918933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988417542129286879783821 4120656578298482579918933)
                      ·
                        rfl

theorem cell23_8024950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_8024950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024950 prefixEnd_8024950 := by exact prefixLift 8024950
  have htrace : WordTrace (prefixWord ++ tailWord_8024950) baseStart_8024950 baseEnd_8024950 := by
    simpa [prefixWord, tailWord_8024950, baseEnd_8024950] using wordTrace_append hprefix tailTrace_8024950
  have hstable : (prefixWord ++ tailWord_8024950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024950).length < 2 ^ (prefixWord ++ tailWord_8024950).sum := by decide
  have hdescent : baseEnd_8024950 < baseStart_8024950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024956 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_8024956 : Nat := 118140960795 + 8024956 * 2 ^ 59
def prefixEnd_8024956 : Nat := 4983230072969 + 3 ^ 40 * 8024956 * 2
def baseEnd_8024956 : Nat := 4120659659182409556443905

theorem tailTrace_8024956 : CollatzResearch.WordTrace tailWord_8024956 prefixEnd_8024956 4120659659182409556443905 := by
  unfold tailWord_8024956
  simp only [CollatzResearch.WordTrace]
  refine ⟨146347095557481220107291361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195129460743308293476388481 146347095557481220107291361)
  ·
    refine ⟨109760321668110915080468521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146347095557481220107291361 109760321668110915080468521)
    ·
      refine ⟨82320241251083186310351391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109760321668110915080468521 82320241251083186310351391)
      ·
        refine ⟨123480361876624779465527087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82320241251083186310351391 123480361876624779465527087)
        ·
          refine ⟨185220542814937169198290631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123480361876624779465527087 185220542814937169198290631)
          ·
            refine ⟨277830814222405753797435947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185220542814937169198290631 277830814222405753797435947)
            ·
              refine ⟨416746221333608630696153921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277830814222405753797435947 416746221333608630696153921)
              ·
                refine ⟨312559666000206473022115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416746221333608630696153921 312559666000206473022115441)
                ·
                  refine ⟨234419749500154854766586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312559666000206473022115441 234419749500154854766586581)
                  ·
                    refine ⟨5494212878909879408591873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234419749500154854766586581 5494212878909879408591873)
                    ·
                      refine ⟨4120659659182409556443905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494212878909879408591873 4120659659182409556443905)
                      ·
                        rfl

theorem cell23_8024956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_8024956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024956 prefixEnd_8024956 := by exact prefixLift 8024956
  have htrace : WordTrace (prefixWord ++ tailWord_8024956) baseStart_8024956 baseEnd_8024956 := by
    simpa [prefixWord, tailWord_8024956, baseEnd_8024956] using wordTrace_append hprefix tailTrace_8024956
  have hstable : (prefixWord ++ tailWord_8024956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024956).length < 2 ^ (prefixWord ++ tailWord_8024956).sum := by decide
  have hdescent : baseEnd_8024956 < baseStart_8024956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024959 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_8024959 : Nat := 118140960795 + 8024959 * 2 ^ 59
def prefixEnd_8024959 : Nat := 4983230072969 + 3 ^ 40 * 8024959 * 2
def baseEnd_8024959 : Nat := 4120661199624373044706391

theorem tailTrace_8024959 : CollatzResearch.WordTrace tailWord_8024959 prefixEnd_8024959 4120661199624373044706391 := by
  unfold tailWord_8024959
  simp only [CollatzResearch.WordTrace]
  refine ⟨292694300533951571726941931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195129533689301047817961287 292694300533951571726941931)
  ·
    refine ⟨439041450800927357590412897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292694300533951571726941931 439041450800927357590412897)
    ·
      refine ⟨329281088100695518192809673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439041450800927357590412897 329281088100695518192809673)
      ·
        refine ⟨246960816075521638644607255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329281088100695518192809673 246960816075521638644607255)
        ·
          refine ⟨370441224113282457966910883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246960816075521638644607255 370441224113282457966910883)
          ·
            refine ⟨555661836169923686950366325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370441224113282457966910883 555661836169923686950366325)
            ·
              refine ⟨52093297140930345651596843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 555661836169923686950366325 52093297140930345651596843)
              ·
                refine ⟨78139945711395518477395265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52093297140930345651596843 78139945711395518477395265)
                ·
                  refine ⟨58604959283546638858046449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78139945711395518477395265 58604959283546638858046449)
                  ·
                    refine ⟨43953719462659979143534837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58604959283546638858046449 43953719462659979143534837)
                    ·
                      refine ⟨4120661199624373044706391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43953719462659979143534837 4120661199624373044706391)
                      ·
                        rfl

theorem cell23_8024959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_8024959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024959 prefixEnd_8024959 := by exact prefixLift 8024959
  have htrace : WordTrace (prefixWord ++ tailWord_8024959) baseStart_8024959 baseEnd_8024959 := by
    simpa [prefixWord, tailWord_8024959, baseEnd_8024959] using wordTrace_append hprefix tailTrace_8024959
  have hstable : (prefixWord ++ tailWord_8024959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024959).length < 2 ^ (prefixWord ++ tailWord_8024959).sum := by decide
  have hdescent : baseEnd_8024959 < baseStart_8024959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024979 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 6]
def baseStart_8024979 : Nat := 118140960795 + 8024979 * 2 ^ 59
def prefixEnd_8024979 : Nat := 4983230072969 + 3 ^ 40 * 8024979 * 2
def baseEnd_8024979 : Nat := 1373557156412487655485433

theorem tailTrace_8024979 : CollatzResearch.WordTrace tailWord_8024979 prefixEnd_8024979 1373557156412487655485433 := by
  unfold tailWord_8024979
  simp only [CollatzResearch.WordTrace]
  refine ⟨292695029993879115142669991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195130019995919410095113327 292695029993879115142669991)
  ·
    refine ⟨439042544990818672714004987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292695029993879115142669991 439042544990818672714004987)
    ·
      refine ⟨658563817486228009071007481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439042544990818672714004987 658563817486228009071007481)
      ·
        refine ⟨493922863114671006803255611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658563817486228009071007481 493922863114671006803255611)
        ·
          refine ⟨740884294672006510204883417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493922863114671006803255611 740884294672006510204883417)
          ·
            refine ⟨555663221004004882653662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740884294672006510204883417 555663221004004882653662563)
            ·
              refine ⟨833494831506007323980493845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555663221004004882653662563 833494831506007323980493845)
              ·
                refine ⟨39070070226844093311585649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 833494831506007323980493845 39070070226844093311585649)
                ·
                  refine ⟨29302552670133069983689237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39070070226844093311585649 29302552670133069983689237)
                  ·
                    refine ⟨1373557156412487655485433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29302552670133069983689237 1373557156412487655485433)
                    ·
                      rfl

theorem cell23_8024979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_8024979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024979 prefixEnd_8024979 := by exact prefixLift 8024979
  have htrace : WordTrace (prefixWord ++ tailWord_8024979) baseStart_8024979 baseEnd_8024979 := by
    simpa [prefixWord, tailWord_8024979, baseEnd_8024979] using wordTrace_append hprefix tailTrace_8024979
  have hstable : (prefixWord ++ tailWord_8024979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024979).length < 2 ^ (prefixWord ++ tailWord_8024979).sum := by decide
  have hdescent : baseEnd_8024979 < baseStart_8024979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024980 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_8024980 : Nat := 118140960795 + 8024980 * 2 ^ 59
def prefixEnd_8024980 : Nat := 4983230072969 + 3 ^ 40 * 8024980 * 2
def baseEnd_8024980 : Nat := 4120671982718117462543795

theorem tailTrace_8024980 : CollatzResearch.WordTrace tailWord_8024980 prefixEnd_8024980 4120671982718117462543795 := by
  unfold tailWord_8024980
  simp only [CollatzResearch.WordTrace]
  refine ⟨146347533233437746156728197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195130044311250328208970929 146347533233437746156728197)
  ·
    refine ⟨27440162481269577404386537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146347533233437746156728197 27440162481269577404386537)
    ·
      refine ⟨20580121860952183053289903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27440162481269577404386537 20580121860952183053289903)
      ·
        refine ⟨30870182791428274579934855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580121860952183053289903 30870182791428274579934855)
        ·
          refine ⟨46305274187142411869902283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30870182791428274579934855 46305274187142411869902283)
          ·
            refine ⟨69457911280713617804853425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46305274187142411869902283 69457911280713617804853425)
            ·
              refine ⟨52093433460535213353640069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69457911280713617804853425 52093433460535213353640069)
              ·
                refine ⟨9767518773850352503807513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52093433460535213353640069 9767518773850352503807513)
                ·
                  refine ⟨7325639080387764377855635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9767518773850352503807513 7325639080387764377855635)
                  ·
                    refine ⟨10988458620581646566783453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325639080387764377855635 10988458620581646566783453)
                    ·
                      refine ⟨4120671982718117462543795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988458620581646566783453 4120671982718117462543795)
                      ·
                        rfl

theorem cell23_8024980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_8024980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024980 prefixEnd_8024980 := by exact prefixLift 8024980
  have htrace : WordTrace (prefixWord ++ tailWord_8024980) baseStart_8024980 baseEnd_8024980 := by
    simpa [prefixWord, tailWord_8024980, baseEnd_8024980] using wordTrace_append hprefix tailTrace_8024980
  have hstable : (prefixWord ++ tailWord_8024980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024980).length < 2 ^ (prefixWord ++ tailWord_8024980).sum := by decide
  have hdescent : baseEnd_8024980 < baseStart_8024980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025014 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_8025014 : Nat := 118140960795 + 8025014 * 2 ^ 59
def prefixEnd_8025014 : Nat := 4983230072969 + 3 ^ 40 * 8025014 * 2
def baseEnd_8025014 : Nat := 4120689441060370329518639

theorem tailTrace_8025014 : CollatzResearch.WordTrace tailWord_8025014 prefixEnd_8025014 4120689441060370329518639 := by
  unfold tailWord_8025014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293519159297019757512131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195130871032501544080129397 18293519159297019757512131)
  ·
    refine ⟨27440278738945529636268197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293519159297019757512131 27440278738945529636268197)
    ·
      refine ⟨5145052263552286806800287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27440278738945529636268197 5145052263552286806800287)
      ·
        refine ⟨7717578395328430210200431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145052263552286806800287 7717578395328430210200431)
        ·
          refine ⟨11576367592992645315300647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717578395328430210200431 11576367592992645315300647)
          ·
            refine ⟨17364551389488967972950971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576367592992645315300647 17364551389488967972950971)
            ·
              refine ⟨26046827084233451959426457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17364551389488967972950971 26046827084233451959426457)
              ·
                refine ⟨19535120313175088969569843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26046827084233451959426457 19535120313175088969569843)
                ·
                  refine ⟨29302680469762633454354765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19535120313175088969569843 29302680469762633454354765)
                  ·
                    refine ⟨10988505176160987545383037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29302680469762633454354765 10988505176160987545383037)
                    ·
                      refine ⟨4120689441060370329518639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988505176160987545383037 4120689441060370329518639)
                      ·
                        rfl

theorem cell23_8025014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_8025014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025014 prefixEnd_8025014 := by exact prefixLift 8025014
  have htrace : WordTrace (prefixWord ++ tailWord_8025014) baseStart_8025014 baseEnd_8025014 := by
    simpa [prefixWord, tailWord_8025014, baseEnd_8025014] using wordTrace_append hprefix tailTrace_8025014
  have hstable : (prefixWord ++ tailWord_8025014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025014).length < 2 ^ (prefixWord ++ tailWord_8025014).sum := by decide
  have hdescent : baseEnd_8025014 < baseStart_8025014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025029 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_8025029 : Nat := 118140960795 + 8025029 * 2 ^ 59
def prefixEnd_8025029 : Nat := 4983230072969 + 3 ^ 40 * 8025029 * 2
def baseEnd_8025029 : Nat := 4120697143270187770831069

theorem tailTrace_8025029 : CollatzResearch.WordTrace tailWord_8025029 prefixEnd_8025029 4120697143270187770831069 := by
  unfold tailWord_8025029
  simp only [CollatzResearch.WordTrace]
  refine ⟨292696853643697973681990141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195131235762465315787993427 292696853643697973681990141)
  ·
    refine ⟨109761320116386740130746303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292696853643697973681990141 109761320116386740130746303)
    ·
      refine ⟨164641980174580110196119455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109761320116386740130746303 164641980174580110196119455)
      ·
        refine ⟨246962970261870165294179183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164641980174580110196119455 246962970261870165294179183)
        ·
          refine ⟨370444455392805247941268775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246962970261870165294179183 370444455392805247941268775)
          ·
            refine ⟨555666683089207871911903163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370444455392805247941268775 555666683089207871911903163)
            ·
              refine ⟨833500024633811807867854745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555666683089207871911903163 833500024633811807867854745)
              ·
                refine ⟨625125018475358855900891059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833500024633811807867854745 625125018475358855900891059)
                ·
                  refine ⟨937687527713038283851336589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625125018475358855900891059 937687527713038283851336589)
                  ·
                    refine ⟨351632822892389356444251221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937687527713038283851336589 351632822892389356444251221)
                    ·
                      refine ⟨4120697143270187770831069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 351632822892389356444251221 4120697143270187770831069)
                      ·
                        rfl

theorem cell23_8025029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_8025029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025029 prefixEnd_8025029 := by exact prefixLift 8025029
  have htrace : WordTrace (prefixWord ++ tailWord_8025029) baseStart_8025029 baseEnd_8025029 := by
    simpa [prefixWord, tailWord_8025029, baseEnd_8025029] using wordTrace_append hprefix tailTrace_8025029
  have hstable : (prefixWord ++ tailWord_8025029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025029).length < 2 ^ (prefixWord ++ tailWord_8025029).sum := by decide
  have hdescent : baseEnd_8025029 < baseStart_8025029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025053 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_8025053 : Nat := 118140960795 + 8025053 * 2 ^ 59
def prefixEnd_8025053 : Nat := 4983230072969 + 3 ^ 40 * 8025053 * 2
def baseEnd_8025053 : Nat := 4120709466805895676930959

theorem tailTrace_8025053 : CollatzResearch.WordTrace tailWord_8025053 prefixEnd_8025053 4120709466805895676930959 := by
  unfold tailWord_8025053
  simp only [CollatzResearch.WordTrace]
  refine ⟨292697728995611025780863813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195131819330407350520575875 292697728995611025780863813)
  ·
    refine ⟨54880824186677067333911965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292697728995611025780863813 54880824186677067333911965)
    ·
      refine ⟨20580309070003900250216987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54880824186677067333911965 20580309070003900250216987)
      ·
        refine ⟨30870463605005850375325481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580309070003900250216987 30870463605005850375325481)
        ·
          refine ⟨23152847703754387781494111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30870463605005850375325481 23152847703754387781494111)
          ·
            refine ⟨34729271555631581672241167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23152847703754387781494111 34729271555631581672241167)
            ·
              refine ⟨52093907333447372508361751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34729271555631581672241167 52093907333447372508361751)
              ·
                refine ⟨78140861000171058762542627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52093907333447372508361751 78140861000171058762542627)
                ·
                  refine ⟨117211291500256588143813941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78140861000171058762542627 117211291500256588143813941)
                  ·
                    refine ⟨10988558578149055138482557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117211291500256588143813941 10988558578149055138482557)
                    ·
                      refine ⟨4120709466805895676930959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988558578149055138482557 4120709466805895676930959)
                      ·
                        rfl

theorem cell23_8025053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_8025053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025053 prefixEnd_8025053 := by exact prefixLift 8025053
  have htrace : WordTrace (prefixWord ++ tailWord_8025053) baseStart_8025053 baseEnd_8025053 := by
    simpa [prefixWord, tailWord_8025053, baseEnd_8025053] using wordTrace_append hprefix tailTrace_8025053
  have hstable : (prefixWord ++ tailWord_8025053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025053).length < 2 ^ (prefixWord ++ tailWord_8025053).sum := by decide
  have hdescent : baseEnd_8025053 < baseStart_8025053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025073 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_8025073 : Nat := 118140960795 + 8025073 * 2 ^ 59
def prefixEnd_8025073 : Nat := 4983230072969 + 3 ^ 40 * 8025073 * 2
def baseEnd_8025073 : Nat := 1373573245472995199560289

theorem tailTrace_8025073 : CollatzResearch.WordTrace tailWord_8025073 prefixEnd_8025073 1373573245472995199560289 := by
  unfold tailWord_8025073
  simp only [CollatzResearch.WordTrace]
  refine ⟨292698458455538569196591873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195132305637025712797727915 292698458455538569196591873)
  ·
    refine ⟨219523843841653926897443905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292698458455538569196591873 219523843841653926897443905)
    ·
      refine ⟨164642882881240445173082929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219523843841653926897443905 164642882881240445173082929)
      ·
        refine ⟨123482162160930333879812197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164642882881240445173082929 123482162160930333879812197)
        ·
          refine ⟨23152905405174437602464787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123482162160930333879812197 23152905405174437602464787)
          ·
            refine ⟨34729358107761656403697181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23152905405174437602464787 34729358107761656403697181)
            ·
              refine ⟨13023509290410621151386443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34729358107761656403697181 13023509290410621151386443)
              ·
                refine ⟨19535263935615931727079665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023509290410621151386443 19535263935615931727079665)
                ·
                  refine ⟨14651447951711948795309749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19535263935615931727079665 14651447951711948795309749)
                  ·
                    refine ⟨1373573245472995199560289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14651447951711948795309749 1373573245472995199560289)
                    ·
                      rfl

theorem cell23_8025073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_8025073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025073 prefixEnd_8025073 := by exact prefixLift 8025073
  have htrace : WordTrace (prefixWord ++ tailWord_8025073) baseStart_8025073 baseEnd_8025073 := by
    simpa [prefixWord, tailWord_8025073, baseEnd_8025073] using wordTrace_append hprefix tailTrace_8025073
  have hstable : (prefixWord ++ tailWord_8025073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025073).length < 2 ^ (prefixWord ++ tailWord_8025073).sum := by decide
  have hdescent : baseEnd_8025073 < baseStart_8025073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025093 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_8025093 : Nat := 118140960795 + 8025093 * 2 ^ 59
def prefixEnd_8025093 : Nat := 4983230072969 + 3 ^ 40 * 8025093 * 2
def baseEnd_8025093 : Nat := 4120730006032075520430775

theorem tailTrace_8025093 : CollatzResearch.WordTrace tailWord_8025093 prefixEnd_8025093 4120730006032075520430775 := by
  unfold tailWord_8025093
  simp only [CollatzResearch.WordTrace]
  refine ⟨292699187915466112612319933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195132791943644075074879955 292699187915466112612319933)
  ·
    refine ⟨109762195468299792229619975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292699187915466112612319933 109762195468299792229619975)
    ·
      refine ⟨164643293202449688344429963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109762195468299792229619975 164643293202449688344429963)
      ·
        refine ⟨246964939803674532516644945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164643293202449688344429963 246964939803674532516644945)
        ·
          refine ⟨185223704852755899387483709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246964939803674532516644945 185223704852755899387483709)
          ·
            refine ⟨69458889319783462270306391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185223704852755899387483709 69458889319783462270306391)
            ·
              refine ⟨104188333979675193405459587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69458889319783462270306391 104188333979675193405459587)
              ·
                refine ⟨156282500969512790108189381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104188333979675193405459587 156282500969512790108189381)
                ·
                  refine ⟨29302968931783648145285509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156282500969512790108189381 29302968931783648145285509)
                  ·
                    refine ⟨5494306674709434027241033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29302968931783648145285509 5494306674709434027241033)
                    ·
                      refine ⟨4120730006032075520430775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494306674709434027241033 4120730006032075520430775)
                      ·
                        rfl

theorem cell23_8025093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_8025093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025093 prefixEnd_8025093 := by exact prefixLift 8025093
  have htrace : WordTrace (prefixWord ++ tailWord_8025093) baseStart_8025093 baseEnd_8025093 := by
    simpa [prefixWord, tailWord_8025093, baseEnd_8025093] using wordTrace_append hprefix tailTrace_8025093
  have hstable : (prefixWord ++ tailWord_8025093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025093).length < 2 ^ (prefixWord ++ tailWord_8025093).sum := by decide
  have hdescent : baseEnd_8025093 < baseStart_8025093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025183 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_8025183 : Nat := 118140960795 + 8025183 * 2 ^ 59
def prefixEnd_8025183 : Nat := 4983230072969 + 3 ^ 40 * 8025183 * 2
def baseEnd_8025183 : Nat := 4120776219290980168305361

theorem tailTrace_8025183 : CollatzResearch.WordTrace tailWord_8025183 prefixEnd_8025183 4120776219290980168305361 := by
  unfold tailWord_8025183
  simp only [CollatzResearch.WordTrace]
  refine ⟨292702470485140057983096203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195134980323426705322064135 292702470485140057983096203)
  ·
    refine ⟨439053705727710086974644305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292702470485140057983096203 439053705727710086974644305)
    ·
      refine ⟨329290279295782565230983229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439053705727710086974644305 329290279295782565230983229)
      ·
        refine ⟨123483854735918461961618711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329290279295782565230983229 123483854735918461961618711)
        ·
          refine ⟨185225782103877692942428067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123483854735918461961618711 185225782103877692942428067)
          ·
            refine ⟨277838673155816539413642101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185225782103877692942428067 277838673155816539413642101)
            ·
              refine ⟨26047375608357800570028947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277838673155816539413642101 26047375608357800570028947)
              ·
                refine ⟨39071063412536700855043421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26047375608357800570028947 39071063412536700855043421)
                ·
                  refine ⟨14651648779701262820641283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39071063412536700855043421 14651648779701262820641283)
                  ·
                    refine ⟨21977473169551894230961925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14651648779701262820641283 21977473169551894230961925)
                    ·
                      refine ⟨4120776219290980168305361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21977473169551894230961925 4120776219290980168305361)
                      ·
                        rfl

theorem cell23_8025183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_8025183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025183 prefixEnd_8025183 := by exact prefixLift 8025183
  have htrace : WordTrace (prefixWord ++ tailWord_8025183) baseStart_8025183 baseEnd_8025183 := by
    simpa [prefixWord, tailWord_8025183, baseEnd_8025183] using wordTrace_append hprefix tailTrace_8025183
  have hstable : (prefixWord ++ tailWord_8025183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025183).length < 2 ^ (prefixWord ++ tailWord_8025183).sum := by decide
  have hdescent : baseEnd_8025183 < baseStart_8025183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025193 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_8025193 : Nat := 118140960795 + 8025193 * 2 ^ 59
def prefixEnd_8025193 : Nat := 4983230072969 + 3 ^ 40 * 8025193 * 2
def baseEnd_8025193 : Nat := 1373593784699175043060105

theorem tailTrace_8025193 : CollatzResearch.WordTrace tailWord_8025193 prefixEnd_8025193 1373593784699175043060105 := by
  unfold tailWord_8025193
  simp only [CollatzResearch.WordTrace]
  refine ⟨292702835215103829690960233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195135223476735886460640155 292702835215103829690960233)
  ·
    refine ⟨219527126411327872268220175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292702835215103829690960233 219527126411327872268220175)
    ·
      refine ⟨329290689616991808402330263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219527126411327872268220175 329290689616991808402330263)
      ·
        refine ⟨493936034425487712603495395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329290689616991808402330263 493936034425487712603495395)
        ·
          refine ⟨740904051638231568905243093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493936034425487712603495395 740904051638231568905243093)
          ·
            refine ⟨17364938710271052396216635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 740904051638231568905243093 17364938710271052396216635)
            ·
              refine ⟨26047408065406578594324953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17364938710271052396216635 26047408065406578594324953)
              ·
                refine ⟨19535556049054933945743715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26047408065406578594324953 19535556049054933945743715)
                ·
                  refine ⟨29303334073582400918615573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19535556049054933945743715 29303334073582400918615573)
                  ·
                    refine ⟨1373593784699175043060105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29303334073582400918615573 1373593784699175043060105)
                    ·
                      rfl

theorem cell23_8025193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_8025193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025193 prefixEnd_8025193 := by exact prefixLift 8025193
  have htrace : WordTrace (prefixWord ++ tailWord_8025193) baseStart_8025193 baseEnd_8025193 := by
    simpa [prefixWord, tailWord_8025193, baseEnd_8025193] using wordTrace_append hprefix tailTrace_8025193
  have hstable : (prefixWord ++ tailWord_8025193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025193).length < 2 ^ (prefixWord ++ tailWord_8025193).sum := by decide
  have hdescent : baseEnd_8025193 < baseStart_8025193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025197 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_8025197 : Nat := 118140960795 + 8025197 * 2 ^ 59
def prefixEnd_8025197 : Nat := 4983230072969 + 3 ^ 40 * 8025197 * 2
def baseEnd_8025197 : Nat := 1373594469340047704510099

theorem tailTrace_8025197 : CollatzResearch.WordTrace tailWord_8025197 prefixEnd_8025197 1373594469340047704510099 := by
  unfold tailWord_8025197
  simp only [CollatzResearch.WordTrace]
  refine ⟨292702981107089338374105845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195135320738059558916070563 292702981107089338374105845)
  ·
    refine ⟨27440904478789625472572423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292702981107089338374105845 27440904478789625472572423)
    ·
      refine ⟨41161356718184438208858635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440904478789625472572423 41161356718184438208858635)
      ·
        refine ⟨61742035077276657313287953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41161356718184438208858635 61742035077276657313287953)
        ·
          refine ⟨46306526307957492984965965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61742035077276657313287953 46306526307957492984965965)
          ·
            refine ⟨17364947365484059869362237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46306526307957492984965965 17364947365484059869362237)
            ·
              refine ⟨6511855262056522451010839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17364947365484059869362237 6511855262056522451010839)
              ·
                refine ⟨9767782893084783676516259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511855262056522451010839 9767782893084783676516259)
                ·
                  refine ⟨14651674339627175514774389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767782893084783676516259 14651674339627175514774389)
                  ·
                    refine ⟨1373594469340047704510099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14651674339627175514774389 1373594469340047704510099)
                    ·
                      rfl

theorem cell23_8025197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_8025197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025197 prefixEnd_8025197 := by exact prefixLift 8025197
  have htrace : WordTrace (prefixWord ++ tailWord_8025197) baseStart_8025197 baseEnd_8025197 := by
    simpa [prefixWord, tailWord_8025197, baseEnd_8025197] using wordTrace_append hprefix tailTrace_8025197
  have hstable : (prefixWord ++ tailWord_8025197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025197).length < 2 ^ (prefixWord ++ tailWord_8025197).sum := by decide
  have hdescent : baseEnd_8025197 < baseStart_8025197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025213 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_8025213 : Nat := 118140960795 + 8025213 * 2 ^ 59
def prefixEnd_8025213 : Nat := 4983230072969 + 3 ^ 40 * 8025213 * 2
def baseEnd_8025213 : Nat := 4120791623710615050930223

theorem tailTrace_8025213 : CollatzResearch.WordTrace tailWord_8025213 prefixEnd_8025213 4120791623710615050930223 := by
  unfold tailWord_8025213
  simp only [CollatzResearch.WordTrace]
  refine ⟨292703564675031373106688293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195135709783354248737792195 292703564675031373106688293)
  ·
    refine ⟨54881918376568382457504055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292703564675031373106688293 54881918376568382457504055)
    ·
      refine ⟨82322877564852573686256083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54881918376568382457504055 82322877564852573686256083)
      ·
        refine ⟨123484316347278860529384125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82322877564852573686256083 123484316347278860529384125)
        ·
          refine ⟨46306618630229572698519047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123484316347278860529384125 46306618630229572698519047)
          ·
            refine ⟨69459927945344359047778571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46306618630229572698519047 69459927945344359047778571)
            ·
              refine ⟨104189891918016538571667857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69459927945344359047778571 104189891918016538571667857)
              ·
                refine ⟨78142418938512403928750893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104189891918016538571667857 78142418938512403928750893)
                ·
                  refine ⟨29303407101942151473281585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78142418938512403928750893 29303407101942151473281585)
                  ·
                    refine ⟨21977555326456613604961189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29303407101942151473281585 21977555326456613604961189)
                    ·
                      refine ⟨4120791623710615050930223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21977555326456613604961189 4120791623710615050930223)
                      ·
                        rfl

theorem cell23_8025213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_8025213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025213 prefixEnd_8025213 := by exact prefixLift 8025213
  have htrace : WordTrace (prefixWord ++ tailWord_8025213) baseStart_8025213 baseEnd_8025213 := by
    simpa [prefixWord, tailWord_8025213, baseEnd_8025213] using wordTrace_append hprefix tailTrace_8025213
  have hstable : (prefixWord ++ tailWord_8025213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025213).length < 2 ^ (prefixWord ++ tailWord_8025213).sum := by decide
  have hdescent : baseEnd_8025213 < baseStart_8025213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025220 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_8025220 : Nat := 118140960795 + 8025220 * 2 ^ 59
def prefixEnd_8025220 : Nat := 4983230072969 + 3 ^ 40 * 8025220 * 2
def baseEnd_8025220 : Nat := 4120795218075196523542691

theorem tailTrace_8025220 : CollatzResearch.WordTrace tailWord_8025220 prefixEnd_8025220 4120795218075196523542691 := by
  unfold tailWord_8025220
  simp only [CollatzResearch.WordTrace]
  refine ⟨146351909993003006651096557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195135879990670675534795409 146351909993003006651096557)
  ·
    refine ⟨54881966247376127494161209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146351909993003006651096557 54881966247376127494161209)
    ·
      refine ⟨41161474685532095620620907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54881966247376127494161209 41161474685532095620620907)
      ·
        refine ⟨61742212028298143430931361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41161474685532095620620907 61742212028298143430931361)
        ·
          refine ⟨46306659021223607573198521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61742212028298143430931361 46306659021223607573198521)
          ·
            refine ⟨34729994265917705679898891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46306659021223607573198521 34729994265917705679898891)
            ·
              refine ⟨52094991398876558519848337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34729994265917705679898891 52094991398876558519848337)
              ·
                refine ⟨39071243549157418889886253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52094991398876558519848337 39071243549157418889886253)
                ·
                  refine ⟨14651716330934032083707345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39071243549157418889886253 14651716330934032083707345)
                  ·
                    refine ⟨10988787248200524062780509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14651716330934032083707345 10988787248200524062780509)
                    ·
                      refine ⟨4120795218075196523542691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988787248200524062780509 4120795218075196523542691)
                      ·
                        rfl

theorem cell23_8025220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_8025220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025220 prefixEnd_8025220 := by exact prefixLift 8025220
  have htrace : WordTrace (prefixWord ++ tailWord_8025220) baseStart_8025220 baseEnd_8025220 := by
    simpa [prefixWord, tailWord_8025220, baseEnd_8025220] using wordTrace_append hprefix tailTrace_8025220
  have hstable : (prefixWord ++ tailWord_8025220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025220).length < 2 ^ (prefixWord ++ tailWord_8025220).sum := by decide
  have hdescent : baseEnd_8025220 < baseStart_8025220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025230 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_8025230 : Nat := 118140960795 + 8025230 * 2 ^ 59
def prefixEnd_8025230 : Nat := 4983230072969 + 3 ^ 40 * 8025230 * 2
def baseEnd_8025230 : Nat := 4120800352881741484417645

theorem tailTrace_8025230 : CollatzResearch.WordTrace tailWord_8025230 prefixEnd_8025230 4120800352881741484417645 := by
  unfold tailWord_8025230
  simp only [CollatzResearch.WordTrace]
  refine ⟨36588023089496223126257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195136123143979856673371429 36588023089496223126257143)
  ·
    refine ⟨54882034634244334689385715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36588023089496223126257143 54882034634244334689385715)
    ·
      refine ⟨82323051951366502034078573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54882034634244334689385715 82323051951366502034078573)
      ·
        refine ⟨30871144481762438262779465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82323051951366502034078573 30871144481762438262779465)
        ·
          refine ⟨23153358361321828697084599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30871144481762438262779465 23153358361321828697084599)
          ·
            refine ⟨34730037541982743045626899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153358361321828697084599 34730037541982743045626899)
            ·
              refine ⟨52095056312974114568440349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34730037541982743045626899 52095056312974114568440349)
              ·
                refine ⟨19535646117365292963165131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52095056312974114568440349 19535646117365292963165131)
                ·
                  refine ⟨29303469176047939444747697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19535646117365292963165131 29303469176047939444747697)
                  ·
                    refine ⟨21977601882035954583560773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29303469176047939444747697 21977601882035954583560773)
                    ·
                      refine ⟨4120800352881741484417645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21977601882035954583560773 4120800352881741484417645)
                      ·
                        rfl

theorem cell23_8025230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_8025230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025230 prefixEnd_8025230 := by exact prefixLift 8025230
  have htrace : WordTrace (prefixWord ++ tailWord_8025230) baseStart_8025230 baseEnd_8025230 := by
    simpa [prefixWord, tailWord_8025230, baseEnd_8025230] using wordTrace_append hprefix tailTrace_8025230
  have hstable : (prefixWord ++ tailWord_8025230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025230).length < 2 ^ (prefixWord ++ tailWord_8025230).sum := by decide
  have hdescent : baseEnd_8025230 < baseStart_8025230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025234 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_8025234 : Nat := 118140960795 + 8025234 * 2 ^ 59
def prefixEnd_8025234 : Nat := 4983230072969 + 3 ^ 40 * 8025234 * 2
def baseEnd_8025234 : Nat := 4120802406804359468767627

theorem tailTrace_8025234 : CollatzResearch.WordTrace tailWord_8025234 prefixEnd_8025234 4120802406804359468767627 := by
  unfold tailWord_8025234
  simp only [CollatzResearch.WordTrace]
  refine ⟨73176082651988823423300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195136220405303529128801837 73176082651988823423300689)
  ·
    refine ⟨54882061988991617567475517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73176082651988823423300689 54882061988991617567475517)
    ·
      refine ⟨20580773245871856587803319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54882061988991617567475517 20580773245871856587803319)
      ·
        refine ⟨30871159868807784881704979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580773245871856587803319 30871159868807784881704979)
        ·
          refine ⟨46306739803211677322557469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30871159868807784881704979 46306739803211677322557469)
          ·
            refine ⟨17365027426204378995959051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46306739803211677322557469 17365027426204378995959051)
            ·
              refine ⟨26047541139306568493938577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17365027426204378995959051 26047541139306568493938577)
              ·
                refine ⟨19535655854479926370453933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26047541139306568493938577 19535655854479926370453933)
                ·
                  refine ⟨7325870945429972388920225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19535655854479926370453933 7325870945429972388920225)
                  ·
                    refine ⟨5494403209072479291690169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325870945429972388920225 5494403209072479291690169)
                    ·
                      refine ⟨4120802406804359468767627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494403209072479291690169 4120802406804359468767627)
                      ·
                        rfl

theorem cell23_8025234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_8025234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025234 prefixEnd_8025234 := by exact prefixLift 8025234
  have htrace : WordTrace (prefixWord ++ tailWord_8025234) baseStart_8025234 baseEnd_8025234 := by
    simpa [prefixWord, tailWord_8025234, baseEnd_8025234] using wordTrace_append hprefix tailTrace_8025234
  have hstable : (prefixWord ++ tailWord_8025234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025234).length < 2 ^ (prefixWord ++ tailWord_8025234).sum := by decide
  have hdescent : baseEnd_8025234 < baseStart_8025234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025240 : List Nat := [2, 1, 2, 4, 2, 2, 3, 7]
def baseStart_8025240 : Nat := 118140960795 + 8025240 * 2 ^ 59
def prefixEnd_8025240 : Nat := 4983230072969 + 3 ^ 40 * 8025240 * 2
def baseEnd_8025240 : Nat := 152622425469936535010837

theorem tailTrace_8025240 : CollatzResearch.WordTrace tailWord_8025240 prefixEnd_8025240 152622425469936535010837 := by
  unfold tailWord_8025240
  simp only [CollatzResearch.WordTrace]
  refine ⟨146352274722966778358960587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195136366297289037811947449 146352274722966778358960587)
  ·
    refine ⟨219528412084450167538440881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146352274722966778358960587 219528412084450167538440881)
    ·
      refine ⟨164646309063337625653830661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219528412084450167538440881 164646309063337625653830661)
      ·
        refine ⟨30871182949375804810093249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164646309063337625653830661 30871182949375804810093249)
        ·
          refine ⟨23153387212031853607569937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30871182949375804810093249 23153387212031853607569937)
          ·
            refine ⟨17365040409023890205677453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23153387212031853607569937 17365040409023890205677453)
            ·
              refine ⟨6511890153383958827129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17365040409023890205677453 6511890153383958827129045)
              ·
                refine ⟨152622425469936535010837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6511890153383958827129045 152622425469936535010837)
                ·
                  rfl

theorem cell23_8025240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 7].length) (baseStart_8025240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025240 prefixEnd_8025240 := by exact prefixLift 8025240
  have htrace : WordTrace (prefixWord ++ tailWord_8025240) baseStart_8025240 baseEnd_8025240 := by
    simpa [prefixWord, tailWord_8025240, baseEnd_8025240] using wordTrace_append hprefix tailTrace_8025240
  have hstable : (prefixWord ++ tailWord_8025240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025240).length < 2 ^ (prefixWord ++ tailWord_8025240).sum := by decide
  have hdescent : baseEnd_8025240 < baseStart_8025240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_8025260 : Nat := 118140960795 + 8025260 * 2 ^ 59
def prefixEnd_8025260 : Nat := 4983230072969 + 3 ^ 40 * 8025260 * 2
def baseEnd_8025260 : Nat := 4120815757301376367042507

theorem tailTrace_8025260 : CollatzResearch.WordTrace tailWord_8025260 prefixEnd_8025260 4120815757301376367042507 := by
  unfold tailWord_8025260
  simp only [CollatzResearch.WordTrace]
  refine ⟨146352639452930550066824617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195136852603907400089099489 146352639452930550066824617)
  ·
    refine ⟨109764479589697912550118463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146352639452930550066824617 109764479589697912550118463)
    ·
      refine ⟨164646719384546868825177695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109764479589697912550118463 164646719384546868825177695)
      ·
        refine ⟨246970079076820303237766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164646719384546868825177695 246970079076820303237766543)
        ·
          refine ⟨370455118615230454856649815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246970079076820303237766543 370455118615230454856649815)
          ·
            refine ⟨555682677922845682284974723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370455118615230454856649815 555682677922845682284974723)
            ·
              refine ⟨833524016884268523427462085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555682677922845682284974723 833524016884268523427462085)
              ·
                refine ⟨156285753165800348142649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833524016884268523427462085 156285753165800348142649141)
                ·
                  refine ⟨14651789359293782638373357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156285753165800348142649141 14651789359293782638373357)
                  ·
                    refine ⟨5494421009735168489390009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14651789359293782638373357 5494421009735168489390009)
                    ·
                      refine ⟨4120815757301376367042507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494421009735168489390009 4120815757301376367042507)
                      ·
                        rfl

theorem cell23_8025260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_8025260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025260 prefixEnd_8025260 := by exact prefixLift 8025260
  have htrace : WordTrace (prefixWord ++ tailWord_8025260) baseStart_8025260 baseEnd_8025260 := by
    simpa [prefixWord, tailWord_8025260, baseEnd_8025260] using wordTrace_append hprefix tailTrace_8025260
  have hstable : (prefixWord ++ tailWord_8025260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025260).length < 2 ^ (prefixWord ++ tailWord_8025260).sum := by decide
  have hdescent : baseEnd_8025260 < baseStart_8025260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025261 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_8025261 : Nat := 118140960795 + 8025261 * 2 ^ 59
def prefixEnd_8025261 : Nat := 4983230072969 + 3 ^ 40 * 8025261 * 2
def baseEnd_8025261 : Nat := 1373605423594010287710001

theorem tailTrace_8025261 : CollatzResearch.WordTrace tailWord_8025261 prefixEnd_8025261 1373605423594010287710001 := by
  unfold tailWord_8025261
  simp only [CollatzResearch.WordTrace]
  refine ⟨292705315378857477304435637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195136876919238318202957091 292705315378857477304435637)
  ·
    refine ⟨27441123316767888497290841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292705315378857477304435637 27441123316767888497290841)
    ·
      refine ⟨20580842487575916372968131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27441123316767888497290841 20580842487575916372968131)
      ·
        refine ⟨30871263731363874559452197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580842487575916372968131 30871263731363874559452197)
        ·
          refine ⟨5788361949630726479897287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30871263731363874559452197 5788361949630726479897287)
          ·
            refine ⟨8682542924446089719845931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788361949630726479897287 8682542924446089719845931)
            ·
              refine ⟨13023814386669134579768897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682542924446089719845931 13023814386669134579768897)
              ·
                refine ⟨9767860790001850934826673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13023814386669134579768897 9767860790001850934826673)
                ·
                  refine ⟨7325895592501388201120005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9767860790001850934826673 7325895592501388201120005)
                  ·
                    refine ⟨1373605423594010287710001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325895592501388201120005 1373605423594010287710001)
                    ·
                      rfl

theorem cell23_8025261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_8025261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025261 prefixEnd_8025261 := by exact prefixLift 8025261
  have htrace : WordTrace (prefixWord ++ tailWord_8025261) baseStart_8025261 baseEnd_8025261 := by
    simpa [prefixWord, tailWord_8025261, baseEnd_8025261] using wordTrace_append hprefix tailTrace_8025261
  have hstable : (prefixWord ++ tailWord_8025261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025261).length < 2 ^ (prefixWord ++ tailWord_8025261).sum := by decide
  have hdescent : baseEnd_8025261 < baseStart_8025261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025267 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 3]
def baseStart_8025267 : Nat := 118140960795 + 8025267 * 2 ^ 59
def prefixEnd_8025267 : Nat := 4983230072969 + 3 ^ 40 * 8025267 * 2
def baseEnd_8025267 : Nat := 4120819351665957839654975

theorem tailTrace_8025267 : CollatzResearch.WordTrace tailWord_8025267 prefixEnd_8025267 4120819351665957839654975 := by
  unfold tailWord_8025267
  simp only [CollatzResearch.WordTrace]
  refine ⟨292705534216835740329154055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195137022811223826886102703 292705534216835740329154055)
  ·
    refine ⟨439058301325253610493731083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292705534216835740329154055 439058301325253610493731083)
    ·
      refine ⟨658587451987880415740596625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439058301325253610493731083 658587451987880415740596625)
      ·
        refine ⟨493940588990910311805447469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658587451987880415740596625 493940588990910311805447469)
        ·
          refine ⟨185227720871591366927042801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493940588990910311805447469 185227720871591366927042801)
          ·
            refine ⟨138920790653693525195282101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185227720871591366927042801 138920790653693525195282101)
            ·
              refine ⟨13023824123783767987057697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138920790653693525195282101 13023824123783767987057697)
              ·
                refine ⟨9767868092837825990293273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13023824123783767987057697 9767868092837825990293273)
                ·
                  refine ⟨7325901069628369492719955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9767868092837825990293273 7325901069628369492719955)
                  ·
                    refine ⟨10988851604442554239079933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325901069628369492719955 10988851604442554239079933)
                    ·
                      refine ⟨4120819351665957839654975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988851604442554239079933 4120819351665957839654975)
                      ·
                        rfl

theorem cell23_8025267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_8025267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025267 prefixEnd_8025267 := by exact prefixLift 8025267
  have htrace : WordTrace (prefixWord ++ tailWord_8025267) baseStart_8025267 baseEnd_8025267 := by
    simpa [prefixWord, tailWord_8025267, baseEnd_8025267] using wordTrace_append hprefix tailTrace_8025267
  have hstable : (prefixWord ++ tailWord_8025267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025267).length < 2 ^ (prefixWord ++ tailWord_8025267).sum := by decide
  have hdescent : baseEnd_8025267 < baseStart_8025267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025284 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_8025284 : Nat := 118140960795 + 8025284 * 2 ^ 59
def prefixEnd_8025284 : Nat := 4983230072969 + 3 ^ 40 * 8025284 * 2
def baseEnd_8025284 : Nat := 4120828080837084273142397

theorem tailTrace_8025284 : CollatzResearch.WordTrace tailWord_8025284 prefixEnd_8025284 4120828080837084273142397 := by
  unfold tailWord_8025284
  simp only [CollatzResearch.WordTrace]
  refine ⟨146353077128887076116261453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195137436171849434821681937 146353077128887076116261453)
  ·
    refine ⟨54882403923332653543598045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146353077128887076116261453 54882403923332653543598045)
    ·
      refine ⟨20580901471249745078849267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54882403923332653543598045 20580901471249745078849267)
      ·
        refine ⟨30871352206874617618273901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580901471249745078849267 30871352206874617618273901)
        ·
          refine ⟨11576757077577981606852713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30871352206874617618273901 11576757077577981606852713)
          ·
            refine ⟨8682567808183486205139535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11576757077577981606852713 8682567808183486205139535)
            ·
              refine ⟨13023851712275229307709303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682567808183486205139535 13023851712275229307709303)
              ·
                refine ⟨19535777568412843961563955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023851712275229307709303 19535777568412843961563955)
                ·
                  refine ⟨29303666352619265942345933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19535777568412843961563955 29303666352619265942345933)
                  ·
                    refine ⟨10988874882232224728379725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29303666352619265942345933 10988874882232224728379725)
                    ·
                      refine ⟨4120828080837084273142397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10988874882232224728379725 4120828080837084273142397)
                      ·
                        rfl

theorem cell23_8025284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_8025284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025284 prefixEnd_8025284 := by exact prefixLift 8025284
  have htrace : WordTrace (prefixWord ++ tailWord_8025284) baseStart_8025284 baseEnd_8025284 := by
    simpa [prefixWord, tailWord_8025284, baseEnd_8025284] using wordTrace_append hprefix tailTrace_8025284
  have hstable : (prefixWord ++ tailWord_8025284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025284).length < 2 ^ (prefixWord ++ tailWord_8025284).sum := by decide
  have hdescent : baseEnd_8025284 < baseStart_8025284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025302 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_8025302 : Nat := 118140960795 + 8025302 * 2 ^ 59
def prefixEnd_8025302 : Nat := 4983230072969 + 3 ^ 40 * 8025302 * 2
def baseEnd_8025302 : Nat := 4120837323488865202717315

theorem tailTrace_8025302 : CollatzResearch.WordTrace tailWord_8025302 prefixEnd_8025302 4120837323488865202717315 := by
  unfold tailWord_8025302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294175673231808831667385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195137873847805960871118773 18294175673231808831667385)
  ·
    refine ⟨13720631754923856623750539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18294175673231808831667385 13720631754923856623750539)
    ·
      refine ⟨20580947632385784935625809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13720631754923856623750539 20580947632385784935625809)
      ·
        refine ⟨15435710724289338701719357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20580947632385784935625809 15435710724289338701719357)
        ·
          refine ⟨5788391521608502013144759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15435710724289338701719357 5788391521608502013144759)
          ·
            refine ⟨8682587282412753019717139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788391521608502013144759 8682587282412753019717139)
            ·
              refine ⟨13023880923619129529575709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682587282412753019717139 13023880923619129529575709)
              ·
                refine ⟨4883955346357173573590891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13023880923619129529575709 4883955346357173573590891)
                ·
                  refine ⟨7325933019535760360386337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883955346357173573590891 7325933019535760360386337)
                  ·
                    refine ⟨5494449764651820270289753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325933019535760360386337 5494449764651820270289753)
                    ·
                      refine ⟨4120837323488865202717315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494449764651820270289753 4120837323488865202717315)
                      ·
                        rfl

theorem cell23_8025302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_8025302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025302 prefixEnd_8025302 := by exact prefixLift 8025302
  have htrace : WordTrace (prefixWord ++ tailWord_8025302) baseStart_8025302 baseEnd_8025302 := by
    simpa [prefixWord, tailWord_8025302, baseEnd_8025302] using wordTrace_append hprefix tailTrace_8025302
  have hstable : (prefixWord ++ tailWord_8025302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025302).length < 2 ^ (prefixWord ++ tailWord_8025302).sum := by decide
  have hdescent : baseEnd_8025302 < baseStart_8025302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025303 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_8025303 : Nat := 118140960795 + 8025303 * 2 ^ 59
def prefixEnd_8025303 : Nat := 4983230072969 + 3 ^ 40 * 8025303 * 2
def baseEnd_8025303 : Nat := 4120837836969519698804809

theorem tailTrace_8025303 : CollatzResearch.WordTrace tailWord_8025303 prefixEnd_8025303 4120837836969519698804809 := by
  unfold tailWord_8025303
  simp only [CollatzResearch.WordTrace]
  refine ⟨292706847244705318477464563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195137898163136878984976375 292706847244705318477464563)
  ·
    refine ⟨439060270867057977716196845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292706847244705318477464563 439060270867057977716196845)
    ·
      refine ⟨164647601575146741643573817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439060270867057977716196845 164647601575146741643573817)
      ·
        refine ⟨123485701181360056232680363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164647601575146741643573817 123485701181360056232680363)
        ·
          refine ⟨185228551772040084349020545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123485701181360056232680363 185228551772040084349020545)
          ·
            refine ⟨138921413829030063261765409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185228551772040084349020545 138921413829030063261765409)
            ·
              refine ⟨104191060371772547446324057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138921413829030063261765409 104191060371772547446324057)
              ·
                refine ⟨78143295278829410584743043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104191060371772547446324057 78143295278829410584743043)
                ·
                  refine ⟨117214942918244115877114565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78143295278829410584743043 117214942918244115877114565)
                  ·
                    refine ⟨21977801797170771726958981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117214942918244115877114565 21977801797170771726958981)
                    ·
                      refine ⟨4120837836969519698804809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21977801797170771726958981 4120837836969519698804809)
                      ·
                        rfl

theorem cell23_8025303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_8025303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025303 prefixEnd_8025303 := by exact prefixLift 8025303
  have htrace : WordTrace (prefixWord ++ tailWord_8025303) baseStart_8025303 baseEnd_8025303 := by
    simpa [prefixWord, tailWord_8025303, baseEnd_8025303] using wordTrace_append hprefix tailTrace_8025303
  have hstable : (prefixWord ++ tailWord_8025303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025303).length < 2 ^ (prefixWord ++ tailWord_8025303).sum := by decide
  have hdescent : baseEnd_8025303 < baseStart_8025303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025353 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_8025353 : Nat := 118140960795 + 8025353 * 2 ^ 59
def prefixEnd_8025353 : Nat := 4983230072969 + 3 ^ 40 * 8025353 * 2
def baseEnd_8025353 : Nat := 4120863511002244503179579

theorem tailTrace_8025353 : CollatzResearch.WordTrace tailWord_8025353 prefixEnd_8025353 4120863511002244503179579 := by
  unfold tailWord_8025353
  simp only [CollatzResearch.WordTrace]
  refine ⟨292708670894524177016784713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195139113929682784677856475 292708670894524177016784713)
  ·
    refine ⟨219531503170893132762588535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292708670894524177016784713 219531503170893132762588535)
    ·
      refine ⟨329297254756339699143882803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219531503170893132762588535 329297254756339699143882803)
      ·
        refine ⟨493945882134509548715824205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329297254756339699143882803 493945882134509548715824205)
        ·
          refine ⟨185229705800441080768434077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493945882134509548715824205 185229705800441080768434077)
          ·
            refine ⟨69461139675165405288162779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185229705800441080768434077 69461139675165405288162779)
            ·
              refine ⟨104191709512748107932244169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69461139675165405288162779 104191709512748107932244169)
              ·
                refine ⟨78143782134561080949183127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104191709512748107932244169 78143782134561080949183127)
                ·
                  refine ⟨117215673201841621423774691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78143782134561080949183127 117215673201841621423774691)
                  ·
                    refine ⟨175823509802762432135662037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117215673201841621423774691 175823509802762432135662037)
                    ·
                      refine ⟨4120863511002244503179579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175823509802762432135662037 4120863511002244503179579)
                      ·
                        rfl

theorem cell23_8025353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_8025353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025353 prefixEnd_8025353 := by exact prefixLift 8025353
  have htrace : WordTrace (prefixWord ++ tailWord_8025353) baseStart_8025353 baseEnd_8025353 := by
    simpa [prefixWord, tailWord_8025353, baseEnd_8025353] using wordTrace_append hprefix tailTrace_8025353
  have hstable : (prefixWord ++ tailWord_8025353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025353).length < 2 ^ (prefixWord ++ tailWord_8025353).sum := by decide
  have hdescent : baseEnd_8025353 < baseStart_8025353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025370 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_8025370 : Nat := 118140960795 + 8025370 * 2 ^ 59
def prefixEnd_8025370 : Nat := 4983230072969 + 3 ^ 40 * 8025370 * 2
def baseEnd_8025370 : Nat := 4120872240173370936667001

theorem tailTrace_8025370 : CollatzResearch.WordTrace tailWord_8025370 prefixEnd_8025370 4120872240173370936667001 := by
  unfold tailWord_8025370
  simp only [CollatzResearch.WordTrace]
  refine ⟨73177322733865647230038391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195139527290308392613435709 73177322733865647230038391)
  ·
    refine ⟨109765984100798470845057587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73177322733865647230038391 109765984100798470845057587)
    ·
      refine ⟨164648976151197706267586381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109765984100798470845057587 164648976151197706267586381)
      ·
        refine ⟨61743366056699139850344893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164648976151197706267586381 61743366056699139850344893)
        ·
          refine ⟨23153762271262177443879335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61743366056699139850344893 23153762271262177443879335)
          ·
            refine ⟨34730643406893266165819003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153762271262177443879335 34730643406893266165819003)
            ·
              refine ⟨52095965110339899248728505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34730643406893266165819003 52095965110339899248728505)
              ·
                refine ⟨39071973832754924436546379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52095965110339899248728505 39071973832754924436546379)
                ·
                  refine ⟨58607960749132386654819569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39071973832754924436546379 58607960749132386654819569)
                  ·
                    refine ⟨43955970561849289991114677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58607960749132386654819569 43955970561849289991114677)
                    ·
                      refine ⟨4120872240173370936667001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43955970561849289991114677 4120872240173370936667001)
                      ·
                        rfl

theorem cell23_8025370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_8025370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025370 prefixEnd_8025370 := by exact prefixLift 8025370
  have htrace : WordTrace (prefixWord ++ tailWord_8025370) baseStart_8025370 baseEnd_8025370 := by
    simpa [prefixWord, tailWord_8025370, baseEnd_8025370] using wordTrace_append hprefix tailTrace_8025370
  have hstable : (prefixWord ++ tailWord_8025370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025370).length < 2 ^ (prefixWord ++ tailWord_8025370).sum := by decide
  have hdescent : baseEnd_8025370 < baseStart_8025370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025397 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_8025397 : Nat := 118140960795 + 8025397 * 2 ^ 59
def prefixEnd_8025397 : Nat := 4983230072969 + 3 ^ 40 * 8025397 * 2
def baseEnd_8025397 : Nat := 4120886104151042331029377

theorem tailTrace_8025397 : CollatzResearch.WordTrace tailWord_8025397 prefixEnd_8025397 4120886104151042331029377 := by
  unfold tailWord_8025397
  simp only [CollatzResearch.WordTrace]
  refine ⟨292710275706364772531386445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195140183804243181687590963 292710275706364772531386445)
  ·
    refine ⟨109766353389886789699269917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292710275706364772531386445 109766353389886789699269917)
    ·
      refine ⟨41162382521207546137226219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109766353389886789699269917 41162382521207546137226219)
      ·
        refine ⟨61743573781811319205839329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41162382521207546137226219 61743573781811319205839329)
        ·
          refine ⟨46307680336358489404379497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61743573781811319205839329 46307680336358489404379497)
          ·
            refine ⟨34730760252268867053284623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46307680336358489404379497 34730760252268867053284623)
            ·
              refine ⟨52096140378403300579926935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34730760252268867053284623 52096140378403300579926935)
              ·
                refine ⟨78144210567604950869890403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52096140378403300579926935 78144210567604950869890403)
                ·
                  refine ⟨117216315851407426304835605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78144210567604950869890403 117216315851407426304835605)
                  ·
                    refine ⟨5494514805534723108039169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117216315851407426304835605 5494514805534723108039169)
                    ·
                      refine ⟨4120886104151042331029377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494514805534723108039169 4120886104151042331029377)
                      ·
                        rfl

theorem cell23_8025397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_8025397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025397 prefixEnd_8025397 := by exact prefixLift 8025397
  have htrace : WordTrace (prefixWord ++ tailWord_8025397) baseStart_8025397 baseEnd_8025397 := by
    simpa [prefixWord, tailWord_8025397, baseEnd_8025397] using wordTrace_append hprefix tailTrace_8025397
  have hstable : (prefixWord ++ tailWord_8025397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025397).length < 2 ^ (prefixWord ++ tailWord_8025397).sum := by decide
  have hdescent : baseEnd_8025397 < baseStart_8025397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025400 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_8025400 : Nat := 118140960795 + 8025400 * 2 ^ 59
def prefixEnd_8025400 : Nat := 4983230072969 + 3 ^ 40 * 8025400 * 2
def baseEnd_8025400 : Nat := 4120887644593005819291863

theorem tailTrace_8025400 : CollatzResearch.WordTrace tailWord_8025400 prefixEnd_8025400 4120887644593005819291863 := by
  unfold tailWord_8025400
  simp only [CollatzResearch.WordTrace]
  refine ⟨146355192562676952021872827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195140256750235936029163769 146355192562676952021872827)
  ·
    refine ⟨219532788844015428032809241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146355192562676952021872827 219532788844015428032809241)
    ·
      refine ⟨164649591633011571024606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219532788844015428032809241 164649591633011571024606931)
      ·
        refine ⟨246974387449517356536910397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164649591633011571024606931 246974387449517356536910397)
        ·
          refine ⟨92615395293569008701341399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246974387449517356536910397 92615395293569008701341399)
          ·
            refine ⟨138923092940353513052012099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92615395293569008701341399 138923092940353513052012099)
            ·
              refine ⟨208384639410530269578018149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138923092940353513052012099 208384639410530269578018149)
              ·
                refine ⟨39072119889474425545878403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208384639410530269578018149 39072119889474425545878403)
                ·
                  refine ⟨58608179834211638318817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39072119889474425545878403 58608179834211638318817605)
                  ·
                    refine ⟨10989033718914682184778301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58608179834211638318817605 10989033718914682184778301)
                    ·
                      refine ⟨4120887644593005819291863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989033718914682184778301 4120887644593005819291863)
                      ·
                        rfl

theorem cell23_8025400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_8025400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025400 prefixEnd_8025400 := by exact prefixLift 8025400
  have htrace : WordTrace (prefixWord ++ tailWord_8025400) baseStart_8025400 baseEnd_8025400 := by
    simpa [prefixWord, tailWord_8025400, baseEnd_8025400] using wordTrace_append hprefix tailTrace_8025400
  have hstable : (prefixWord ++ tailWord_8025400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025400).length < 2 ^ (prefixWord ++ tailWord_8025400).sum := by decide
  have hdescent : baseEnd_8025400 < baseStart_8025400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025407 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 3, 4]
def baseStart_8025407 : Nat := 118140960795 + 8025407 * 2 ^ 59
def prefixEnd_8025407 : Nat := 4983230072969 + 3 ^ 40 * 8025407 * 2
def baseEnd_8025407 : Nat := 1373630412985862430634777

theorem tailTrace_8025407 : CollatzResearch.WordTrace tailWord_8025407 prefixEnd_8025407 1373630412985862430634777 := by
  unfold tailWord_8025407
  simp only [CollatzResearch.WordTrace]
  refine ⟨292710640436328544239250475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195140426957552362826166983 292710640436328544239250475)
  ·
    refine ⟨439065960654492816358875713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292710640436328544239250475 439065960654492816358875713)
    ·
      refine ⟨329299470490869612269156785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439065960654492816358875713 329299470490869612269156785)
      ·
        refine ⟨246974602868152209201867589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329299470490869612269156785 246974602868152209201867589)
        ·
          refine ⟨46307738037778539225350173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246974602868152209201867589 46307738037778539225350173)
          ·
            refine ⟨17365401764166952209506315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46307738037778539225350173 17365401764166952209506315)
            ·
              refine ⟨26048102646250428314259473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17365401764166952209506315 26048102646250428314259473)
              ·
                refine ⟨19536076984687821235694605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26048102646250428314259473 19536076984687821235694605)
                ·
                  refine ⟨7326028869257932963385477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19536076984687821235694605 7326028869257932963385477)
                  ·
                    refine ⟨1373630412985862430634777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326028869257932963385477 1373630412985862430634777)
                    ·
                      rfl

theorem cell23_8025407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_8025407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025407 prefixEnd_8025407 := by exact prefixLift 8025407
  have htrace : WordTrace (prefixWord ++ tailWord_8025407) baseStart_8025407 baseEnd_8025407 := by
    simpa [prefixWord, tailWord_8025407, baseEnd_8025407] using wordTrace_append hprefix tailTrace_8025407
  have hstable : (prefixWord ++ tailWord_8025407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025407).length < 2 ^ (prefixWord ++ tailWord_8025407).sum := by decide
  have hdescent : baseEnd_8025407 < baseStart_8025407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025417 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_8025417 : Nat := 118140960795 + 8025417 * 2 ^ 59
def prefixEnd_8025417 : Nat := 4983230072969 + 3 ^ 40 * 8025417 * 2
def baseEnd_8025417 : Nat := 4120896373764132252779285

theorem tailTrace_8025417 : CollatzResearch.WordTrace tailWord_8025417 prefixEnd_8025417 4120896373764132252779285 := by
  unfold tailWord_8025417
  simp only [CollatzResearch.WordTrace]
  refine ⟨292711005166292315947114505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195140670110861543964743003 292711005166292315947114505)
  ·
    refine ⟨219533253874719236960335879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292711005166292315947114505 219533253874719236960335879)
    ·
      refine ⟨329299880812078855440503819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219533253874719236960335879 329299880812078855440503819)
      ·
        refine ⟨493949821218118283160755729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329299880812078855440503819 493949821218118283160755729)
        ·
          refine ⟨370462365913588712370566797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493949821218118283160755729 370462365913588712370566797)
          ·
            refine ⟨138923387217595767138962549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370462365913588712370566797 138923387217595767138962549)
            ·
              refine ⟨13024067551649603169277739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138923387217595767138962549 13024067551649603169277739)
              ·
                refine ⟨19536101327474404753916609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024067551649603169277739 19536101327474404753916609)
                ·
                  refine ⟨14652075995605803565437457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19536101327474404753916609 14652075995605803565437457)
                  ·
                    refine ⟨10989056996704352674078093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14652075995605803565437457 10989056996704352674078093)
                    ·
                      refine ⟨4120896373764132252779285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989056996704352674078093 4120896373764132252779285)
                      ·
                        rfl

theorem cell23_8025417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_8025417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025417 prefixEnd_8025417 := by exact prefixLift 8025417
  have htrace : WordTrace (prefixWord ++ tailWord_8025417) baseStart_8025417 baseEnd_8025417 := by
    simpa [prefixWord, tailWord_8025417, baseEnd_8025417] using wordTrace_append hprefix tailTrace_8025417
  have hstable : (prefixWord ++ tailWord_8025417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025417).length < 2 ^ (prefixWord ++ tailWord_8025417).sum := by decide
  have hdescent : baseEnd_8025417 < baseStart_8025417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025424 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 1, 4]
def baseStart_8025424 : Nat := 118140960795 + 8025424 * 2 ^ 59
def prefixEnd_8025424 : Nat := 4983230072969 + 3 ^ 40 * 8025424 * 2
def baseEnd_8025424 : Nat := 1373633322709571241797251

theorem tailTrace_8025424 : CollatzResearch.WordTrace tailWord_8025424 prefixEnd_8025424 1373633322709571241797251 := by
  unfold tailWord_8025424
  simp only [CollatzResearch.WordTrace]
  refine ⟨146355630238633478071309663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195140840318177970761746217 146355630238633478071309663)
  ·
    refine ⟨219533445357950217106964495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146355630238633478071309663 219533445357950217106964495)
    ·
      refine ⟨329300168036925325660446743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219533445357950217106964495 329300168036925325660446743)
      ·
        refine ⟨493950252055387988490670115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329300168036925325660446743 493950252055387988490670115)
        ·
          refine ⟨740925378083081982736005173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493950252055387988490670115 740925378083081982736005173)
          ·
            refine ⟨69461754195288935881500485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740925378083081982736005173 69461754195288935881500485)
            ·
              refine ⟨13024078911616675477781341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69461754195288935881500485 13024078911616675477781341)
              ·
                refine ⟨4884029591856253304168003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024078911616675477781341 4884029591856253304168003)
                ·
                  refine ⟨7326044387784379956252005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884029591856253304168003 7326044387784379956252005)
                  ·
                    refine ⟨1373633322709571241797251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326044387784379956252005 1373633322709571241797251)
                    ·
                      rfl

theorem cell23_8025424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_8025424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025424 prefixEnd_8025424 := by exact prefixLift 8025424
  have htrace : WordTrace (prefixWord ++ tailWord_8025424) baseStart_8025424 baseEnd_8025424 := by
    simpa [prefixWord, tailWord_8025424, baseEnd_8025424] using wordTrace_append hprefix tailTrace_8025424
  have hstable : (prefixWord ++ tailWord_8025424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025424).length < 2 ^ (prefixWord ++ tailWord_8025424).sum := by decide
  have hdescent : baseEnd_8025424 < baseStart_8025424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025440 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_8025440 : Nat := 118140960795 + 8025440 * 2 ^ 59
def prefixEnd_8025440 : Nat := 4983230072969 + 3 ^ 40 * 8025440 * 2
def baseEnd_8025440 : Nat := 4120908183819185662791679

theorem tailTrace_8025440 : CollatzResearch.WordTrace tailWord_8025440 prefixEnd_8025440 4120908183819185662791679 := by
  unfold tailWord_8025440
  simp only [CollatzResearch.WordTrace]
  refine ⟨146355922022604495437600887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195141229363472660583467849 146355922022604495437600887)
  ·
    refine ⟨219533883033906743156401331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146355922022604495437600887 219533883033906743156401331)
    ·
      refine ⟨329300824550860114734601997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219533883033906743156401331 329300824550860114734601997)
      ·
        refine ⟨123487809206572543025475749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329300824550860114734601997 123487809206572543025475749)
        ·
          refine ⟨23153964226232351817276703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123487809206572543025475749 23153964226232351817276703)
          ·
            refine ⟨34730946339348527725915055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153964226232351817276703 34730946339348527725915055)
            ·
              refine ⟨52096419509022791588872583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34730946339348527725915055 52096419509022791588872583)
              ·
                refine ⟨78144629263534187383308875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52096419509022791588872583 78144629263534187383308875)
                ·
                  refine ⟨117216943895301281074963313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78144629263534187383308875 117216943895301281074963313)
                  ·
                    refine ⟨87912707921475960806222485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117216943895301281074963313 87912707921475960806222485)
                    ·
                      refine ⟨4120908183819185662791679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87912707921475960806222485 4120908183819185662791679)
                      ·
                        rfl

theorem cell23_8025440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_8025440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025440 prefixEnd_8025440 := by exact prefixLift 8025440
  have htrace : WordTrace (prefixWord ++ tailWord_8025440) baseStart_8025440 baseEnd_8025440 := by
    simpa [prefixWord, tailWord_8025440, baseEnd_8025440] using wordTrace_append hprefix tailTrace_8025440
  have hstable : (prefixWord ++ tailWord_8025440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025440).length < 2 ^ (prefixWord ++ tailWord_8025440).sum := by decide
  have hdescent : baseEnd_8025440 < baseStart_8025440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025457 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_8025457 : Nat := 118140960795 + 8025457 * 2 ^ 59
def prefixEnd_8025457 : Nat := 4983230072969 + 3 ^ 40 * 8025457 * 2
def baseEnd_8025457 : Nat := 4120916912990312096279101

theorem tailTrace_8025457 : CollatzResearch.WordTrace tailWord_8025457 prefixEnd_8025457 4120916912990312096279101 := by
  unfold tailWord_8025457
  simp only [CollatzResearch.WordTrace]
  refine ⟨292712464086147402778570625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195141642724098268519047083 292712464086147402778570625)
  ·
    refine ⟨219534348064610552083927969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292712464086147402778570625 219534348064610552083927969)
    ·
      refine ⟨164650761048457914062945977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219534348064610552083927969 164650761048457914062945977)
      ·
        refine ⟨123488070786343435547209483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164650761048457914062945977 123488070786343435547209483)
        ·
          refine ⟨185232106179515153320814225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123488070786343435547209483 185232106179515153320814225)
          ·
            refine ⟨138924079634636364990610669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185232106179515153320814225 138924079634636364990610669)
            ·
              refine ⟨52096529862988636871479001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138924079634636364990610669 52096529862988636871479001)
              ·
                refine ⟨39072397397241477653609251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52096529862988636871479001 39072397397241477653609251)
                ·
                  refine ⟨58608596095862216480413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39072397397241477653609251 58608596095862216480413877)
                  ·
                    refine ⟨5494555883987082795038801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58608596095862216480413877 5494555883987082795038801)
                    ·
                      refine ⟨4120916912990312096279101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494555883987082795038801 4120916912990312096279101)
                      ·
                        rfl

theorem cell23_8025457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_8025457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025457 prefixEnd_8025457 := by exact prefixLift 8025457
  have htrace : WordTrace (prefixWord ++ tailWord_8025457) baseStart_8025457 baseEnd_8025457 := by
    simpa [prefixWord, tailWord_8025457, baseEnd_8025457] using wordTrace_append hprefix tailTrace_8025457
  have hstable : (prefixWord ++ tailWord_8025457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025457).length < 2 ^ (prefixWord ++ tailWord_8025457).sum := by decide
  have hdescent : baseEnd_8025457 < baseStart_8025457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025467 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 1, 5]
def baseStart_8025467 : Nat := 118140960795 + 8025467 * 2 ^ 59
def prefixEnd_8025467 : Nat := 4983230072969 + 3 ^ 40 * 8025467 * 2
def baseEnd_8025467 : Nat := 1373640682598952352384685

theorem tailTrace_8025467 : CollatzResearch.WordTrace tailWord_8025467 prefixEnd_8025467 1373640682598952352384685 := by
  unfold tailWord_8025467
  simp only [CollatzResearch.WordTrace]
  refine ⟨292712828816111174486434655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195141885877407449657623103 292712828816111174486434655)
  ·
    refine ⟨439069243224166761729651983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292712828816111174486434655 439069243224166761729651983)
    ·
      refine ⟨658603864836250142594477975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439069243224166761729651983 658603864836250142594477975)
      ·
        refine ⟨987905797254375213891716963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658603864836250142594477975 987905797254375213891716963)
        ·
          refine ⟨1481858695881562820837575445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987905797254375213891716963 1481858695881562820837575445)
          ·
            refine ⟨69462126369448257226761349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1481858695881562820837575445 69462126369448257226761349)
            ·
              refine ⟨13024148694271548230017753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69462126369448257226761349 13024148694271548230017753)
              ·
                refine ⟨9768111520703661172513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13024148694271548230017753 9768111520703661172513315)
                ·
                  refine ⟨14652167281055491758769973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9768111520703661172513315 14652167281055491758769973)
                  ·
                    refine ⟨1373640682598952352384685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14652167281055491758769973 1373640682598952352384685)
                    ·
                      rfl

theorem cell23_8025467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 5].length) (baseStart_8025467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025467 prefixEnd_8025467 := by exact prefixLift 8025467
  have htrace : WordTrace (prefixWord ++ tailWord_8025467) baseStart_8025467 baseEnd_8025467 := by
    simpa [prefixWord, tailWord_8025467, baseEnd_8025467] using wordTrace_append hprefix tailTrace_8025467
  have hstable : (prefixWord ++ tailWord_8025467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025467).length < 2 ^ (prefixWord ++ tailWord_8025467).sum := by decide
  have hdescent : baseEnd_8025467 < baseStart_8025467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025497 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_8025497 : Nat := 118140960795 + 8025497 * 2 ^ 59
def prefixEnd_8025497 : Nat := 4983230072969 + 3 ^ 40 * 8025497 * 2
def baseEnd_8025497 : Nat := 1373645817405497313259639

theorem tailTrace_8025497 : CollatzResearch.WordTrace tailWord_8025497 prefixEnd_8025497 1373645817405497313259639 := by
  unfold tailWord_8025497
  simp only [CollatzResearch.WordTrace]
  refine ⟨292713923006002489610026745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195142615337334993073351163 292713923006002489610026745)
  ·
    refine ⟨219535442254501867207520059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292713923006002489610026745 219535442254501867207520059)
    ·
      refine ⟨329303163381752800811280089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219535442254501867207520059 329303163381752800811280089)
      ·
        refine ⟨246977372536314600608460067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329303163381752800811280089 246977372536314600608460067)
        ·
          refine ⟨370466058804471900912690101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246977372536314600608460067 370466058804471900912690101)
          ·
            refine ⟨34731193012919240710564697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370466058804471900912690101 34731193012919240710564697)
            ·
              refine ⟨26048394759689430532923523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34731193012919240710564697 26048394759689430532923523)
              ·
                refine ⟨39072592139534145799385285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26048394759689430532923523 39072592139534145799385285)
                ·
                  refine ⟨7326111026162652337384741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39072592139534145799385285 7326111026162652337384741)
                  ·
                    refine ⟨1373645817405497313259639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326111026162652337384741 1373645817405497313259639)
                    ·
                      rfl

theorem cell23_8025497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_8025497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025497 prefixEnd_8025497 := by exact prefixLift 8025497
  have htrace : WordTrace (prefixWord ++ tailWord_8025497) baseStart_8025497 baseEnd_8025497 := by
    simpa [prefixWord, tailWord_8025497, baseEnd_8025497] using wordTrace_append hprefix tailTrace_8025497
  have hstable : (prefixWord ++ tailWord_8025497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025497).length < 2 ^ (prefixWord ++ tailWord_8025497).sum := by decide
  have hdescent : baseEnd_8025497 < baseStart_8025497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025498 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_8025498 : Nat := 118140960795 + 8025498 * 2 ^ 59
def prefixEnd_8025498 : Nat := 4983230072969 + 3 ^ 40 * 8025498 * 2
def baseEnd_8025498 : Nat := 4120937965697146435866413

theorem tailTrace_8025498 : CollatzResearch.WordTrace tailWord_8025498 prefixEnd_8025498 4120937965697146435866413 := by
  unfold tailWord_8025498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73178489869749716695203287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195142639652665911187208765 73178489869749716695203287)
  ·
    refine ⟨109767734804624575042804931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73178489869749716695203287 109767734804624575042804931)
    ·
      refine ⟨164651602206936862564207397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109767734804624575042804931 164651602206936862564207397)
      ·
        refine ⟨30872175413800661730788887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164651602206936862564207397 30872175413800661730788887)
        ·
          refine ⟨46308263120700992596183331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30872175413800661730788887 46308263120700992596183331)
          ·
            refine ⟨69462394681051488894274997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46308263120700992596183331 69462394681051488894274997)
            ·
              refine ⟨6512099501348577083838281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69462394681051488894274997 6512099501348577083838281)
              ·
                refine ⟨4884074626011432812878711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512099501348577083838281 4884074626011432812878711)
                ·
                  refine ⟨7326111939017149219318067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884074626011432812878711 7326111939017149219318067)
                  ·
                    refine ⟨10989167908525723828977101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7326111939017149219318067 10989167908525723828977101)
                    ·
                      refine ⟨4120937965697146435866413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989167908525723828977101 4120937965697146435866413)
                      ·
                        rfl

theorem cell23_8025498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_8025498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025498 prefixEnd_8025498 := by exact prefixLift 8025498
  have htrace : WordTrace (prefixWord ++ tailWord_8025498) baseStart_8025498 baseEnd_8025498 := by
    simpa [prefixWord, tailWord_8025498, baseEnd_8025498] using wordTrace_append hprefix tailTrace_8025498
  have hstable : (prefixWord ++ tailWord_8025498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025498).length < 2 ^ (prefixWord ++ tailWord_8025498).sum := by decide
  have hdescent : baseEnd_8025498 < baseStart_8025498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025507 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3]
def baseStart_8025507 : Nat := 118140960795 + 8025507 * 2 ^ 59
def prefixEnd_8025507 : Nat := 4983230072969 + 3 ^ 40 * 8025507 * 2
def baseEnd_8025507 : Nat := 4120942587023036900653871

theorem tailTrace_8025507 : CollatzResearch.WordTrace tailWord_8025507 prefixEnd_8025507 4120942587023036900653871 := by
  unfold tailWord_8025507
  simp only [CollatzResearch.WordTrace]
  refine ⟨292714287735966261317890775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195142858490644174211927183 292714287735966261317890775)
  ·
    refine ⟨439071431603949391976836163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292714287735966261317890775 439071431603949391976836163)
    ·
      refine ⟨658607147405924087965254245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439071431603949391976836163 658607147405924087965254245)
      ·
        refine ⟨123488840138610766493485171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 658607147405924087965254245 123488840138610766493485171)
        ·
          refine ⟨185233260207916149740227757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123488840138610766493485171 185233260207916149740227757)
          ·
            refine ⟨69462472577968556152585409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185233260207916149740227757 69462472577968556152585409)
            ·
              refine ⟨52096854433476417114439057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69462472577968556152585409 52096854433476417114439057)
              ·
                refine ⟨39072640825107312835829293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52096854433476417114439057 39072640825107312835829293)
                ·
                  refine ⟨14652240309415242313435985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39072640825107312835829293 14652240309415242313435985)
                  ·
                    refine ⟨10989180232061431735076989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14652240309415242313435985 10989180232061431735076989)
                    ·
                      refine ⟨4120942587023036900653871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989180232061431735076989 4120942587023036900653871)
                      ·
                        rfl

theorem cell23_8025507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_8025507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025507 prefixEnd_8025507 := by exact prefixLift 8025507
  have htrace : WordTrace (prefixWord ++ tailWord_8025507) baseStart_8025507 baseEnd_8025507 := by
    simpa [prefixWord, tailWord_8025507, baseEnd_8025507] using wordTrace_append hprefix tailTrace_8025507
  have hstable : (prefixWord ++ tailWord_8025507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025507).length < 2 ^ (prefixWord ++ tailWord_8025507).sum := by decide
  have hdescent : baseEnd_8025507 < baseStart_8025507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025571 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 3]
def baseStart_8025571 : Nat := 118140960795 + 8025571 * 2 ^ 59
def prefixEnd_8025571 : Nat := 4983230072969 + 3 ^ 40 * 8025571 * 2
def baseEnd_8025571 : Nat := 4120975449784924650253577

theorem tailTrace_8025571 : CollatzResearch.WordTrace tailWord_8025571 prefixEnd_8025571 4120975449784924650253577 := by
  unfold tailWord_8025571
  simp only [CollatzResearch.WordTrace]
  refine ⟨292716622007734400248220567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195144414671822933498813711 292716622007734400248220567)
  ·
    refine ⟨439074933011601600372330851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292716622007734400248220567 439074933011601600372330851)
    ·
      refine ⟨658612399517402400558496277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439074933011601600372330851 658612399517402400558496277)
      ·
        refine ⟨30872456227378237526179513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 658612399517402400558496277 30872456227378237526179513)
        ·
          refine ⟨23154342170533678144634635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30872456227378237526179513 23154342170533678144634635)
          ·
            refine ⟨34731513255800517216951953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23154342170533678144634635 34731513255800517216951953)
            ·
              refine ⟨26048634941850387912713965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34731513255800517216951953 26048634941850387912713965)
              ·
                refine ⟨9768238103193895467267737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26048634941850387912713965 9768238103193895467267737)
                ·
                  refine ⟨7326178577395421600450803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9768238103193895467267737 7326178577395421600450803)
                  ·
                    refine ⟨10989267866093132400676205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7326178577395421600450803 10989267866093132400676205)
                    ·
                      refine ⟨4120975449784924650253577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989267866093132400676205 4120975449784924650253577)
                      ·
                        rfl

theorem cell23_8025571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_8025571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025571 prefixEnd_8025571 := by exact prefixLift 8025571
  have htrace : WordTrace (prefixWord ++ tailWord_8025571) baseStart_8025571 baseEnd_8025571 := by
    simpa [prefixWord, tailWord_8025571, baseEnd_8025571] using wordTrace_append hprefix tailTrace_8025571
  have hstable : (prefixWord ++ tailWord_8025571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025571).length < 2 ^ (prefixWord ++ tailWord_8025571).sum := by decide
  have hdescent : baseEnd_8025571 < baseStart_8025571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025594 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_8025594 : Nat := 118140960795 + 8025594 * 2 ^ 59
def prefixEnd_8025594 : Nat := 4983230072969 + 3 ^ 40 * 8025594 * 2
def baseEnd_8025594 : Nat := 4120987259839978060265971

theorem tailTrace_8025594 : CollatzResearch.WordTrace tailWord_8025594 prefixEnd_8025594 4120987259839978060265971 := by
  unfold tailWord_8025594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73179365221662768794076959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195144973924434050117538557 73179365221662768794076959)
  ·
    refine ⟨109769047832494153191115439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73179365221662768794076959 109769047832494153191115439)
    ·
      refine ⟨164653571748741229786673159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109769047832494153191115439 164653571748741229786673159)
      ·
        refine ⟨246980357623111844680009739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164653571748741229786673159 246980357623111844680009739)
        ·
          refine ⟨370470536434667767020014609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246980357623111844680009739 370470536434667767020014609)
          ·
            refine ⟨277852902326000825265010957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370470536434667767020014609 277852902326000825265010957)
            ·
              refine ⟨104194838372250309474379109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277852902326000825265010957 104194838372250309474379109)
              ·
                refine ⟨19536532194796933026446083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104194838372250309474379109 19536532194796933026446083)
                ·
                  refine ⟨29304798292195399539669125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19536532194796933026446083 29304798292195399539669125)
                  ·
                    refine ⟨5494649679786637413687961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29304798292195399539669125 5494649679786637413687961)
                    ·
                      refine ⟨4120987259839978060265971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494649679786637413687961 4120987259839978060265971)
                      ·
                        rfl

theorem cell23_8025594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_8025594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025594 prefixEnd_8025594 := by exact prefixLift 8025594
  have htrace : WordTrace (prefixWord ++ tailWord_8025594) baseStart_8025594 baseEnd_8025594 := by
    simpa [prefixWord, tailWord_8025594, baseEnd_8025594] using wordTrace_append hprefix tailTrace_8025594
  have hstable : (prefixWord ++ tailWord_8025594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025594).length < 2 ^ (prefixWord ++ tailWord_8025594).sum := by decide
  have hdescent : baseEnd_8025594 < baseStart_8025594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025617 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 7]
def baseStart_8025617 : Nat := 118140960795 + 8025617 * 2 ^ 59
def prefixEnd_8025617 : Nat := 4983230072969 + 3 ^ 40 * 8025617 * 2
def baseEnd_8025617 : Nat := 457888785543892385586485

theorem tailTrace_8025617 : CollatzResearch.WordTrace tailWord_8025617 prefixEnd_8025617 457888785543892385586485 := by
  unfold tailWord_8025617
  simp only [CollatzResearch.WordTrace]
  refine ⟨292718299765567750104395105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195145533177045166736263403 292718299765567750104395105)
  ·
    refine ⟨219538724824175812578296329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292718299765567750104395105 219538724824175812578296329)
    ·
      refine ⟨164654043618131859433722247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219538724824175812578296329 164654043618131859433722247)
      ·
        refine ⟨246981065427197789150583371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164654043618131859433722247 246981065427197789150583371)
        ·
          refine ⟨370471598140796683725875057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246981065427197789150583371 370471598140796683725875057)
          ·
            refine ⟨277853698605597512794406293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370471598140796683725875057 277853698605597512794406293)
            ·
              refine ⟨13024392122137383412237795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277853698605597512794406293 13024392122137383412237795)
              ·
                refine ⟨19536588183206075118356693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024392122137383412237795 19536588183206075118356693)
                ·
                  refine ⟨457888785543892385586485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19536588183206075118356693 457888785543892385586485)
                  ·
                    rfl

theorem cell23_8025617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_8025617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025617 prefixEnd_8025617 := by exact prefixLift 8025617
  have htrace : WordTrace (prefixWord ++ tailWord_8025617) baseStart_8025617 baseEnd_8025617 := by
    simpa [prefixWord, tailWord_8025617, baseEnd_8025617] using wordTrace_append hprefix tailTrace_8025617
  have hstable : (prefixWord ++ tailWord_8025617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025617).length < 2 ^ (prefixWord ++ tailWord_8025617).sum := by decide
  have hdescent : baseEnd_8025617 < baseStart_8025617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025651 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 5]
def baseStart_8025651 : Nat := 118140960795 + 8025651 * 2 ^ 59
def prefixEnd_8025651 : Nat := 4983230072969 + 3 ^ 40 * 8025651 * 2
def baseEnd_8025651 : Nat := 457890725359698259694801

theorem tailTrace_8025651 : CollatzResearch.WordTrace tailWord_8025651 prefixEnd_8025651 457890725359698259694801 := by
  unfold tailWord_8025651
  simp only [CollatzResearch.WordTrace]
  refine ⟨292719539847444573911132807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195146359898296382607421871 292719539847444573911132807)
  ·
    refine ⟨439079309771166860866699211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292719539847444573911132807 439079309771166860866699211)
    ·
      refine ⟨658618964656750291300048817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439079309771166860866699211 658618964656750291300048817)
      ·
        refine ⟨493964223492562718475036613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658618964656750291300048817 493964223492562718475036613)
        ·
          refine ⟨92618291904855509714069365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493964223492562718475036613 92618291904855509714069365)
          ·
            refine ⟨8682964866080204035694003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92618291904855509714069365 8682964866080204035694003)
            ·
              refine ⟨13024447299120306053541005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682964866080204035694003 13024447299120306053541005)
              ·
                refine ⟨4884167737170114770077877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024447299120306053541005 4884167737170114770077877)
                ·
                  refine ⟨457890725359698259694801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884167737170114770077877 457890725359698259694801)
                  ·
                    rfl

theorem cell23_8025651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 5].length) (baseStart_8025651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025651 prefixEnd_8025651 := by exact prefixLift 8025651
  have htrace : WordTrace (prefixWord ++ tailWord_8025651) baseStart_8025651 baseEnd_8025651 := by
    simpa [prefixWord, tailWord_8025651, baseEnd_8025651] using wordTrace_append hprefix tailTrace_8025651
  have hstable : (prefixWord ++ tailWord_8025651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025651).length < 2 ^ (prefixWord ++ tailWord_8025651).sum := by decide
  have hdescent : baseEnd_8025651 < baseStart_8025651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025684 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_8025684 : Nat := 118140960795 + 8025684 * 2 ^ 59
def prefixEnd_8025684 : Nat := 4983230072969 + 3 ^ 40 * 8025684 * 2
def baseEnd_8025684 : Nat := 4121033473098882708140557

theorem tailTrace_8025684 : CollatzResearch.WordTrace tailWord_8025684 prefixEnd_8025684 4121033473098882708140557 := by
  unfold tailWord_8025684
  simp only [CollatzResearch.WordTrace]
  refine ⟨146360371728162510273542053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195147162304216680364722737 146360371728162510273542053)
  ·
    refine ⟨27442569699030470676289135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146360371728162510273542053 27442569699030470676289135)
    ·
      refine ⟨41163854548545706014433703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27442569699030470676289135 41163854548545706014433703)
      ·
        refine ⟨61745781822818559021650555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41163854548545706014433703 61745781822818559021650555)
        ·
          refine ⟨92618672734227838532475833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61745781822818559021650555 92618672734227838532475833)
          ·
            refine ⟨69464004550670878899356875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92618672734227838532475833 69464004550670878899356875)
            ·
              refine ⟨104196006826006318349035313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69464004550670878899356875 104196006826006318349035313)
              ·
                refine ⟨78147005119504738761776485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104196006826006318349035313 78147005119504738761776485)
                ·
                  refine ⟨14652563459907138517833091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78147005119504738761776485 14652563459907138517833091)
                  ·
                    refine ⟨21978845189860707776749637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14652563459907138517833091 21978845189860707776749637)
                    ·
                      refine ⟨4121033473098882708140557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21978845189860707776749637 4121033473098882708140557)
                      ·
                        rfl

theorem cell23_8025684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_8025684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025684 prefixEnd_8025684 := by exact prefixLift 8025684
  have htrace : WordTrace (prefixWord ++ tailWord_8025684) baseStart_8025684 baseEnd_8025684 := by
    simpa [prefixWord, tailWord_8025684, baseEnd_8025684] using wordTrace_append hprefix tailTrace_8025684
  have hstable : (prefixWord ++ tailWord_8025684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025684).length < 2 ^ (prefixWord ++ tailWord_8025684).sum := by decide
  have hdescent : baseEnd_8025684 < baseStart_8025684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025701 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_8025701 : Nat := 118140960795 + 8025701 * 2 ^ 59
def prefixEnd_8025701 : Nat := 4983230072969 + 3 ^ 40 * 8025701 * 2
def baseEnd_8025701 : Nat := 4121042202270009141627979

theorem tailTrace_8025701 : CollatzResearch.WordTrace tailWord_8025701 prefixEnd_8025701 4121042202270009141627979 := by
  unfold tailWord_8025701
  simp only [CollatzResearch.WordTrace]
  refine ⟨292721363497263432450452957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195147575664842288300301971 292721363497263432450452957)
  ·
    refine ⟨109770511311473787168919859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292721363497263432450452957 109770511311473787168919859)
    ·
      refine ⟨164655766967210680753379789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109770511311473787168919859 164655766967210680753379789)
      ·
        refine ⟨61745912612704005282517421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164655766967210680753379789 61745912612704005282517421)
        ·
          refine ⟨23154717229764001980944033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61745912612704005282517421 23154717229764001980944033)
          ·
            refine ⟨17366037922323001485708025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23154717229764001980944033 17366037922323001485708025)
            ·
              refine ⟨13024528441742251114281019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17366037922323001485708025 13024528441742251114281019)
              ·
                refine ⟨19536792662613376671421529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024528441742251114281019 19536792662613376671421529)
                ·
                  refine ⟨14652594496960032503566147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19536792662613376671421529 14652594496960032503566147)
                  ·
                    refine ⟨21978891745440048755349221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14652594496960032503566147 21978891745440048755349221)
                    ·
                      refine ⟨4121042202270009141627979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21978891745440048755349221 4121042202270009141627979)
                      ·
                        rfl

theorem cell23_8025701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_8025701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025701 prefixEnd_8025701 := by exact prefixLift 8025701
  have htrace : WordTrace (prefixWord ++ tailWord_8025701) baseStart_8025701 baseEnd_8025701 := by
    simpa [prefixWord, tailWord_8025701, baseEnd_8025701] using wordTrace_append hprefix tailTrace_8025701
  have hstable : (prefixWord ++ tailWord_8025701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025701).length < 2 ^ (prefixWord ++ tailWord_8025701).sum := by decide
  have hdescent : baseEnd_8025701 < baseStart_8025701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025711 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 1, 4]
def baseStart_8025711 : Nat := 118140960795 + 8025711 * 2 ^ 59
def prefixEnd_8025711 : Nat := 4983230072969 + 3 ^ 40 * 8025711 * 2
def baseEnd_8025711 : Nat := 1373682445692184700834311

theorem tailTrace_8025711 : CollatzResearch.WordTrace tailWord_8025711 prefixEnd_8025711 1373682445692184700834311 := by
  unfold tailWord_8025711
  simp only [CollatzResearch.WordTrace]
  refine ⟨292721728227227204158316987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195147818818151469438877991 292721728227227204158316987)
  ·
    refine ⟨439082592340840806237475481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292721728227227204158316987 439082592340840806237475481)
    ·
      refine ⟨329311944255630604678106611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439082592340840806237475481 329311944255630604678106611)
      ·
        refine ⟨493967916383445907017159917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329311944255630604678106611 493967916383445907017159917)
        ·
          refine ⟨185237968643792215131434969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493967916383445907017159917 185237968643792215131434969)
          ·
            refine ⟨138928476482844161348576227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185237968643792215131434969 138928476482844161348576227)
            ·
              refine ⟨208392714724266242022864341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138928476482844161348576227 208392714724266242022864341)
              ·
                refine ⟨4884204251349990047410883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208392714724266242022864341 4884204251349990047410883)
                ·
                  refine ⟨7326306377024985071116325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884204251349990047410883 7326306377024985071116325)
                  ·
                    refine ⟨1373682445692184700834311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326306377024985071116325 1373682445692184700834311)
                    ·
                      rfl

theorem cell23_8025711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_8025711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025711 prefixEnd_8025711 := by exact prefixLift 8025711
  have htrace : WordTrace (prefixWord ++ tailWord_8025711) baseStart_8025711 baseEnd_8025711 := by
    simpa [prefixWord, tailWord_8025711, baseEnd_8025711] using wordTrace_append hprefix tailTrace_8025711
  have hstable : (prefixWord ++ tailWord_8025711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025711).length < 2 ^ (prefixWord ++ tailWord_8025711).sum := by decide
  have hdescent : baseEnd_8025711 < baseStart_8025711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025751 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_8025751 : Nat := 118140960795 + 8025751 * 2 ^ 59
def prefixEnd_8025751 : Nat := 4983230072969 + 3 ^ 40 * 8025751 * 2
def baseEnd_8025751 : Nat := 4121067876302733946002749

theorem tailTrace_8025751 : CollatzResearch.WordTrace tailWord_8025751 prefixEnd_8025751 4121067876302733946002749 := by
  unfold tailWord_8025751
  simp only [CollatzResearch.WordTrace]
  refine ⟨292723187147082290989773107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195148791431388193993182071 292723187147082290989773107)
  ·
    refine ⟨439084780720623436484659661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292723187147082290989773107 439084780720623436484659661)
    ·
      refine ⟨164656792770233788681747373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439084780720623436484659661 164656792770233788681747373)
      ·
        refine ⟨61746297288837670755655265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164656792770233788681747373 61746297288837670755655265)
        ·
          refine ⟨46309722966628253066741449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61746297288837670755655265 46309722966628253066741449)
          ·
            refine ⟨34732292224971189800056087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46309722966628253066741449 34732292224971189800056087)
            ·
              refine ⟨52098438337456784700084131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34732292224971189800056087 52098438337456784700084131)
              ·
                refine ⟨78147657506185177050126197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52098438337456784700084131 78147657506185177050126197)
                ·
                  refine ⟨7326342891204860348449331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78147657506185177050126197 7326342891204860348449331)
                  ·
                    refine ⟨10989514336807290522673997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7326342891204860348449331 10989514336807290522673997)
                    ·
                      refine ⟨4121067876302733946002749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989514336807290522673997 4121067876302733946002749)
                      ·
                        rfl

theorem cell23_8025751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_8025751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025751 prefixEnd_8025751 := by exact prefixLift 8025751
  have htrace : WordTrace (prefixWord ++ tailWord_8025751) baseStart_8025751 baseEnd_8025751 := by
    simpa [prefixWord, tailWord_8025751, baseEnd_8025751] using wordTrace_append hprefix tailTrace_8025751
  have hstable : (prefixWord ++ tailWord_8025751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025751).length < 2 ^ (prefixWord ++ tailWord_8025751).sum := by decide
  have hdescent : baseEnd_8025751 < baseStart_8025751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025762 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_8025762 : Nat := 118140960795 + 8025762 * 2 ^ 59
def prefixEnd_8025762 : Nat := 4983230072969 + 3 ^ 40 * 8025762 * 2
def baseEnd_8025762 : Nat := 1373691174863311134321733

theorem tailTrace_8025762 : CollatzResearch.WordTrace tailWord_8025762 prefixEnd_8025762 1373691174863311134321733 := by
  unfold tailWord_8025762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180897087510609967105885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195149058900028293245615693 73180897087510609967105885)
  ·
    refine ⟨27442836407816478737664707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73180897087510609967105885 27442836407816478737664707)
    ·
      refine ⟨41164254611724718106497061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27442836407816478737664707 41164254611724718106497061)
      ·
        refine ⟨7718297739698384644968199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41164254611724718106497061 7718297739698384644968199)
        ·
          refine ⟨11577446609547576967452299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718297739698384644968199 11577446609547576967452299)
          ·
            refine ⟨17366169914321365451178449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577446609547576967452299 17366169914321365451178449)
            ·
              refine ⟨13024627435741024088383837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17366169914321365451178449 13024627435741024088383837)
              ·
                refine ⟨4884235288402884033143939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024627435741024088383837 4884235288402884033143939)
                ·
                  refine ⟨7326352932604326049715909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884235288402884033143939 7326352932604326049715909)
                  ·
                    refine ⟨1373691174863311134321733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326352932604326049715909 1373691174863311134321733)
                    ·
                      rfl

theorem cell23_8025762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_8025762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025762 prefixEnd_8025762 := by exact prefixLift 8025762
  have htrace : WordTrace (prefixWord ++ tailWord_8025762) baseStart_8025762 baseEnd_8025762 := by
    simpa [prefixWord, tailWord_8025762, baseEnd_8025762] using wordTrace_append hprefix tailTrace_8025762
  have hstable : (prefixWord ++ tailWord_8025762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025762).length < 2 ^ (prefixWord ++ tailWord_8025762).sum := by decide
  have hdescent : baseEnd_8025762 < baseStart_8025762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025805 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_8025805 : Nat := 118140960795 + 8025805 * 2 ^ 59
def prefixEnd_8025805 : Nat := 4983230072969 + 3 ^ 40 * 8025805 * 2
def baseEnd_8025805 : Nat := 1373698534752692244909167

theorem tailTrace_8025805 : CollatzResearch.WordTrace tailWord_8025805 prefixEnd_8025805 1373698534752692244909167 := by
  unfold tailWord_8025805
  simp only [CollatzResearch.WordTrace]
  refine ⟨292725156688886658212238869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195150104459257772141492579 292725156688886658212238869)
  ·
    refine ⟨13721491719791562103698697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292725156688886658212238869 13721491719791562103698697)
    ·
      refine ⟨10291118789843671577774023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13721491719791562103698697 10291118789843671577774023)
      ·
        refine ⟨15436678184765507366661035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291118789843671577774023 15436678184765507366661035)
        ·
          refine ⟨23155017277148261049991553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15436678184765507366661035 23155017277148261049991553)
          ·
            refine ⟨17366262957861195787493665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23155017277148261049991553 17366262957861195787493665)
            ·
              refine ⟨13024697218395896840620249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17366262957861195787493665 13024697218395896840620249)
              ·
                refine ⟨9768522913796922630465187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13024697218395896840620249 9768522913796922630465187)
                ·
                  refine ⟨14652784370695383945697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9768522913796922630465187 14652784370695383945697781)
                  ·
                    refine ⟨1373698534752692244909167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14652784370695383945697781 1373698534752692244909167)
                    ·
                      rfl

theorem cell23_8025805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_8025805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025805 prefixEnd_8025805 := by exact prefixLift 8025805
  have htrace : WordTrace (prefixWord ++ tailWord_8025805) baseStart_8025805 baseEnd_8025805 := by
    simpa [prefixWord, tailWord_8025805, baseEnd_8025805] using wordTrace_append hprefix tailTrace_8025805
  have hstable : (prefixWord ++ tailWord_8025805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025805).length < 2 ^ (prefixWord ++ tailWord_8025805).sum := by decide
  have hdescent : baseEnd_8025805 < baseStart_8025805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025858 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_8025858 : Nat := 118140960795 + 8025858 * 2 ^ 59
def prefixEnd_8025858 : Nat := 4983230072969 + 3 ^ 40 * 8025858 * 2
def baseEnd_8025858 : Nat := 4121122818732765027364757

theorem tailTrace_8025858 : CollatzResearch.WordTrace tailWord_8025858 prefixEnd_8025858 4121122818732765027364757 := by
  unfold tailWord_8025858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73181772439423662065979557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195151393171796432175945485 73181772439423662065979557)
  ·
    refine ⟨13721582332391936637371167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73181772439423662065979557 13721582332391936637371167)
    ·
      refine ⟨20582373498587904956056751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721582332391936637371167 20582373498587904956056751)
      ·
        refine ⟨30873560247881857434085127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20582373498587904956056751 30873560247881857434085127)
        ·
          refine ⟨46310340371822786151127691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30873560247881857434085127 46310340371822786151127691)
          ·
            refine ⟨69465510557734179226691537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46310340371822786151127691 69465510557734179226691537)
            ·
              refine ⟨52099132918300634420018653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69465510557734179226691537 52099132918300634420018653)
              ·
                refine ⟨19537174844362737907506995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52099132918300634420018653 19537174844362737907506995)
                ·
                  refine ⟨29305762266544106861260493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19537174844362737907506995 29305762266544106861260493)
                  ·
                    refine ⟨10989660849954040072972685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29305762266544106861260493 10989660849954040072972685)
                    ·
                      refine ⟨4121122818732765027364757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989660849954040072972685 4121122818732765027364757)
                      ·
                        rfl

theorem cell23_8025858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_8025858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025858 prefixEnd_8025858 := by exact prefixLift 8025858
  have htrace : WordTrace (prefixWord ++ tailWord_8025858) baseStart_8025858 baseEnd_8025858 := by
    simpa [prefixWord, tailWord_8025858, baseEnd_8025858] using wordTrace_append hprefix tailTrace_8025858
  have hstable : (prefixWord ++ tailWord_8025858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025858).length < 2 ^ (prefixWord ++ tailWord_8025858).sum := by decide
  have hdescent : baseEnd_8025858 < baseStart_8025858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025908 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_8025908 : Nat := 118140960795 + 8025908 * 2 ^ 59
def prefixEnd_8025908 : Nat := 4983230072969 + 3 ^ 40 * 8025908 * 2
def baseEnd_8025908 : Nat := 1373716164255163277246509

theorem tailTrace_8025908 : CollatzResearch.WordTrace tailWord_8025908 prefixEnd_8025908 1373716164255163277246509 := by
  unfold tailWord_8025908
  simp only [CollatzResearch.WordTrace]
  refine ⟨146364456703756753401619189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195152608938342337868825585 146364456703756753401619189)
  ·
    refine ⟨13721667815977195631401799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146364456703756753401619189 13721667815977195631401799)
    ·
      refine ⟨20582501723965793447102699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721667815977195631401799 20582501723965793447102699)
      ·
        refine ⟨30873752585948690170654049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20582501723965793447102699 30873752585948690170654049)
        ·
          refine ⟨23155314439461517627990537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30873752585948690170654049 23155314439461517627990537)
          ·
            refine ⟨17366485829596138220992903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23155314439461517627990537 17366485829596138220992903)
            ·
              refine ⟨26049728744394207331489355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366485829596138220992903 26049728744394207331489355)
              ·
                refine ⟨39074593116591310997234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26049728744394207331489355 39074593116591310997234033)
                ·
                  refine ⟨29305944837443483247925525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39074593116591310997234033 29305944837443483247925525)
                  ·
                    refine ⟨1373716164255163277246509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29305944837443483247925525 1373716164255163277246509)
                    ·
                      rfl

theorem cell23_8025908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_8025908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025908 prefixEnd_8025908 := by exact prefixLift 8025908
  have htrace : WordTrace (prefixWord ++ tailWord_8025908) baseStart_8025908 baseEnd_8025908 := by
    simpa [prefixWord, tailWord_8025908, baseEnd_8025908] using wordTrace_append hprefix tailTrace_8025908
  have hstable : (prefixWord ++ tailWord_8025908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025908).length < 2 ^ (prefixWord ++ tailWord_8025908).sum := by decide
  have hdescent : baseEnd_8025908 < baseStart_8025908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025938 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_8025938 : Nat := 118140960795 + 8025938 * 2 ^ 59
def prefixEnd_8025938 : Nat := 4983230072969 + 3 ^ 40 * 8025938 * 2
def baseEnd_8025938 : Nat := 457907099687236079373821

theorem tailTrace_8025938 : CollatzResearch.WordTrace tailWord_8025938 prefixEnd_8025938 457907099687236079373821 := by
  unfold tailWord_8025938
  simp only [CollatzResearch.WordTrace]
  refine ⟨73182501899351205481707617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195153338398269881284553645 73182501899351205481707617)
  ·
    refine ⟨54886876424513404111280713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73182501899351205481707617 54886876424513404111280713)
    ·
      refine ⟨41165157318385053083460535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54886876424513404111280713 41165157318385053083460535)
      ·
        refine ⟨61747735977577579625190803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41165157318385053083460535 61747735977577579625190803)
        ·
          refine ⟨92621603966366369437786205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61747735977577579625190803 92621603966366369437786205)
          ·
            refine ⟨34733101487387388539169827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92621603966366369437786205 34733101487387388539169827)
            ·
              refine ⟨52099652231081082808754741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34733101487387388539169827 52099652231081082808754741)
              ·
                refine ⟨4884342396663851513320757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52099652231081082808754741 4884342396663851513320757)
                ·
                  refine ⟨457907099687236079373821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884342396663851513320757 457907099687236079373821)
                  ·
                    rfl

theorem cell23_8025938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_8025938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025938 prefixEnd_8025938 := by exact prefixLift 8025938
  have htrace : WordTrace (prefixWord ++ tailWord_8025938) baseStart_8025938 baseEnd_8025938 := by
    simpa [prefixWord, tailWord_8025938, baseEnd_8025938] using wordTrace_append hprefix tailTrace_8025938
  have hstable : (prefixWord ++ tailWord_8025938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025938).length < 2 ^ (prefixWord ++ tailWord_8025938).sum := by decide
  have hdescent : baseEnd_8025938 < baseStart_8025938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8025988 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_8025988 : Nat := 118140960795 + 8025988 * 2 ^ 59
def prefixEnd_8025988 : Nat := 4983230072969 + 3 ^ 40 * 8025988 * 2
def baseEnd_8025988 : Nat := 4121189571217849518739159

theorem tailTrace_8025988 : CollatzResearch.WordTrace tailWord_8025988 prefixEnd_8025988 4121189571217849518739159 := by
  unfold tailWord_8025988
  simp only [CollatzResearch.WordTrace]
  refine ⟨146365915623611840233075309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195154554164815786977433745 146365915623611840233075309)
  ·
    refine ⟨54887218358854440087403241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146365915623611840233075309 54887218358854440087403241)
    ·
      refine ⟨41165413769140830065552431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54887218358854440087403241 41165413769140830065552431)
      ·
        refine ⟨61748120653711245098328647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41165413769140830065552431 61748120653711245098328647)
        ·
          refine ⟨92622180980566867647492971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61748120653711245098328647 92622180980566867647492971)
          ·
            refine ⟨138933271470850301471239457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92622180980566867647492971 138933271470850301471239457)
            ·
              refine ⟨104199953603137726103429593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138933271470850301471239457 104199953603137726103429593)
              ·
                refine ⟨78149965202353294577572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104199953603137726103429593 78149965202353294577572195)
                ·
                  refine ⟨117224947803529941866358293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78149965202353294577572195 117224947803529941866358293)
                  ·
                    refine ⟨5494919428290466024985545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117224947803529941866358293 5494919428290466024985545)
                    ·
                      refine ⟨4121189571217849518739159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5494919428290466024985545 4121189571217849518739159)
                      ·
                        rfl

theorem cell23_8025988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_8025988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8025988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8025988 prefixEnd_8025988 := by exact prefixLift 8025988
  have htrace : WordTrace (prefixWord ++ tailWord_8025988) baseStart_8025988 baseEnd_8025988 := by
    simpa [prefixWord, tailWord_8025988, baseEnd_8025988] using wordTrace_append hprefix tailTrace_8025988
  have hstable : (prefixWord ++ tailWord_8025988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8025988).length < 2 ^ (prefixWord ++ tailWord_8025988).sum := by decide
  have hdescent : baseEnd_8025988 < baseStart_8025988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8025988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026006 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_8026006 : Nat := 118140960795 + 8026006 * 2 ^ 59
def prefixEnd_8026006 : Nat := 4983230072969 + 3 ^ 40 * 8026006 * 2
def baseEnd_8026006 : Nat := 457910979318847827590453

theorem tailTrace_8026006 : CollatzResearch.WordTrace tailWord_8026006 prefixEnd_8026006 457910979318847827590453 := by
  unfold tailWord_8026006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295780485072404346269117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195154991840772313026870581 18295780485072404346269117)
  ·
    refine ⟨6860917681902151629850919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18295780485072404346269117 6860917681902151629850919)
    ·
      refine ⟨10291376522853227444776379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860917681902151629850919 10291376522853227444776379)
      ·
        refine ⟨15437064784279841167164569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291376522853227444776379 15437064784279841167164569)
        ·
          refine ⟨11577798588209880875373427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437064784279841167164569 11577798588209880875373427)
          ·
            refine ⟨17366697882314821313060141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577798588209880875373427 17366697882314821313060141)
            ·
              refine ⟨6512511705868057992397553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17366697882314821313060141 6512511705868057992397553)
              ·
                refine ⟨4884383779401043494298165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512511705868057992397553 4884383779401043494298165)
                ·
                  refine ⟨457910979318847827590453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884383779401043494298165 457910979318847827590453)
                  ·
                    rfl

theorem cell23_8026006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_8026006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026006 prefixEnd_8026006 := by exact prefixLift 8026006
  have htrace : WordTrace (prefixWord ++ tailWord_8026006) baseStart_8026006 baseEnd_8026006 := by
    simpa [prefixWord, tailWord_8026006, baseEnd_8026006] using wordTrace_append hprefix tailTrace_8026006
  have hstable : (prefixWord ++ tailWord_8026006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026006).length < 2 ^ (prefixWord ++ tailWord_8026006).sum := by decide
  have hdescent : baseEnd_8026006 < baseStart_8026006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026058 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_8026058 : Nat := 118140960795 + 8026058 * 2 ^ 59
def prefixEnd_8026058 : Nat := 4983230072969 + 3 ^ 40 * 8026058 * 2
def baseEnd_8026058 : Nat := 1373741838287888081621279

theorem tailTrace_8026058 : CollatzResearch.WordTrace tailWord_8026058 prefixEnd_8026058 1373741838287888081621279 := by
  unfold tailWord_8026058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73183596089242520605299707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195156256237980054947465885 73183596089242520605299707)
  ·
    refine ⟨109775394133863780907949561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73183596089242520605299707 109775394133863780907949561)
    ·
      refine ⟨82331545600397835680962171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109775394133863780907949561 82331545600397835680962171)
      ·
        refine ⟨123497318400596753521443257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82331545600397835680962171 123497318400596753521443257)
        ·
          refine ⟨92622988800447565141082443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123497318400596753521443257 92622988800447565141082443)
          ·
            refine ⟨138934483200671347711623665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92622988800447565141082443 138934483200671347711623665)
            ·
              refine ⟨104200862400503510783717749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138934483200671347711623665 104200862400503510783717749)
              ·
                refine ⟨9768830850047204135973539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104200862400503510783717749 9768830850047204135973539)
                ·
                  refine ⟨14653246275070806203960309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9768830850047204135973539 14653246275070806203960309)
                  ·
                    refine ⟨1373741838287888081621279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14653246275070806203960309 1373741838287888081621279)
                    ·
                      rfl

theorem cell23_8026058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_8026058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026058 prefixEnd_8026058 := by exact prefixLift 8026058
  have htrace : WordTrace (prefixWord ++ tailWord_8026058) baseStart_8026058 baseEnd_8026058 := by
    simpa [prefixWord, tailWord_8026058, baseEnd_8026058] using wordTrace_append hprefix tailTrace_8026058
  have hstable : (prefixWord ++ tailWord_8026058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026058).length < 2 ^ (prefixWord ++ tailWord_8026058).sum := by decide
  have hdescent : baseEnd_8026058 < baseStart_8026058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026066 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_8026066 : Nat := 118140960795 + 8026066 * 2 ^ 59
def prefixEnd_8026066 : Nat := 4983230072969 + 3 ^ 40 * 8026066 * 2
def baseEnd_8026066 : Nat := 1373743207569633404521267

theorem tailTrace_8026066 : CollatzResearch.WordTrace tailWord_8026066 prefixEnd_8026066 1373743207569633404521267 := by
  unfold tailWord_8026066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73183669035235274946872513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195156450760627399858326701 73183669035235274946872513)
  ·
    refine ⟨54887751776426456210154385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73183669035235274946872513 54887751776426456210154385)
    ·
      refine ⟨41165813832319842157615789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54887751776426456210154385 41165813832319842157615789)
      ·
        refine ⟨15437180187119940809105921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41165813832319842157615789 15437180187119940809105921)
        ·
          refine ⟨11577885140339955606829441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437180187119940809105921 11577885140339955606829441)
          ·
            refine ⟨8683413855254966705122081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11577885140339955606829441 8683413855254966705122081)
            ·
              refine ⟨6512560391441225028841561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8683413855254966705122081 6512560391441225028841561)
              ·
                refine ⟨4884420293580918771631171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512560391441225028841561 4884420293580918771631171)
                ·
                  refine ⟨7326630440371378157446757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884420293580918771631171 7326630440371378157446757)
                  ·
                    refine ⟨1373743207569633404521267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326630440371378157446757 1373743207569633404521267)
                    ·
                      rfl

theorem cell23_8026066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_8026066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026066 prefixEnd_8026066 := by exact prefixLift 8026066
  have htrace : WordTrace (prefixWord ++ tailWord_8026066) baseStart_8026066 baseEnd_8026066 := by
    simpa [prefixWord, tailWord_8026066, baseEnd_8026066] using wordTrace_append hprefix tailTrace_8026066
  have hstable : (prefixWord ++ tailWord_8026066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026066).length < 2 ^ (prefixWord ++ tailWord_8026066).sum := by decide
  have hdescent : baseEnd_8026066 < baseStart_8026066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026071 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 6]
def baseStart_8026071 : Nat := 118140960795 + 8026071 * 2 ^ 59
def prefixEnd_8026071 : Nat := 4983230072969 + 3 ^ 40 * 8026071 * 2
def baseEnd_8026071 : Nat := 1373744063370724231333759

theorem tailTrace_8026071 : CollatzResearch.WordTrace tailWord_8026071 prefixEnd_8026071 1373744063370724231333759 := by
  unfold tailWord_8026071
  simp only [CollatzResearch.WordTrace]
  refine ⟨292734858505922985641422067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195156572337281990427614711 292734858505922985641422067)
  ·
    refine ⟨439102287758884478462133101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292734858505922985641422067 439102287758884478462133101)
    ·
      refine ⟨164663357909581679423299913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439102287758884478462133101 164663357909581679423299913)
      ·
        refine ⟨123497518432186259567474935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164663357909581679423299913 123497518432186259567474935)
        ·
          refine ⟨185246277648279389351212403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123497518432186259567474935 185246277648279389351212403)
          ·
            refine ⟨277869416472419084026818605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185246277648279389351212403 277869416472419084026818605)
            ·
              refine ⟨104201031177157156510056977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277869416472419084026818605 104201031177157156510056977)
              ·
                refine ⟨78150773382867867382542733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104201031177157156510056977 78150773382867867382542733)
                ·
                  refine ⟨29306540018575450268453525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78150773382867867382542733 29306540018575450268453525)
                  ·
                    refine ⟨1373744063370724231333759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29306540018575450268453525 1373744063370724231333759)
                    ·
                      rfl

theorem cell23_8026071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_8026071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026071 prefixEnd_8026071 := by exact prefixLift 8026071
  have htrace : WordTrace (prefixWord ++ tailWord_8026071) baseStart_8026071 baseEnd_8026071 := by
    simpa [prefixWord, tailWord_8026071, baseEnd_8026071] using wordTrace_append hprefix tailTrace_8026071
  have hstable : (prefixWord ++ tailWord_8026071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026071).length < 2 ^ (prefixWord ++ tailWord_8026071).sum := by decide
  have hdescent : baseEnd_8026071 < baseStart_8026071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026072 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_8026072 : Nat := 118140960795 + 8026072 * 2 ^ 59
def prefixEnd_8026072 : Nat := 4983230072969 + 3 ^ 40 * 8026072 * 2
def baseEnd_8026072 : Nat := 4121232703592827190088773

theorem tailTrace_8026072 : CollatzResearch.WordTrace tailWord_8026072 prefixEnd_8026072 4121232703592827190088773 := by
  unfold tailWord_8026072
  simp only [CollatzResearch.WordTrace]
  refine ⟨146367447489459681406104235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195156596652612908541472313 146367447489459681406104235)
  ·
    refine ⟨219551171234189522109156353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146367447489459681406104235 219551171234189522109156353)
    ·
      refine ⟨164663378425642141581867265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219551171234189522109156353 164663378425642141581867265)
      ·
        refine ⟨123497533819231606186400449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164663378425642141581867265 123497533819231606186400449)
        ·
          refine ⟨92623150364423704639800337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123497533819231606186400449 92623150364423704639800337)
          ·
            refine ⟨69467362773317778479850253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92623150364423704639800337 69467362773317778479850253)
            ·
              refine ⟨26050261039994166929943845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69467362773317778479850253 26050261039994166929943845)
              ·
                refine ⟨4884423944998906299364471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26050261039994166929943845 4884423944998906299364471)
                ·
                  refine ⟨7326635917498359449046707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884423944998906299364471 7326635917498359449046707)
                  ·
                    refine ⟨10989953876247539173570061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7326635917498359449046707 10989953876247539173570061)
                    ·
                      refine ⟨4121232703592827190088773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10989953876247539173570061 4121232703592827190088773)
                      ·
                        rfl

theorem cell23_8026072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_8026072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026072 prefixEnd_8026072 := by exact prefixLift 8026072
  have htrace : WordTrace (prefixWord ++ tailWord_8026072) baseStart_8026072 baseEnd_8026072 := by
    simpa [prefixWord, tailWord_8026072, baseEnd_8026072] using wordTrace_append hprefix tailTrace_8026072
  have hstable : (prefixWord ++ tailWord_8026072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026072).length < 2 ^ (prefixWord ++ tailWord_8026072).sum := by decide
  have hdescent : baseEnd_8026072 < baseStart_8026072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026088 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_8026088 : Nat := 118140960795 + 8026088 * 2 ^ 59
def prefixEnd_8026088 : Nat := 4983230072969 + 3 ^ 40 * 8026088 * 2
def baseEnd_8026088 : Nat := 1373746973094433042496233

theorem tailTrace_8026088 : CollatzResearch.WordTrace tailWord_8026088 prefixEnd_8026088 1373746973094433042496233 := by
  unfold tailWord_8026088
  simp only [CollatzResearch.WordTrace]
  refine ⟨146367739273430698772395459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195156985697907598363193945 146367739273430698772395459)
  ·
    refine ⟨219551608910146048158593189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146367739273430698772395459 219551608910146048158593189)
    ·
      refine ⟨41165926670652384029736223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219551608910146048158593189 41165926670652384029736223)
      ·
        refine ⟨61748890005978576044604335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41165926670652384029736223 61748890005978576044604335)
        ·
          refine ⟨92623335008967864066906503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61748890005978576044604335 92623335008967864066906503)
          ·
            refine ⟨138935002513451796100359755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92623335008967864066906503 138935002513451796100359755)
            ·
              refine ⟨208402503770177694150539633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138935002513451796100359755 208402503770177694150539633)
              ·
                refine ⟨156301877827633270612904725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208402503770177694150539633 156301877827633270612904725)
                ·
                  refine ⟨7326650523170309559979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156301877827633270612904725 7326650523170309559979909)
                  ·
                    refine ⟨1373746973094433042496233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326650523170309559979909 1373746973094433042496233)
                    ·
                      rfl

theorem cell23_8026088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_8026088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026088 prefixEnd_8026088 := by exact prefixLift 8026088
  have htrace : WordTrace (prefixWord ++ tailWord_8026088) baseStart_8026088 baseEnd_8026088 := by
    simpa [prefixWord, tailWord_8026088, baseEnd_8026088] using wordTrace_append hprefix tailTrace_8026088
  have hstable : (prefixWord ++ tailWord_8026088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026088).length < 2 ^ (prefixWord ++ tailWord_8026088).sum := by decide
  have hdescent : baseEnd_8026088 < baseStart_8026088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_8026091 : Nat := 118140960795 + 8026091 * 2 ^ 59
def prefixEnd_8026091 : Nat := 4983230072969 + 3 ^ 40 * 8026091 * 2
def baseEnd_8026091 : Nat := 4121242459725262615751185

theorem tailTrace_8026091 : CollatzResearch.WordTrace tailWord_8026091 prefixEnd_8026091 4121242459725262615751185 := by
  unfold tailWord_8026091
  simp only [CollatzResearch.WordTrace]
  refine ⟨292735587965850529057150127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195157058643900352704766751 292735587965850529057150127)
  ·
    refine ⟨439103381948775793585725191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292735587965850529057150127 439103381948775793585725191)
    ·
      refine ⟨658655072923163690378587787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439103381948775793585725191 658655072923163690378587787)
      ·
        refine ⟨987982609384745535567881681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658655072923163690378587787 987982609384745535567881681)
        ·
          refine ⟨740986957038559151675911261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987982609384745535567881681 740986957038559151675911261)
          ·
            refine ⟨277870108889459681878466723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740986957038559151675911261 277870108889459681878466723)
            ·
              refine ⟨416805163334189522817700085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277870108889459681878466723 416805163334189522817700085)
              ·
                refine ⟨39075484062580267764159383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416805163334189522817700085 39075484062580267764159383)
                ·
                  refine ⟨58613226093870401646239075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39075484062580267764159383 58613226093870401646239075)
                  ·
                    refine ⟨87919839140805602469358613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58613226093870401646239075 87919839140805602469358613)
                    ·
                      refine ⟨4121242459725262615751185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87919839140805602469358613 4121242459725262615751185)
                      ·
                        rfl

theorem cell23_8026091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_8026091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026091 prefixEnd_8026091 := by exact prefixLift 8026091
  have htrace : WordTrace (prefixWord ++ tailWord_8026091) baseStart_8026091 baseEnd_8026091 := by
    simpa [prefixWord, tailWord_8026091, baseEnd_8026091] using wordTrace_append hprefix tailTrace_8026091
  have hstable : (prefixWord ++ tailWord_8026091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026091).length < 2 ^ (prefixWord ++ tailWord_8026091).sum := by decide
  have hdescent : baseEnd_8026091 < baseStart_8026091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026108 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_8026108 : Nat := 118140960795 + 8026108 * 2 ^ 59
def prefixEnd_8026108 : Nat := 4983230072969 + 3 ^ 40 * 8026108 * 2
def baseEnd_8026108 : Nat := 4121251188896389049238607

theorem tailTrace_8026108 : CollatzResearch.WordTrace tailWord_8026108 prefixEnd_8026108 4121251188896389049238607 := by
  unfold tailWord_8026108
  simp only [CollatzResearch.WordTrace]
  refine ⟨146368104003394470480259489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195157472004525960640345985 146368104003394470480259489)
  ·
    refine ⟨109776078002545852860194617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146368104003394470480259489 109776078002545852860194617)
    ·
      refine ⟨82332058501909389645145963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109776078002545852860194617 82332058501909389645145963)
      ·
        refine ⟨123498087752864084467718945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82332058501909389645145963 123498087752864084467718945)
        ·
          refine ⟨92623565814648063350789209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123498087752864084467718945 92623565814648063350789209)
          ·
            refine ⟨69467674360986047513091907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92623565814648063350789209 69467674360986047513091907)
            ·
              refine ⟨104201511541479071269637861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69467674360986047513091907 104201511541479071269637861)
              ·
                refine ⟨19537783414027325863057099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104201511541479071269637861 19537783414027325863057099)
                ·
                  refine ⟨29306675121040988794585649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19537783414027325863057099 29306675121040988794585649)
                  ·
                    refine ⟨21980006340780741595939237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29306675121040988794585649 21980006340780741595939237)
                    ·
                      refine ⟨4121251188896389049238607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21980006340780741595939237 4121251188896389049238607)
                      ·
                        rfl

theorem cell23_8026108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_8026108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026108 prefixEnd_8026108 := by exact prefixLift 8026108
  have htrace : WordTrace (prefixWord ++ tailWord_8026108) baseStart_8026108 baseEnd_8026108 := by
    simpa [prefixWord, tailWord_8026108, baseEnd_8026108] using wordTrace_append hprefix tailTrace_8026108
  have hstable : (prefixWord ++ tailWord_8026108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026108).length < 2 ^ (prefixWord ++ tailWord_8026108).sum := by decide
  have hdescent : baseEnd_8026108 < baseStart_8026108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026121 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_8026121 : Nat := 118140960795 + 8026121 * 2 ^ 59
def prefixEnd_8026121 : Nat := 4983230072969 + 3 ^ 40 * 8026121 * 2
def baseEnd_8026121 : Nat := 4121257864144897498376047

theorem tailTrace_8026121 : CollatzResearch.WordTrace tailWord_8026121 prefixEnd_8026121 4121257864144897498376047 := by
  unfold tailWord_8026121
  simp only [CollatzResearch.WordTrace]
  refine ⟨292736682155741844180742217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195157788103827896120494811 292736682155741844180742217)
  ·
    refine ⟨219552511616806383135556663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292736682155741844180742217 219552511616806383135556663)
    ·
      refine ⟨329328767425209574703334995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219552511616806383135556663 329328767425209574703334995)
      ·
        refine ⟨493993151137814362055002493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329328767425209574703334995 493993151137814362055002493)
        ·
          refine ⟨185247431676680385770625935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493993151137814362055002493 185247431676680385770625935)
          ·
            refine ⟨277871147515020578655938903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185247431676680385770625935 277871147515020578655938903)
            ·
              refine ⟨416806721272530867983908355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277871147515020578655938903 416806721272530867983908355)
              ·
                refine ⟨625210081908796301975862533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416806721272530867983908355 625210081908796301975862533)
                ·
                  refine ⟨117226890357899306620474225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625210081908796301975862533 117226890357899306620474225)
                  ·
                    refine ⟨87920167768424479965355669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117226890357899306620474225 87920167768424479965355669)
                    ·
                      refine ⟨4121257864144897498376047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87920167768424479965355669 4121257864144897498376047)
                      ·
                        rfl

theorem cell23_8026121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_8026121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026121 prefixEnd_8026121 := by exact prefixLift 8026121
  have htrace : WordTrace (prefixWord ++ tailWord_8026121) baseStart_8026121 baseEnd_8026121 := by
    simpa [prefixWord, tailWord_8026121, baseEnd_8026121] using wordTrace_append hprefix tailTrace_8026121
  have hstable : (prefixWord ++ tailWord_8026121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026121).length < 2 ^ (prefixWord ++ tailWord_8026121).sum := by decide
  have hdescent : baseEnd_8026121 < baseStart_8026121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026131 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 9]
def baseStart_8026131 : Nat := 118140960795 + 8026131 * 2 ^ 59
def prefixEnd_8026131 : Nat := 4983230072969 + 3 ^ 40 * 8026131 * 2
def baseEnd_8026131 : Nat := 1373754332983814153083667

theorem tailTrace_8026131 : CollatzResearch.WordTrace tailWord_8026131 prefixEnd_8026131 1373754332983814153083667 := by
  unfold tailWord_8026131
  simp only [CollatzResearch.WordTrace]
  refine ⟨292737046885705615888606247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195158031257137077259070831 292737046885705615888606247)
  ·
    refine ⟨439105570328558423832909371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292737046885705615888606247 439105570328558423832909371)
    ·
      refine ⟨658658355492837635749364057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439105570328558423832909371 658658355492837635749364057)
      ·
        refine ⟨493993766619628226812023043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658658355492837635749364057 493993766619628226812023043)
        ·
          refine ⟨740990649929442340218034565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493993766619628226812023043 740990649929442340218034565)
          ·
            refine ⟨138935746861770438790881481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740990649929442340218034565 138935746861770438790881481)
            ·
              refine ⟨104201810146327829093161111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138935746861770438790881481 104201810146327829093161111)
              ·
                refine ⟨156302715219491743639741667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104201810146327829093161111 156302715219491743639741667)
                ·
                  refine ⟨234454072829237615459612501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156302715219491743639741667 234454072829237615459612501)
                  ·
                    refine ⟨1373754332983814153083667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234454072829237615459612501 1373754332983814153083667)
                    ·
                      rfl

theorem cell23_8026131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_8026131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026131 prefixEnd_8026131 := by exact prefixLift 8026131
  have htrace : WordTrace (prefixWord ++ tailWord_8026131) baseStart_8026131 baseEnd_8026131 := by
    simpa [prefixWord, tailWord_8026131, baseEnd_8026131] using wordTrace_append hprefix tailTrace_8026131
  have hstable : (prefixWord ++ tailWord_8026131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026131).length < 2 ^ (prefixWord ++ tailWord_8026131).sum := by decide
  have hdescent : baseEnd_8026131 < baseStart_8026131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026172 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_8026172 : Nat := 118140960795 + 8026172 * 2 ^ 59
def prefixEnd_8026172 : Nat := 4983230072969 + 3 ^ 40 * 8026172 * 2
def baseEnd_8026172 : Nat := 4121284051658276798838313

theorem tailTrace_8026172 : CollatzResearch.WordTrace tailWord_8026172 prefixEnd_8026172 4121284051658276798838313 := by
  unfold tailWord_8026172
  simp only [CollatzResearch.WordTrace]
  refine ⟨146369271139278539945424385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195159028185704719927232513 146369271139278539945424385)
  ·
    refine ⟨109776953354458904959068289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146369271139278539945424385 109776953354458904959068289)
    ·
      refine ⟨82332715015844178719301217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109776953354458904959068289 82332715015844178719301217)
      ·
        refine ⟨61749536261883134039475913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82332715015844178719301217 61749536261883134039475913)
        ·
          refine ⟨46312152196412350529606935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61749536261883134039475913 46312152196412350529606935)
          ·
            refine ⟨69468228294618525794410403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46312152196412350529606935 69468228294618525794410403)
            ·
              refine ⟨104202342441927788691615605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69468228294618525794410403 104202342441927788691615605)
              ·
                refine ⟨9768969603930730189838963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104202342441927788691615605 9768969603930730189838963)
                ·
                  refine ⟨14653454405896095284758445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9768969603930730189838963 14653454405896095284758445)
                  ·
                    refine ⟨5495045402211035731784417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14653454405896095284758445 5495045402211035731784417)
                    ·
                      refine ⟨4121284051658276798838313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495045402211035731784417 4121284051658276798838313)
                      ·
                        rfl

theorem cell23_8026172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_8026172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026172 prefixEnd_8026172 := by exact prefixLift 8026172
  have htrace : WordTrace (prefixWord ++ tailWord_8026172) baseStart_8026172 baseEnd_8026172 := by
    simpa [prefixWord, tailWord_8026172, baseEnd_8026172] using wordTrace_append hprefix tailTrace_8026172
  have hstable : (prefixWord ++ tailWord_8026172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026172).length < 2 ^ (prefixWord ++ tailWord_8026172).sum := by decide
  have hdescent : baseEnd_8026172 < baseStart_8026172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026225 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 5]
def baseStart_8026225 : Nat := 118140960795 + 8026225 * 2 ^ 59
def prefixEnd_8026225 : Nat := 4983230072969 + 3 ^ 40 * 8026225 * 2
def baseEnd_8026225 : Nat := 457923474014773899052841

theorem tailTrace_8026225 : CollatzResearch.WordTrace tailWord_8026225 prefixEnd_8026225 457923474014773899052841 := by
  unfold tailWord_8026225
  simp only [CollatzResearch.WordTrace]
  refine ⟨292740475347365069942528129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195160316898243379961685419 292740475347365069942528129)
  ·
    refine ⟨219555356510523802456896097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292740475347365069942528129 219555356510523802456896097)
    ·
      refine ⟨164666517382892851842672073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219555356510523802456896097 164666517382892851842672073)
      ·
        refine ⟨123499888037169638882004055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164666517382892851842672073 123499888037169638882004055)
        ·
          refine ⟨185249832055754458323006083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123499888037169638882004055 185249832055754458323006083)
          ·
            refine ⟨277874748083631687484509125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185249832055754458323006083 277874748083631687484509125)
            ·
              refine ⟨52101515265680941403345461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277874748083631687484509125 52101515265680941403345461)
              ·
                refine ⟨4884517056157588256563637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52101515265680941403345461 4884517056157588256563637)
                ·
                  refine ⟨457923474014773899052841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884517056157588256563637 457923474014773899052841)
                  ·
                    rfl

theorem cell23_8026225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 5].length) (baseStart_8026225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026225 prefixEnd_8026225 := by exact prefixLift 8026225
  have htrace : WordTrace (prefixWord ++ tailWord_8026225) baseStart_8026225 baseEnd_8026225 := by
    simpa [prefixWord, tailWord_8026225, baseEnd_8026225] using wordTrace_append hprefix tailTrace_8026225
  have hstable : (prefixWord ++ tailWord_8026225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026225).length < 2 ^ (prefixWord ++ tailWord_8026225).sum := by decide
  have hdescent : baseEnd_8026225 < baseStart_8026225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026272 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_8026272 : Nat := 118140960795 + 8026272 * 2 ^ 59
def prefixEnd_8026272 : Nat := 4983230072969 + 3 ^ 40 * 8026272 * 2
def baseEnd_8026272 : Nat := 1373778466574575469195951

theorem tailTrace_8026272 : CollatzResearch.WordTrace tailWord_8026272 prefixEnd_8026272 1373778466574575469195951 := by
  unfold tailWord_8026272
  simp only [CollatzResearch.WordTrace]
  refine ⟨146371094789097398484744535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195161459718796531312992713 146371094789097398484744535)
  ·
    refine ⟨219556642183646097727116803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146371094789097398484744535 219556642183646097727116803)
    ·
      refine ⟨329334963275469146590675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219556642183646097727116803 329334963275469146590675205)
      ·
        refine ⟨61750305614150464985751601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329334963275469146590675205 61750305614150464985751601)
        ·
          refine ⟨46312729210612848739313701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61750305614150464985751601 46312729210612848739313701)
          ·
            refine ⟨8683636726989909138621319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46312729210612848739313701 8683636726989909138621319)
            ·
              refine ⟨13025455090484863707931979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683636726989909138621319 13025455090484863707931979)
              ·
                refine ⟨19538182635727295561897969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025455090484863707931979 19538182635727295561897969)
                ·
                  refine ⟨14653636976795471671423477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19538182635727295561897969 14653636976795471671423477)
                  ·
                    refine ⟨1373778466574575469195951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14653636976795471671423477 1373778466574575469195951)
                    ·
                      rfl

theorem cell23_8026272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_8026272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026272 prefixEnd_8026272 := by exact prefixLift 8026272
  have htrace : WordTrace (prefixWord ++ tailWord_8026272) baseStart_8026272 baseEnd_8026272 := by
    simpa [prefixWord, tailWord_8026272, baseEnd_8026272] using wordTrace_append hprefix tailTrace_8026272
  have hstable : (prefixWord ++ tailWord_8026272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026272).length < 2 ^ (prefixWord ++ tailWord_8026272).sum := by decide
  have hdescent : baseEnd_8026272 < baseStart_8026272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026382 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_8026382 : Nat := 118140960795 + 8026382 * 2 ^ 59
def prefixEnd_8026382 : Nat := 4983230072969 + 3 ^ 40 * 8026382 * 2
def baseEnd_8026382 : Nat := 4121391882595720977212347

theorem tailTrace_8026382 : CollatzResearch.WordTrace tailWord_8026382 prefixEnd_8026382 4121391882595720977212347 := by
  unfold tailWord_8026382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36593275200974535719499175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195164134405197523837328933 36593275200974535719499175)
  ·
    refine ⟨54889912801461803579248763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36593275200974535719499175 54889912801461803579248763)
    ·
      refine ⟨82334869202192705368873145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54889912801461803579248763 82334869202192705368873145)
      ·
        refine ⟨61751151901644529026654859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82334869202192705368873145 61751151901644529026654859)
        ·
          refine ⟨92626727852466793539982289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61751151901644529026654859 92626727852466793539982289)
          ·
            refine ⟨69470045889350095154986717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92626727852466793539982289 69470045889350095154986717)
            ·
              refine ⟨26051267208506285683120019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69470045889350095154986717 26051267208506285683120019)
              ·
                refine ⟨39076900812759428524680029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26051267208506285683120019 39076900812759428524680029)
                ·
                  refine ⟨14653837804784785696755011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39076900812759428524680029 14653837804784785696755011)
                  ·
                    refine ⟨21980756707177178545132517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14653837804784785696755011 21980756707177178545132517)
                    ·
                      refine ⟨4121391882595720977212347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21980756707177178545132517 4121391882595720977212347)
                      ·
                        rfl

theorem cell23_8026382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_8026382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026382 prefixEnd_8026382 := by exact prefixLift 8026382
  have htrace : WordTrace (prefixWord ++ tailWord_8026382) baseStart_8026382 baseEnd_8026382 := by
    simpa [prefixWord, tailWord_8026382, baseEnd_8026382] using wordTrace_append hprefix tailTrace_8026382
  have hstable : (prefixWord ++ tailWord_8026382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026382).length < 2 ^ (prefixWord ++ tailWord_8026382).sum := by decide
  have hdescent : baseEnd_8026382 < baseStart_8026382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026395 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_8026395 : Nat := 118140960795 + 8026395 * 2 ^ 59
def prefixEnd_8026395 : Nat := 4983230072969 + 3 ^ 40 * 8026395 * 2
def baseEnd_8026395 : Nat := 4121398557844229426349787

theorem tailTrace_8026395 : CollatzResearch.WordTrace tailWord_8026395 prefixEnd_8026395 4121398557844229426349787 := by
  unfold tailWord_8026395
  simp only [CollatzResearch.WordTrace]
  refine ⟨292746675756749188976216639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195164450504499459317477759 292746675756749188976216639)
  ·
    refine ⟨439120013635123783464324959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292746675756749188976216639 439120013635123783464324959)
    ·
      refine ⟨658680020452685675196487439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439120013635123783464324959 658680020452685675196487439)
      ·
        refine ⟨988020030679028512794731159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658680020452685675196487439 988020030679028512794731159)
        ·
          refine ⟨1482030046018542769192096739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988020030679028512794731159 1482030046018542769192096739)
          ·
            refine ⟨2223045069027814153788145109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482030046018542769192096739 2223045069027814153788145109)
            ·
              refine ⟨52102618805339394229409651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2223045069027814153788145109 52102618805339394229409651)
              ·
                refine ⟨78153928208009091344114477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52102618805339394229409651 78153928208009091344114477)
                ·
                  refine ⟨29307723078003409254042929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78153928208009091344114477 29307723078003409254042929)
                  ·
                    refine ⟨21980792308502556940532197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29307723078003409254042929 21980792308502556940532197)
                    ·
                      refine ⟨4121398557844229426349787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21980792308502556940532197 4121398557844229426349787)
                      ·
                        rfl

theorem cell23_8026395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_8026395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026395 prefixEnd_8026395 := by exact prefixLift 8026395
  have htrace : WordTrace (prefixWord ++ tailWord_8026395) baseStart_8026395 baseEnd_8026395 := by
    simpa [prefixWord, tailWord_8026395, baseEnd_8026395] using wordTrace_append hprefix tailTrace_8026395
  have hstable : (prefixWord ++ tailWord_8026395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026395).length < 2 ^ (prefixWord ++ tailWord_8026395).sum := by decide
  have hdescent : baseEnd_8026395 < baseStart_8026395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026405 : List Nat := [1, 3, 1, 2, 5, 11]
def baseStart_8026405 : Nat := 118140960795 + 8026405 * 2 ^ 59
def prefixEnd_8026405 : Nat := 4983230072969 + 3 ^ 40 * 8026405 * 2
def baseEnd_8026405 : Nat := 16960509023254215585287

theorem tailTrace_8026405 : CollatzResearch.WordTrace tailWord_8026405 prefixEnd_8026405 16960509023254215585287 := by
  unfold tailWord_8026405
  simp only [CollatzResearch.WordTrace]
  refine ⟨292747040486712960684080669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195164693657808640456053779 292747040486712960684080669)
  ·
    refine ⟨109780140182517360256530251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292747040486712960684080669 109780140182517360256530251)
    ·
      refine ⟨164670210273776040384795377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109780140182517360256530251 164670210273776040384795377)
      ·
        refine ⟨123502657705332030288596533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164670210273776040384795377 123502657705332030288596533)
        ·
          refine ⟨11578374159874877839555925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123502657705332030288596533 11578374159874877839555925)
          ·
            refine ⟨16960509023254215585287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11578374159874877839555925 16960509023254215585287)
            ·
              rfl

theorem cell23_8026405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 11].length) (baseStart_8026405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026405 prefixEnd_8026405 := by exact prefixLift 8026405
  have htrace : WordTrace (prefixWord ++ tailWord_8026405) baseStart_8026405 baseEnd_8026405 := by
    simpa [prefixWord, tailWord_8026405, baseEnd_8026405] using wordTrace_append hprefix tailTrace_8026405
  have hstable : (prefixWord ++ tailWord_8026405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026405).length < 2 ^ (prefixWord ++ tailWord_8026405).sum := by decide
  have hdescent : baseEnd_8026405 < baseStart_8026405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026433 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8026433 : Nat := 118140960795 + 8026433 * 2 ^ 59
def prefixEnd_8026433 : Nat := 4983230072969 + 3 ^ 40 * 8026433 * 2
def baseEnd_8026433 : Nat := 4121418070109100277674613

theorem tailTrace_8026433 : CollatzResearch.WordTrace tailWord_8026433 prefixEnd_8026433 4121418070109100277674613 := by
  unfold tailWord_8026433
  simp only [CollatzResearch.WordTrace]
  refine ⟨292748061730611521466099953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195165374487074347644066635 292748061730611521466099953)
  ·
    refine ⟨219561046297958641099574965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292748061730611521466099953 219561046297958641099574965)
    ·
      refine ⟨20583848090433622603085153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219561046297958641099574965 20583848090433622603085153)
      ·
        refine ⟨15437886067825216952313865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20583848090433622603085153 15437886067825216952313865)
        ·
          refine ⟨11578414550868912714235399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437886067825216952313865 11578414550868912714235399)
          ·
            refine ⟨17367621826303369071353099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578414550868912714235399 17367621826303369071353099)
            ·
              refine ⟨26051432739455053607029649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17367621826303369071353099 26051432739455053607029649)
              ·
                refine ⟨19538574554591290205272237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26051432739455053607029649 19538574554591290205272237)
                ·
                  refine ⟨7326965457971733826977089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19538574554591290205272237 7326965457971733826977089)
                  ·
                    refine ⟨5495224093478800370232817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326965457971733826977089 5495224093478800370232817)
                    ·
                      refine ⟨4121418070109100277674613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495224093478800370232817 4121418070109100277674613)
                      ·
                        rfl

theorem cell23_8026433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8026433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026433 prefixEnd_8026433 := by exact prefixLift 8026433
  have htrace : WordTrace (prefixWord ++ tailWord_8026433) baseStart_8026433 baseEnd_8026433 := by
    simpa [prefixWord, tailWord_8026433, baseEnd_8026433] using wordTrace_append hprefix tailTrace_8026433
  have hstable : (prefixWord ++ tailWord_8026433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026433).length < 2 ^ (prefixWord ++ tailWord_8026433).sum := by decide
  have hdescent : baseEnd_8026433 < baseStart_8026433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026453 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_8026453 : Nat := 118140960795 + 8026453 * 2 ^ 59
def prefixEnd_8026453 : Nat := 4983230072969 + 3 ^ 40 * 8026453 * 2
def baseEnd_8026453 : Nat := 4121428339722190199424521

theorem tailTrace_8026453 : CollatzResearch.WordTrace tailWord_8026453 prefixEnd_8026453 4121428339722190199424521 := by
  unfold tailWord_8026453
  simp only [CollatzResearch.WordTrace]
  refine ⟨292748791190539064881828013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195165860793692709921218675 292748791190539064881828013)
  ·
    refine ⟨109780796696452149330685505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292748791190539064881828013 109780796696452149330685505)
    ·
      refine ⟨82335597522339111998014129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109780796696452149330685505 82335597522339111998014129)
      ·
        refine ⟨61751698141754333998510597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82335597522339111998014129 61751698141754333998510597)
        ·
          refine ⟨11578443401578937624720737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61751698141754333998510597 11578443401578937624720737)
          ·
            refine ⟨8683832551184203218540553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11578443401578937624720737 8683832551184203218540553)
            ·
              refine ⟨6512874413388152413905415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8683832551184203218540553 6512874413388152413905415)
              ·
                refine ⟨9769311620082228620858123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512874413388152413905415 9769311620082228620858123)
                ·
                  refine ⟨14653967430123342931287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769311620082228620858123 14653967430123342931287185)
                  ·
                    refine ⟨10990475572592507198465389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14653967430123342931287185 10990475572592507198465389)
                    ·
                      refine ⟨4121428339722190199424521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990475572592507198465389 4121428339722190199424521)
                      ·
                        rfl

theorem cell23_8026453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_8026453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026453 prefixEnd_8026453 := by exact prefixLift 8026453
  have htrace : WordTrace (prefixWord ++ tailWord_8026453) baseStart_8026453 baseEnd_8026453 := by
    simpa [prefixWord, tailWord_8026453, baseEnd_8026453] using wordTrace_append hprefix tailTrace_8026453
  have hstable : (prefixWord ++ tailWord_8026453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026453).length < 2 ^ (prefixWord ++ tailWord_8026453).sum := by decide
  have hdescent : baseEnd_8026453 < baseStart_8026453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026460 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_8026460 : Nat := 118140960795 + 8026460 * 2 ^ 59
def prefixEnd_8026460 : Nat := 4983230072969 + 3 ^ 40 * 8026460 * 2
def baseEnd_8026460 : Nat := 1373810644695590557345663

theorem tailTrace_8026460 : CollatzResearch.WordTrace tailWord_8026460 prefixEnd_8026460 1373810644695590557345663 := by
  unfold tailWord_8026460
  simp only [CollatzResearch.WordTrace]
  refine ⟨146374523250756852538666417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195166031001009136718221889 146374523250756852538666417)
  ·
    refine ⟨109780892438067639403999813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146374523250756852538666417 109780892438067639403999813)
    ·
      refine ⟨20583917332137682388249965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109780892438067639403999813 20583917332137682388249965)
      ·
        refine ⟨7718968999551630895593737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20583917332137682388249965 7718968999551630895593737)
        ·
          refine ⟨5789226749663723171695303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7718968999551630895593737 5789226749663723171695303)
          ·
            refine ⟨8683840124495584757542955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789226749663723171695303 8683840124495584757542955)
            ·
              refine ⟨13025760186743377136314433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683840124495584757542955 13025760186743377136314433)
              ·
                refine ⟨9769320140057532852235825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13025760186743377136314433 9769320140057532852235825)
                ·
                  refine ⟨7326990105043149639176869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9769320140057532852235825 7326990105043149639176869)
                  ·
                    refine ⟨1373810644695590557345663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326990105043149639176869 1373810644695590557345663)
                    ·
                      rfl

theorem cell23_8026460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_8026460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026460 prefixEnd_8026460 := by exact prefixLift 8026460
  have htrace : WordTrace (prefixWord ++ tailWord_8026460) baseStart_8026460 baseEnd_8026460 := by
    simpa [prefixWord, tailWord_8026460, baseEnd_8026460] using wordTrace_append hprefix tailTrace_8026460
  have hstable : (prefixWord ++ tailWord_8026460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026460).length < 2 ^ (prefixWord ++ tailWord_8026460).sum := by decide
  have hdescent : baseEnd_8026460 < baseStart_8026460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026466 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_8026466 : Nat := 118140960795 + 8026466 * 2 ^ 59
def prefixEnd_8026466 : Nat := 4983230072969 + 3 ^ 40 * 8026466 * 2
def baseEnd_8026466 : Nat := 4121435014970698648561961

theorem tailTrace_8026466 : CollatzResearch.WordTrace tailWord_8026466 prefixEnd_8026466 4121435014970698648561961 := by
  unfold tailWord_8026466
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187316334872992025512813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195166176892994645401367501 73187316334872992025512813)
  ·
    refine ⟨27445243625577372009567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73187316334872992025512813 27445243625577372009567305)
    ·
      refine ⟨20583932719183029007175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27445243625577372009567305 20583932719183029007175479)
      ·
        refine ⟨30875899078774543510763219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20583932719183029007175479 30875899078774543510763219)
        ·
          refine ⟨46313848618161815266144829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30875899078774543510763219 46313848618161815266144829)
          ·
            refine ⟨17367693231810680724804311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46313848618161815266144829 17367693231810680724804311)
            ·
              refine ⟨26051539847716021087206467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17367693231810680724804311 26051539847716021087206467)
              ·
                refine ⟨39077309771574031630809701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26051539847716021087206467 39077309771574031630809701)
                ·
                  refine ⟨7326995582170130930776819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39077309771574031630809701 7326995582170130930776819)
                  ·
                    refine ⟨10990493373255196396165229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7326995582170130930776819 10990493373255196396165229)
                    ·
                      refine ⟨4121435014970698648561961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990493373255196396165229 4121435014970698648561961)
                      ·
                        rfl

theorem cell23_8026466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_8026466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026466 prefixEnd_8026466 := by exact prefixLift 8026466
  have htrace : WordTrace (prefixWord ++ tailWord_8026466) baseStart_8026466 baseEnd_8026466 := by
    simpa [prefixWord, tailWord_8026466, baseEnd_8026466] using wordTrace_append hprefix tailTrace_8026466
  have hstable : (prefixWord ++ tailWord_8026466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026466).length < 2 ^ (prefixWord ++ tailWord_8026466).sum := by decide
  have hdescent : baseEnd_8026466 < baseStart_8026466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_8026475 : Nat := 118140960795 + 8026475 * 2 ^ 59
def prefixEnd_8026475 : Nat := 4983230072969 + 3 ^ 40 * 8026475 * 2
def baseEnd_8026475 : Nat := 4121439636296589113349419

theorem tailTrace_8026475 : CollatzResearch.WordTrace tailWord_8026475 prefixEnd_8026475 4121439636296589113349419 := by
  unfold tailWord_8026475
  simp only [CollatzResearch.WordTrace]
  refine ⟨292749593596459362639128879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195166395730972908426085919 292749593596459362639128879)
  ·
    refine ⟨439124390394689043958693319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292749593596459362639128879 439124390394689043958693319)
    ·
      refine ⟨658686585592033565938039979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439124390394689043958693319 658686585592033565938039979)
      ·
        refine ⟨988029878388050348907059969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658686585592033565938039979 988029878388050348907059969)
        ·
          refine ⟨741022408791037761680294977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988029878388050348907059969 741022408791037761680294977)
          ·
            refine ⟨555766806593278321260221233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741022408791037761680294977 555766806593278321260221233)
            ·
              refine ⟨416825104944958740945165925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555766806593278321260221233 416825104944958740945165925)
              ·
                refine ⟨78154707177179763927218611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416825104944958740945165925 78154707177179763927218611)
                ·
                  refine ⟨117232060765769645890827917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78154707177179763927218611 117232060765769645890827917)
                  ·
                    refine ⟨43962022787163617209060469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117232060765769645890827917 43962022787163617209060469)
                    ·
                      refine ⟨4121439636296589113349419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43962022787163617209060469 4121439636296589113349419)
                      ·
                        rfl

theorem cell23_8026475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_8026475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026475 prefixEnd_8026475 := by exact prefixLift 8026475
  have htrace : WordTrace (prefixWord ++ tailWord_8026475) baseStart_8026475 baseEnd_8026475 := by
    simpa [prefixWord, tailWord_8026475, baseEnd_8026475] using wordTrace_append hprefix tailTrace_8026475
  have hstable : (prefixWord ++ tailWord_8026475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026475).length < 2 ^ (prefixWord ++ tailWord_8026475).sum := by decide
  have hdescent : baseEnd_8026475 < baseStart_8026475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026482 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_8026482 : Nat := 118140960795 + 8026482 * 2 ^ 59
def prefixEnd_8026482 : Nat := 4983230072969 + 3 ^ 40 * 8026482 * 2
def baseEnd_8026482 : Nat := 1373814410220390195320629

theorem tailTrace_8026482 : CollatzResearch.WordTrace tailWord_8026482 prefixEnd_8026482 1373814410220390195320629 := by
  unfold tailWord_8026482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187462226858500708658425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195166565938289335223089133 73187462226858500708658425)
  ·
    refine ⟨54890596670143875531493819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73187462226858500708658425 54890596670143875531493819)
    ·
      refine ⟨82335895005215813297240729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54890596670143875531493819 82335895005215813297240729)
      ·
        refine ⟨61751921253911859972930547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82335895005215813297240729 61751921253911859972930547)
        ·
          refine ⟨92627881880867789959395821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61751921253911859972930547 92627881880867789959395821)
          ·
            refine ⟨34735455705325421234773433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92627881880867789959395821 34735455705325421234773433)
            ·
              refine ⟨26051591778994065926080075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34735455705325421234773433 26051591778994065926080075)
              ·
                refine ⟨39077387668491098889120113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26051591778994065926080075 39077387668491098889120113)
                ·
                  refine ⟨29308040751368324166840085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39077387668491098889120113 29308040751368324166840085)
                  ·
                    refine ⟨1373814410220390195320629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29308040751368324166840085 1373814410220390195320629)
                    ·
                      rfl

theorem cell23_8026482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_8026482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026482 prefixEnd_8026482 := by exact prefixLift 8026482
  have htrace : WordTrace (prefixWord ++ tailWord_8026482) baseStart_8026482 baseEnd_8026482 := by
    simpa [prefixWord, tailWord_8026482, baseEnd_8026482] using wordTrace_append hprefix tailTrace_8026482
  have hstable : (prefixWord ++ tailWord_8026482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026482).length < 2 ^ (prefixWord ++ tailWord_8026482).sum := by decide
  have hdescent : baseEnd_8026482 < baseStart_8026482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026515 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_8026515 : Nat := 118140960795 + 8026515 * 2 ^ 59
def prefixEnd_8026515 : Nat := 4983230072969 + 3 ^ 40 * 8026515 * 2
def baseEnd_8026515 : Nat := 4121460175522768956849235

theorem tailTrace_8026515 : CollatzResearch.WordTrace tailWord_8026515 prefixEnd_8026515 4121460175522768956849235 := by
  unfold tailWord_8026515
  simp only [CollatzResearch.WordTrace]
  refine ⟨292751052516314449470584999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195167368344209632980389999 292751052516314449470584999)
  ·
    refine ⟨439126578774471674205877499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292751052516314449470584999 439126578774471674205877499)
    ·
      refine ⟨658689868161707511308816249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439126578774471674205877499 658689868161707511308816249)
      ·
        refine ⟨494017401121280633481612187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658689868161707511308816249 494017401121280633481612187)
        ·
          refine ⟨741026101681920950222418281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494017401121280633481612187 741026101681920950222418281)
          ·
            refine ⟨555769576261440712666813711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741026101681920950222418281 555769576261440712666813711)
            ·
              refine ⟨833654364392161069000220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555769576261440712666813711 833654364392161069000220567)
              ·
                refine ⟨1250481546588241603500330851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833654364392161069000220567 1250481546588241603500330851)
                ·
                  refine ⟨1875722319882362405250496277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250481546588241603500330851 1875722319882362405250496277)
                  ·
                    refine ⟨87924483744485737746117013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1875722319882362405250496277 87924483744485737746117013)
                    ·
                      refine ⟨4121460175522768956849235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87924483744485737746117013 4121460175522768956849235)
                      ·
                        rfl

theorem cell23_8026515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_8026515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026515 prefixEnd_8026515 := by exact prefixLift 8026515
  have htrace : WordTrace (prefixWord ++ tailWord_8026515) baseStart_8026515 baseEnd_8026515 := by
    simpa [prefixWord, tailWord_8026515, baseEnd_8026515] using wordTrace_append hprefix tailTrace_8026515
  have hstable : (prefixWord ++ tailWord_8026515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026515).length < 2 ^ (prefixWord ++ tailWord_8026515).sum := by decide
  have hdescent : baseEnd_8026515 < baseStart_8026515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026599 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_8026599 : Nat := 118140960795 + 8026599 * 2 ^ 59
def prefixEnd_8026599 : Nat := 4983230072969 + 3 ^ 40 * 8026599 * 2
def baseEnd_8026599 : Nat := 4121503307897746628198849

theorem tailTrace_8026599 : CollatzResearch.WordTrace tailWord_8026599 prefixEnd_8026599 4121503307897746628198849 := by
  unfold tailWord_8026599
  simp only [CollatzResearch.WordTrace]
  refine ⟨292754116248010131816642851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195169410832006754544428567 292754116248010131816642851)
  ·
    refine ⟨439131174372015197724964277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292754116248010131816642851 439131174372015197724964277)
    ·
      refine ⟨41168547597376424786715401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439131174372015197724964277 41168547597376424786715401)
      ·
        refine ⟨30876410698032318590036551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41168547597376424786715401 30876410698032318590036551)
        ·
          refine ⟨46314616047048477885054827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30876410698032318590036551 46314616047048477885054827)
          ·
            refine ⟨69471924070572716827582241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46314616047048477885054827 69471924070572716827582241)
            ·
              refine ⟨52103943052929537620686681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69471924070572716827582241 52103943052929537620686681)
              ·
                refine ⟨39077957289697153215515011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52103943052929537620686681 39077957289697153215515011)
                ·
                  refine ⟨58616935934545729823272517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39077957289697153215515011 58616935934545729823272517)
                  ·
                    refine ⟨10990675487727324341863597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58616935934545729823272517 10990675487727324341863597)
                    ·
                      refine ⟨4121503307897746628198849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990675487727324341863597 4121503307897746628198849)
                      ·
                        rfl

theorem cell23_8026599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_8026599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026599 prefixEnd_8026599 := by exact prefixLift 8026599
  have htrace : WordTrace (prefixWord ++ tailWord_8026599) baseStart_8026599 baseEnd_8026599 := by
    simpa [prefixWord, tailWord_8026599, baseEnd_8026599] using wordTrace_append hprefix tailTrace_8026599
  have hstable : (prefixWord ++ tailWord_8026599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026599).length < 2 ^ (prefixWord ++ tailWord_8026599).sum := by decide
  have hdescent : baseEnd_8026599 < baseStart_8026599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026606 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_8026606 : Nat := 118140960795 + 8026606 * 2 ^ 59
def prefixEnd_8026606 : Nat := 4983230072969 + 3 ^ 40 * 8026606 * 2
def baseEnd_8026606 : Nat := 1373835634087442700270439

theorem tailTrace_8026606 : CollatzResearch.WordTrace tailWord_8026606 prefixEnd_8026606 1373835634087442700270439 := by
  unfold tailWord_8026606
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594296444873096501518459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195169581039323181341431781 36594296444873096501518459)
  ·
    refine ⟨54891444667309644752277689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594296444873096501518459 54891444667309644752277689)
    ·
      refine ⟨41168583500482233564208267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54891444667309644752277689 41168583500482233564208267)
      ·
        refine ⟨61752875250723350346312401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41168583500482233564208267 61752875250723350346312401)
        ·
          refine ⟨46314656438042512759734301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61752875250723350346312401 46314656438042512759734301)
          ·
            refine ⟨17367996164265942284900363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46314656438042512759734301 17367996164265942284900363)
            ·
              refine ⟨26051994246398913427350545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17367996164265942284900363 26051994246398913427350545)
              ·
                refine ⟨19538995684799185070512909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26051994246398913427350545 19538995684799185070512909)
                ·
                  refine ⟨7327123381799694401442341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19538995684799185070512909 7327123381799694401442341)
                  ·
                    refine ⟨1373835634087442700270439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327123381799694401442341 1373835634087442700270439)
                    ·
                      rfl

theorem cell23_8026606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_8026606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026606 prefixEnd_8026606 := by exact prefixLift 8026606
  have htrace : WordTrace (prefixWord ++ tailWord_8026606) baseStart_8026606 baseEnd_8026606 := by
    simpa [prefixWord, tailWord_8026606, baseEnd_8026606] using wordTrace_append hprefix tailTrace_8026606
  have hstable : (prefixWord ++ tailWord_8026606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026606).length < 2 ^ (prefixWord ++ tailWord_8026606).sum := by decide
  have hdescent : baseEnd_8026606 < baseStart_8026606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026636 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 6]
def baseStart_8026636 : Nat := 118140960795 + 8026636 * 2 ^ 59
def prefixEnd_8026636 : Nat := 4983230072969 + 3 ^ 40 * 8026636 * 2
def baseEnd_8026636 : Nat := 457946922964662553715131

theorem tailTrace_8026636 : CollatzResearch.WordTrace tailWord_8026636 prefixEnd_8026636 457946922964662553715131 := by
  unfold tailWord_8026636
  simp only [CollatzResearch.WordTrace]
  refine ⟨146377732874438043567869881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195170310499250724757159841 146377732874438043567869881)
  ·
    refine ⟨109783299655828532675902411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146377732874438043567869881 109783299655828532675902411)
    ·
      refine ⟨164674949483742799013853617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109783299655828532675902411 164674949483742799013853617)
      ·
        refine ⟨123506212112807099260390213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164674949483742799013853617 123506212112807099260390213)
        ·
          refine ⟨23157414771151331111323165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123506212112807099260390213 23157414771151331111323165)
          ·
            refine ⟨8684030539181749166746187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23157414771151331111323165 8684030539181749166746187)
            ·
              refine ⟨13026045808772623750119281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684030539181749166746187 13026045808772623750119281)
              ·
                refine ⟨9769534356579467812589461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13026045808772623750119281 9769534356579467812589461)
                ·
                  refine ⟨457946922964662553715131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9769534356579467812589461 457946922964662553715131)
                  ·
                    rfl

theorem cell23_8026636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_8026636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026636 prefixEnd_8026636 := by exact prefixLift 8026636
  have htrace : WordTrace (prefixWord ++ tailWord_8026636) baseStart_8026636 baseEnd_8026636 := by
    simpa [prefixWord, tailWord_8026636, baseEnd_8026636] using wordTrace_append hprefix tailTrace_8026636
  have hstable : (prefixWord ++ tailWord_8026636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026636).length < 2 ^ (prefixWord ++ tailWord_8026636).sum := by decide
  have hdescent : baseEnd_8026636 < baseStart_8026636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026639 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 5, 2]
def baseStart_8026639 : Nat := 118140960795 + 8026639 * 2 ^ 59
def prefixEnd_8026639 : Nat := 4983230072969 + 3 ^ 40 * 8026639 * 2
def baseEnd_8026639 : Nat := 4121523847123926471698665

theorem tailTrace_8026639 : CollatzResearch.WordTrace tailWord_8026639 prefixEnd_8026639 4121523847123926471698665 := by
  unfold tailWord_8026639
  simp only [CollatzResearch.WordTrace]
  refine ⟨292755575167865218648098971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195170383445243479098732647 292755575167865218648098971)
  ·
    refine ⟨439133362751797827972148457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292755575167865218648098971 439133362751797827972148457)
    ·
      refine ⟨329350022063848370979111343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439133362751797827972148457 329350022063848370979111343)
      ·
        refine ⟨494025033095772556468667015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329350022063848370979111343 494025033095772556468667015)
        ·
          refine ⟨741037549643658834703000523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494025033095772556468667015 741037549643658834703000523)
          ·
            refine ⟨1111556324465488252054500785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741037549643658834703000523 1111556324465488252054500785)
            ·
              refine ⟨833667243349116189040875589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111556324465488252054500785 833667243349116189040875589)
              ·
                refine ⟨156312608127959285445164173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833667243349116189040875589 156312608127959285445164173)
                ·
                  refine ⟨58617228047984732041936565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156312608127959285445164173 58617228047984732041936565)
                  ·
                    refine ⟨5495365129498568628931553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58617228047984732041936565 5495365129498568628931553)
                    ·
                      refine ⟨4121523847123926471698665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495365129498568628931553 4121523847123926471698665)
                      ·
                        rfl

theorem cell23_8026639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5, 2].length) (baseStart_8026639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026639 prefixEnd_8026639 := by exact prefixLift 8026639
  have htrace : WordTrace (prefixWord ++ tailWord_8026639) baseStart_8026639 baseEnd_8026639 := by
    simpa [prefixWord, tailWord_8026639, baseEnd_8026639] using wordTrace_append hprefix tailTrace_8026639
  have hstable : (prefixWord ++ tailWord_8026639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026639).length < 2 ^ (prefixWord ++ tailWord_8026639).sum := by decide
  have hdescent : baseEnd_8026639 < baseStart_8026639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026666 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_8026666 : Nat := 118140960795 + 8026666 * 2 ^ 59
def prefixEnd_8026666 : Nat := 4983230072969 + 3 ^ 40 * 8026666 * 2
def baseEnd_8026666 : Nat := 1373845903700532622020347

theorem tailTrace_8026666 : CollatzResearch.WordTrace tailWord_8026666 prefixEnd_8026666 1373845903700532622020347 := by
  unfold tailWord_8026666
  simp only [CollatzResearch.WordTrace]
  refine ⟨73189139984691850564832963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195171039959178268172887901 73189139984691850564832963)
  ·
    refine ⟨109783709977037775847249445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73189139984691850564832963 109783709977037775847249445)
    ·
      refine ⟨20584445620694582971359271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109783709977037775847249445 20584445620694582971359271)
      ·
        refine ⟨30876668431041874457038907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584445620694582971359271 30876668431041874457038907)
        ·
          refine ⟨46315002646562811685558361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30876668431041874457038907 46315002646562811685558361)
          ·
            refine ⟨34736251984922108764168771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46315002646562811685558361 34736251984922108764168771)
            ·
              refine ⟨52104377977383163146253157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34736251984922108764168771 52104377977383163146253157)
              ·
                refine ⟨9769570870759343089922467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52104377977383163146253157 9769570870759343089922467)
                ·
                  refine ⟨14654356306139014634883701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769570870759343089922467 14654356306139014634883701)
                  ·
                    refine ⟨1373845903700532622020347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14654356306139014634883701 1373845903700532622020347)
                    ·
                      rfl

theorem cell23_8026666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_8026666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026666 prefixEnd_8026666 := by exact prefixLift 8026666
  have htrace : WordTrace (prefixWord ++ tailWord_8026666) baseStart_8026666 baseEnd_8026666 := by
    simpa [prefixWord, tailWord_8026666, baseEnd_8026666] using wordTrace_append hprefix tailTrace_8026666
  have hstable : (prefixWord ++ tailWord_8026666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026666).length < 2 ^ (prefixWord ++ tailWord_8026666).sum := by decide
  have hdescent : baseEnd_8026666 < baseStart_8026666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026679 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 6, 4]
def baseStart_8026679 : Nat := 118140960795 + 8026679 * 2 ^ 59
def prefixEnd_8026679 : Nat := 4983230072969 + 3 ^ 40 * 8026679 * 2
def baseEnd_8026679 : Nat := 1373848128783368771732827

theorem tailTrace_8026679 : CollatzResearch.WordTrace tailWord_8026679 prefixEnd_8026679 1373848128783368771732827 := by
  unfold tailWord_8026679
  simp only [CollatzResearch.WordTrace]
  refine ⟨292757034087720305479555091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195171356058480203653036727 292757034087720305479555091)
  ·
    refine ⟨439135551131580458219332637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292757034087720305479555091 439135551131580458219332637)
    ·
      refine ⟨164675831674342671832249739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439135551131580458219332637 164675831674342671832249739)
      ·
        refine ⟨247013747511514007748374609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164675831674342671832249739 247013747511514007748374609)
        ·
          refine ⟨185260310633635505811280957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247013747511514007748374609 185260310633635505811280957)
          ·
            refine ⟨69472616487613314679230359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185260310633635505811280957 69472616487613314679230359)
            ·
              refine ⟨104208924731419972018845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69472616487613314679230359 104208924731419972018845539)
              ·
                refine ⟨156313387097129958028268309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104208924731419972018845539 156313387097129958028268309)
                ·
                  refine ⟨7327190020177966782575077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156313387097129958028268309 7327190020177966782575077)
                  ·
                    refine ⟨1373848128783368771732827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327190020177966782575077 1373848128783368771732827)
                    ·
                      rfl

theorem cell23_8026679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_8026679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026679 prefixEnd_8026679 := by exact prefixLift 8026679
  have htrace : WordTrace (prefixWord ++ tailWord_8026679) baseStart_8026679 baseEnd_8026679 := by
    simpa [prefixWord, tailWord_8026679, baseEnd_8026679] using wordTrace_append hprefix tailTrace_8026679
  have hstable : (prefixWord ++ tailWord_8026679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026679).length < 2 ^ (prefixWord ++ tailWord_8026679).sum := by decide
  have hdescent : baseEnd_8026679 < baseStart_8026679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026703 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 3, 2, 2]
def baseStart_8026703 : Nat := 118140960795 + 8026703 * 2 ^ 59
def prefixEnd_8026703 : Nat := 4983230072969 + 3 ^ 40 * 8026703 * 2
def baseEnd_8026703 : Nat := 4121556709885814221298371

theorem tailTrace_8026703 : CollatzResearch.WordTrace tailWord_8026703 prefixEnd_8026703 4121556709885814221298371 := by
  unfold tailWord_8026703
  simp only [CollatzResearch.WordTrace]
  refine ⟨292757909439633357578428763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195171939626422238385619175 292757909439633357578428763)
  ·
    refine ⟨439136864159450036367643145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292757909439633357578428763 439136864159450036367643145)
    ·
      refine ⟨329352648119587527275732359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439136864159450036367643145 329352648119587527275732359)
      ·
        refine ⟨494028972179381290913598539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329352648119587527275732359 494028972179381290913598539)
        ·
          refine ⟨741043458269071936370397809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494028972179381290913598539 741043458269071936370397809)
          ·
            refine ⟨555782593701803952277798357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741043458269071936370397809 555782593701803952277798357)
            ·
              refine ⟨13026154539886030131510899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555782593701803952277798357 13026154539886030131510899)
              ·
                refine ⟨19539231809829045197266349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026154539886030131510899 19539231809829045197266349)
                ·
                  refine ⟨7327211928685891948974881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19539231809829045197266349 7327211928685891948974881)
                  ·
                    refine ⟨5495408946514418961731161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7327211928685891948974881 5495408946514418961731161)
                    ·
                      refine ⟨4121556709885814221298371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495408946514418961731161 4121556709885814221298371)
                      ·
                        rfl

theorem cell23_8026703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2, 2].length) (baseStart_8026703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026703 prefixEnd_8026703 := by exact prefixLift 8026703
  have htrace : WordTrace (prefixWord ++ tailWord_8026703) baseStart_8026703 baseEnd_8026703 := by
    simpa [prefixWord, tailWord_8026703, baseEnd_8026703] using wordTrace_append hprefix tailTrace_8026703
  have hstable : (prefixWord ++ tailWord_8026703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026703).length < 2 ^ (prefixWord ++ tailWord_8026703).sum := by decide
  have hdescent : baseEnd_8026703 < baseStart_8026703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026706 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_8026706 : Nat := 118140960795 + 8026706 * 2 ^ 59
def prefixEnd_8026706 : Nat := 4983230072969 + 3 ^ 40 * 8026706 * 2
def baseEnd_8026706 : Nat := 4121558250327777709560857

theorem tailTrace_8026706 : CollatzResearch.WordTrace tailWord_8026706 prefixEnd_8026706 4121558250327777709560857 := by
  unfold tailWord_8026706
  simp only [CollatzResearch.WordTrace]
  refine ⟨73189504714655622272696993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195172012572414992727191981 73189504714655622272696993)
  ·
    refine ⟨54892128535991716704522745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73189504714655622272696993 54892128535991716704522745)
    ·
      refine ⟨41169096401993787528392059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54892128535991716704522745 41169096401993787528392059)
      ·
        refine ⟨61753644602990681292588089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41169096401993787528392059 61753644602990681292588089)
        ·
          refine ⟨46315233452243010969441067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61753644602990681292588089 46315233452243010969441067)
          ·
            refine ⟨69472850178364516454161601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46315233452243010969441067 69472850178364516454161601)
            ·
              refine ⟨52104637633773387340621201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69472850178364516454161601 52104637633773387340621201)
              ·
                refine ⟨39078478225330040505465901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52104637633773387340621201 39078478225330040505465901)
                ·
                  refine ⟨14654429334498765189549713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39078478225330040505465901 14654429334498765189549713)
                  ·
                    refine ⟨10990822000874073892162285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14654429334498765189549713 10990822000874073892162285)
                    ·
                      refine ⟨4121558250327777709560857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990822000874073892162285 4121558250327777709560857)
                      ·
                        rfl

theorem cell23_8026706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_8026706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026706 prefixEnd_8026706 := by exact prefixLift 8026706
  have htrace : WordTrace (prefixWord ++ tailWord_8026706) baseStart_8026706 baseEnd_8026706 := by
    simpa [prefixWord, tailWord_8026706, baseEnd_8026706] using wordTrace_append hprefix tailTrace_8026706
  have hstable : (prefixWord ++ tailWord_8026706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026706).length < 2 ^ (prefixWord ++ tailWord_8026706).sum := by decide
  have hdescent : baseEnd_8026706 < baseStart_8026706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026719 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_8026719 : Nat := 118140960795 + 8026719 * 2 ^ 59
def prefixEnd_8026719 : Nat := 4983230072969 + 3 ^ 40 * 8026719 * 2
def baseEnd_8026719 : Nat := 4121564925576286158698297

theorem tailTrace_8026719 : CollatzResearch.WordTrace tailWord_8026719 prefixEnd_8026719 4121564925576286158698297 := by
  unfold tailWord_8026719
  simp only [CollatzResearch.WordTrace]
  refine ⟨292758493007575392311011211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195172328671716928207340807 292758493007575392311011211)
  ·
    refine ⟨439137739511363088466516817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292758493007575392311011211 439137739511363088466516817)
    ·
      refine ⟨329353304633522316349887613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439137739511363088466516817 329353304633522316349887613)
      ·
        refine ⟨123507489237570868631207855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329353304633522316349887613 123507489237570868631207855)
        ·
          refine ⟨185261233856356302946811783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123507489237570868631207855 185261233856356302946811783)
          ·
            refine ⟨277891850784534454420217675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185261233856356302946811783 277891850784534454420217675)
            ·
              refine ⟨416837776176801681630326513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277891850784534454420217675 416837776176801681630326513)
              ·
                refine ⟨312628332132601261222744885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416837776176801681630326513 312628332132601261222744885)
                ·
                  refine ⟨29308906137431368239632333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312628332132601261222744885 29308906137431368239632333)
                  ·
                    refine ⟨10990839801536763089862125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29308906137431368239632333 10990839801536763089862125)
                    ·
                      refine ⟨4121564925576286158698297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990839801536763089862125 4121564925576286158698297)
                      ·
                        rfl

theorem cell23_8026719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_8026719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026719 prefixEnd_8026719 := by exact prefixLift 8026719
  have htrace : WordTrace (prefixWord ++ tailWord_8026719) baseStart_8026719 baseEnd_8026719 := by
    simpa [prefixWord, tailWord_8026719, baseEnd_8026719] using wordTrace_append hprefix tailTrace_8026719
  have hstable : (prefixWord ++ tailWord_8026719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026719).length < 2 ^ (prefixWord ++ tailWord_8026719).sum := by decide
  have hdescent : baseEnd_8026719 < baseStart_8026719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026759 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_8026759 : Nat := 118140960795 + 8026759 * 2 ^ 59
def prefixEnd_8026759 : Nat := 4983230072969 + 3 ^ 40 * 8026759 * 2
def baseEnd_8026759 : Nat := 4121585464802466002198113

theorem tailTrace_8026759 : CollatzResearch.WordTrace tailWord_8026759 prefixEnd_8026759 4121585464802466002198113 := by
  unfold tailWord_8026759
  simp only [CollatzResearch.WordTrace]
  refine ⟨292759951927430479142467331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195173301284953652761644887 292759951927430479142467331)
  ·
    refine ⟨439139927891145718713700997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292759951927430479142467331 439139927891145718713700997)
    ·
      refine ⟨82338736479589822258818937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439139927891145718713700997 82338736479589822258818937)
      ·
        refine ⟨61754052359692366694114203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82338736479589822258818937 61754052359692366694114203)
        ·
          refine ⟨92631078539538550041171305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61754052359692366694114203 92631078539538550041171305)
          ·
            refine ⟨69473308904653912530878479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92631078539538550041171305 69473308904653912530878479)
            ·
              refine ⟨104209963356980868796317719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69473308904653912530878479 104209963356980868796317719)
              ·
                refine ⟨156314945035471303194476579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104209963356980868796317719 156314945035471303194476579)
                ·
                  refine ⟨234472417553206954791714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156314945035471303194476579 234472417553206954791714869)
                  ·
                    refine ⟨21981789145613152011723269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234472417553206954791714869 21981789145613152011723269)
                    ·
                      refine ⟨4121585464802466002198113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21981789145613152011723269 4121585464802466002198113)
                      ·
                        rfl

theorem cell23_8026759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_8026759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026759 prefixEnd_8026759 := by exact prefixLift 8026759
  have htrace : WordTrace (prefixWord ++ tailWord_8026759) baseStart_8026759 baseEnd_8026759 := by
    simpa [prefixWord, tailWord_8026759, baseEnd_8026759] using wordTrace_append hprefix tailTrace_8026759
  have hstable : (prefixWord ++ tailWord_8026759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026759).length < 2 ^ (prefixWord ++ tailWord_8026759).sum := by decide
  have hdescent : baseEnd_8026759 < baseStart_8026759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026770 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_8026770 : Nat := 118140960795 + 8026770 * 2 ^ 59
def prefixEnd_8026770 : Nat := 4983230072969 + 3 ^ 40 * 8026770 * 2
def baseEnd_8026770 : Nat := 4121591113089665459160563

theorem tailTrace_8026770 : CollatzResearch.WordTrace tailWord_8026770 prefixEnd_8026770 4121591113089665459160563 := by
  unfold tailWord_8026770
  simp only [CollatzResearch.WordTrace]
  refine ⟨73190088282597657005279441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195173568753593752014078509 73190088282597657005279441)
  ·
    refine ⟨54892566211948242753959581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73190088282597657005279441 54892566211948242753959581)
    ·
      refine ⟨20584712329480591032734843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54892566211948242753959581 20584712329480591032734843)
      ·
        refine ⟨30877068494220886549102265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584712329480591032734843 30877068494220886549102265)
        ·
          refine ⟨23157801370665664911826699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30877068494220886549102265 23157801370665664911826699)
          ·
            refine ⟨34736702055998497367740049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23157801370665664911826699 34736702055998497367740049)
            ·
              refine ⟨26052526541998873025805037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34736702055998497367740049 26052526541998873025805037)
              ·
                refine ⟨9769697453249577384676889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26052526541998873025805037 9769697453249577384676889)
                ·
                  refine ⟨7327273089937183038507667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9769697453249577384676889 7327273089937183038507667)
                  ·
                    refine ⟨10990909634905774557761501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327273089937183038507667 10990909634905774557761501)
                    ·
                      refine ⟨4121591113089665459160563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10990909634905774557761501 4121591113089665459160563)
                      ·
                        rfl

theorem cell23_8026770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_8026770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026770 prefixEnd_8026770 := by exact prefixLift 8026770
  have htrace : WordTrace (prefixWord ++ tailWord_8026770) baseStart_8026770 baseEnd_8026770 := by
    simpa [prefixWord, tailWord_8026770, baseEnd_8026770] using wordTrace_append hprefix tailTrace_8026770
  have hstable : (prefixWord ++ tailWord_8026770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026770).length < 2 ^ (prefixWord ++ tailWord_8026770).sum := by decide
  have hdescent : baseEnd_8026770 < baseStart_8026770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026789 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_8026789 : Nat := 118140960795 + 8026789 * 2 ^ 59
def prefixEnd_8026789 : Nat := 4983230072969 + 3 ^ 40 * 8026789 * 2
def baseEnd_8026789 : Nat := 4121600869222100884822975

theorem tailTrace_8026789 : CollatzResearch.WordTrace tailWord_8026789 prefixEnd_8026789 4121600869222100884822975 := by
  unfold tailWord_8026789
  simp only [CollatzResearch.WordTrace]
  refine ⟨292761046117321794266059421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195174030744881196177372947 292761046117321794266059421)
  ·
    refine ⟨109785392293995672849772283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292761046117321794266059421 109785392293995672849772283)
    ·
      refine ⟨164678088440993509274658425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109785392293995672849772283 164678088440993509274658425)
      ·
        refine ⟨123508566330745131955993819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164678088440993509274658425 123508566330745131955993819)
        ·
          refine ⟨185262849496117697933990729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123508566330745131955993819 185262849496117697933990729)
          ·
            refine ⟨138947137122088273450493047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185262849496117697933990729 138947137122088273450493047)
            ·
              refine ⟨208420705683132410175739571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138947137122088273450493047 208420705683132410175739571)
              ·
                refine ⟨312631058524698615263609357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208420705683132410175739571 312631058524698615263609357)
                ·
                  refine ⟨117236646946761980723853509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312631058524698615263609357 117236646946761980723853509)
                  ·
                    refine ⟨21981871302517871385722533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117236646946761980723853509 21981871302517871385722533)
                    ·
                      refine ⟨4121600869222100884822975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21981871302517871385722533 4121600869222100884822975)
                      ·
                        rfl

theorem cell23_8026789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_8026789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026789 prefixEnd_8026789 := by exact prefixLift 8026789
  have htrace : WordTrace (prefixWord ++ tailWord_8026789) baseStart_8026789 baseEnd_8026789 := by
    simpa [prefixWord, tailWord_8026789, baseEnd_8026789] using wordTrace_append hprefix tailTrace_8026789
  have hstable : (prefixWord ++ tailWord_8026789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026789).length < 2 ^ (prefixWord ++ tailWord_8026789).sum := by decide
  have hdescent : baseEnd_8026789 < baseStart_8026789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026797 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_8026797 : Nat := 118140960795 + 8026797 * 2 ^ 59
def prefixEnd_8026797 : Nat := 4983230072969 + 3 ^ 40 * 8026797 * 2
def baseEnd_8026797 : Nat := 4121604977067336853522939

theorem tailTrace_8026797 : CollatzResearch.WordTrace tailWord_8026797 prefixEnd_8026797 4121604977067336853522939 := by
  unfold tailWord_8026797
  simp only [CollatzResearch.WordTrace]
  refine ⟨292761337901292811632350645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195174225267528541088233763 292761337901292811632350645)
  ·
    refine ⟨27446375428246201090532873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292761337901292811632350645 27446375428246201090532873)
    ·
      refine ⟨20584781571184650817899655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27446375428246201090532873 20584781571184650817899655)
      ·
        refine ⟨30877172356776976226849483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584781571184650817899655 30877172356776976226849483)
        ·
          refine ⟨46315758535165464340274225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30877172356776976226849483 46315758535165464340274225)
          ·
            refine ⟨34736818901374098255205669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46315758535165464340274225 34736818901374098255205669)
            ·
              refine ⟨6513153544007643422851063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34736818901374098255205669 6513153544007643422851063)
              ·
                refine ⟨9769730316011465134276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513153544007643422851063 9769730316011465134276595)
                ·
                  refine ⟨14654595474017197701414893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769730316011465134276595 14654595474017197701414893)
                  ·
                    refine ⟨5495473302756449138030585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14654595474017197701414893 5495473302756449138030585)
                    ·
                      refine ⟨4121604977067336853522939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495473302756449138030585 4121604977067336853522939)
                      ·
                        rfl

theorem cell23_8026797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_8026797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026797 prefixEnd_8026797 := by exact prefixLift 8026797
  have htrace : WordTrace (prefixWord ++ tailWord_8026797) baseStart_8026797 baseEnd_8026797 := by
    simpa [prefixWord, tailWord_8026797, baseEnd_8026797] using wordTrace_append hprefix tailTrace_8026797
  have hstable : (prefixWord ++ tailWord_8026797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026797).length < 2 ^ (prefixWord ++ tailWord_8026797).sum := by decide
  have hdescent : baseEnd_8026797 < baseStart_8026797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026816 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 7]
def baseStart_8026816 : Nat := 118140960795 + 8026816 * 2 ^ 59
def prefixEnd_8026816 : Nat := 4983230072969 + 3 ^ 40 * 8026816 * 2
def baseEnd_8026816 : Nat := 457957192577752475465039

theorem tailTrace_8026816 : CollatzResearch.WordTrace tailWord_8026816 prefixEnd_8026816 457957192577752475465039 := by
  unfold tailWord_8026816
  simp only [CollatzResearch.WordTrace]
  refine ⟨146381015444111988938646151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195174687258815985251528201 146381015444111988938646151)
  ·
    refine ⟨219571523166167983407969227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146381015444111988938646151 219571523166167983407969227)
    ·
      refine ⟨329357284749251975111953841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219571523166167983407969227 329357284749251975111953841)
      ·
        refine ⟨247017963561938981333965381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329357284749251975111953841 247017963561938981333965381)
        ·
          refine ⟨46315868167863559000118509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247017963561938981333965381 46315868167863559000118509)
          ·
            refine ⟨17368450562948834625044441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46315868167863559000118509 17368450562948834625044441)
            ·
              refine ⟨13026337922211625968783331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17368450562948834625044441 13026337922211625968783331)
              ·
                refine ⟨19539506883317438953174997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026337922211625968783331 19539506883317438953174997)
                ·
                  refine ⟨457957192577752475465039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19539506883317438953174997 457957192577752475465039)
                  ·
                    rfl

theorem cell23_8026816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_8026816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026816 prefixEnd_8026816 := by exact prefixLift 8026816
  have htrace : WordTrace (prefixWord ++ tailWord_8026816) baseStart_8026816 baseEnd_8026816 := by
    simpa [prefixWord, tailWord_8026816, baseEnd_8026816] using wordTrace_append hprefix tailTrace_8026816
  have hstable : (prefixWord ++ tailWord_8026816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026816).length < 2 ^ (prefixWord ++ tailWord_8026816).sum := by decide
  have hdescent : baseEnd_8026816 < baseStart_8026816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026936 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_8026936 : Nat := 118140960795 + 8026936 * 2 ^ 59
def prefixEnd_8026936 : Nat := 4983230072969 + 3 ^ 40 * 8026936 * 2
def baseEnd_8026936 : Nat := 1373892116959437269894933

theorem tailTrace_8026936 : CollatzResearch.WordTrace tailWord_8026936 prefixEnd_8026936 1373892116959437269894933 := by
  unfold tailWord_8026936
  simp only [CollatzResearch.WordTrace]
  refine ⟨146383203823894619185830331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195177605098526158914440441 146383203823894619185830331)
  ·
    refine ⟨219574805735841928778745497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146383203823894619185830331 219574805735841928778745497)
    ·
      refine ⟨164681104301881446584059123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219574805735841928778745497 164681104301881446584059123)
      ·
        refine ⟨247021656452822169876088685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164681104301881446584059123 247021656452822169876088685)
        ·
          refine ⟨92633121169808313703533257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247021656452822169876088685 92633121169808313703533257)
          ·
            refine ⟨69474840877356235277649943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92633121169808313703533257 69474840877356235277649943)
            ·
              refine ⟨104212261316034352916474915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69474840877356235277649943 104212261316034352916474915)
              ·
                refine ⟨156318391974051529374712373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104212261316034352916474915 156318391974051529374712373)
                ·
                  refine ⟨14654849247567330878879285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156318391974051529374712373 14654849247567330878879285)
                  ·
                    refine ⟨1373892116959437269894933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14654849247567330878879285 1373892116959437269894933)
                    ·
                      rfl

theorem cell23_8026936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_8026936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026936 prefixEnd_8026936 := by exact prefixLift 8026936
  have htrace : WordTrace (prefixWord ++ tailWord_8026936) baseStart_8026936 baseEnd_8026936 := by
    simpa [prefixWord, tailWord_8026936, baseEnd_8026936] using wordTrace_append hprefix tailTrace_8026936
  have hstable : (prefixWord ++ tailWord_8026936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026936).length < 2 ^ (prefixWord ++ tailWord_8026936).sum := by decide
  have hdescent : baseEnd_8026936 < baseStart_8026936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026960 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2]
def baseStart_8026960 : Nat := 118140960795 + 8026960 * 2 ^ 59
def prefixEnd_8026960 : Nat := 4983230072969 + 3 ^ 40 * 8026960 * 2
def baseEnd_8026960 : Nat := 4121688674414019715784689

theorem tailTrace_8026960 : CollatzResearch.WordTrace tailWord_8026960 prefixEnd_8026960 4121688674414019715784689 := by
  unfold tailWord_8026960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146383641499851145235267167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195178188666468193647022889 146383641499851145235267167)
  ·
    refine ⟨219575462249776717852900751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146383641499851145235267167 219575462249776717852900751)
    ·
      refine ⟨329363193374665076779351127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219575462249776717852900751 329363193374665076779351127)
      ·
        refine ⟨494044790061997615169026691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329363193374665076779351127 494044790061997615169026691)
        ·
          refine ⟨741067185092996422753540037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494044790061997615169026691 741067185092996422753540037)
          ·
            refine ⟨138950097204936829266288757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741067185092996422753540037 138950097204936829266288757)
            ·
              refine ⟨13026571612962827743714571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138950097204936829266288757 13026571612962827743714571)
              ·
                refine ⟨19539857419444241615571857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026571612962827743714571 19539857419444241615571857)
                ·
                  refine ⟨14654893064583181211678893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19539857419444241615571857 14654893064583181211678893)
                  ·
                    refine ⟨5495584899218692954379585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14654893064583181211678893 5495584899218692954379585)
                    ·
                      refine ⟨4121688674414019715784689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495584899218692954379585 4121688674414019715784689)
                      ·
                        rfl

theorem cell23_8026960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2].length) (baseStart_8026960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026960 prefixEnd_8026960 := by exact prefixLift 8026960
  have htrace : WordTrace (prefixWord ++ tailWord_8026960) baseStart_8026960 baseEnd_8026960 := by
    simpa [prefixWord, tailWord_8026960, baseEnd_8026960] using wordTrace_append hprefix tailTrace_8026960
  have hstable : (prefixWord ++ tailWord_8026960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026960).length < 2 ^ (prefixWord ++ tailWord_8026960).sum := by decide
  have hdescent : baseEnd_8026960 < baseStart_8026960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026967 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_8026967 : Nat := 118140960795 + 8026967 * 2 ^ 59
def prefixEnd_8026967 : Nat := 4983230072969 + 3 ^ 40 * 8026967 * 2
def baseEnd_8026967 : Nat := 4121692268778601188397157

theorem tailTrace_8026967 : CollatzResearch.WordTrace tailWord_8026967 prefixEnd_8026967 4121692268778601188397157 := by
  unfold tailWord_8026967
  simp only [CollatzResearch.WordTrace]
  refine ⟨292767538310676930666039155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195178358873784620444026103 292767538310676930666039155)
  ·
    refine ⟨439151307466015395999058733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292767538310676930666039155 439151307466015395999058733)
    ·
      refine ⟨164681740299755773499647025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439151307466015395999058733 164681740299755773499647025)
      ·
        refine ⟨123511305224816830124735269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164681740299755773499647025 123511305224816830124735269)
        ·
          refine ⟨23158369729653155648387863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123511305224816830124735269 23158369729653155648387863)
          ·
            refine ⟨34737554594479733472581795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23158369729653155648387863 34737554594479733472581795)
            ·
              refine ⟨52106331891719600208872693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34737554594479733472581795 52106331891719600208872693)
              ·
                refine ⟨4884968614848712519581815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52106331891719600208872693 4884968614848712519581815)
                ·
                  refine ⟨7327452922273068779372723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884968614848712519581815 7327452922273068779372723)
                  ·
                    refine ⟨10991179383409603169059085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327452922273068779372723 10991179383409603169059085)
                    ·
                      refine ⟨4121692268778601188397157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991179383409603169059085 4121692268778601188397157)
                      ·
                        rfl

theorem cell23_8026967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_8026967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026967 prefixEnd_8026967 := by exact prefixLift 8026967
  have htrace : WordTrace (prefixWord ++ tailWord_8026967) baseStart_8026967 baseEnd_8026967 := by
    simpa [prefixWord, tailWord_8026967, baseEnd_8026967] using wordTrace_append hprefix tailTrace_8026967
  have hstable : (prefixWord ++ tailWord_8026967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026967).length < 2 ^ (prefixWord ++ tailWord_8026967).sum := by decide
  have hdescent : baseEnd_8026967 < baseStart_8026967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026970 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_8026970 : Nat := 118140960795 + 8026970 * 2 ^ 59
def prefixEnd_8026970 : Nat := 4983230072969 + 3 ^ 40 * 8026970 * 2
def baseEnd_8026970 : Nat := 1373897936406854892219881

theorem tailTrace_8026970 : CollatzResearch.WordTrace tailWord_8026970 prefixEnd_8026970 1373897936406854892219881 := by
  unfold tailWord_8026970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73191911932416515544599591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195178431819777374785598909 73191911932416515544599591)
  ·
    refine ⟨109787867898624773316899387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73191911932416515544599591 109787867898624773316899387)
    ·
      refine ⟨164681801847937159975349081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109787867898624773316899387 164681801847937159975349081)
      ·
        refine ⟨123511351385952869981511811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164681801847937159975349081 123511351385952869981511811)
        ·
          refine ⟨185267027078929304972267717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123511351385952869981511811 185267027078929304972267717)
          ·
            refine ⟨34737567577299244682300197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185267027078929304972267717 34737567577299244682300197)
            ·
              refine ⟨6513293920743608377931287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34737567577299244682300197 6513293920743608377931287)
              ·
                refine ⟨9769940881115412566896931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513293920743608377931287 9769940881115412566896931)
                ·
                  refine ⟨14654911321673118850345397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769940881115412566896931 14654911321673118850345397)
                  ·
                    refine ⟨1373897936406854892219881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14654911321673118850345397 1373897936406854892219881)
                    ·
                      rfl

theorem cell23_8026970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_8026970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026970 prefixEnd_8026970 := by exact prefixLift 8026970
  have htrace : WordTrace (prefixWord ++ tailWord_8026970) baseStart_8026970 baseEnd_8026970 := by
    simpa [prefixWord, tailWord_8026970, baseEnd_8026970] using wordTrace_append hprefix tailTrace_8026970
  have hstable : (prefixWord ++ tailWord_8026970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026970).length < 2 ^ (prefixWord ++ tailWord_8026970).sum := by decide
  have hdescent : baseEnd_8026970 < baseStart_8026970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8026993 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_8026993 : Nat := 118140960795 + 8026993 * 2 ^ 59
def prefixEnd_8026993 : Nat := 4983230072969 + 3 ^ 40 * 8026993 * 2
def baseEnd_8026993 : Nat := 4121705619275618086672037

theorem tailTrace_8026993 : CollatzResearch.WordTrace tailWord_8026993 prefixEnd_8026993 4121705619275618086672037 := by
  unfold tailWord_8026993
  simp only [CollatzResearch.WordTrace]
  refine ⟨292768486608582737106485633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195178991072388491404323755 292768486608582737106485633)
  ·
    refine ⟨219576364956437052829864225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292768486608582737106485633 219576364956437052829864225)
    ·
      refine ⟨164682273717327789622398169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219576364956437052829864225 164682273717327789622398169)
      ·
        refine ⟨123511705287995842216798627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164682273717327789622398169 123511705287995842216798627)
        ·
          refine ⟨185267557931993763325197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123511705287995842216798627 185267557931993763325197941)
          ·
            refine ⟨17368833556124415311737307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185267557931993763325197941 17368833556124415311737307)
            ·
              refine ⟨26053250334186622967605961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17368833556124415311737307 26053250334186622967605961)
              ·
                refine ⟨19539937750639967225704471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26053250334186622967605961 19539937750639967225704471)
                ·
                  refine ⟨29309906625959950838556707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19539937750639967225704471 29309906625959950838556707)
                  ·
                    refine ⟨43964859938939926257835061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29309906625959950838556707 43964859938939926257835061)
                    ·
                      refine ⟨4121705619275618086672037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43964859938939926257835061 4121705619275618086672037)
                      ·
                        rfl

theorem cell23_8026993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_8026993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8026993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8026993 prefixEnd_8026993 := by exact prefixLift 8026993
  have htrace : WordTrace (prefixWord ++ tailWord_8026993) baseStart_8026993 baseEnd_8026993 := by
    simpa [prefixWord, tailWord_8026993, baseEnd_8026993] using wordTrace_append hprefix tailTrace_8026993
  have hstable : (prefixWord ++ tailWord_8026993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8026993).length < 2 ^ (prefixWord ++ tailWord_8026993).sum := by decide
  have hdescent : baseEnd_8026993 < baseStart_8026993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8026993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027003 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4]
def baseStart_8027003 : Nat := 118140960795 + 8027003 * 2 ^ 59
def prefixEnd_8027003 : Nat := 4983230072969 + 3 ^ 40 * 8027003 * 2
def baseEnd_8027003 : Nat := 4121710754082163047546991

theorem tailTrace_8027003 : CollatzResearch.WordTrace tailWord_8027003 prefixEnd_8027003 4121710754082163047546991 := by
  unfold tailWord_8027003
  simp only [CollatzResearch.WordTrace]
  refine ⟨292768851338546508814349663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195179234225697672542899775 292768851338546508814349663)
  ·
    refine ⟨439153277007819763221524495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292768851338546508814349663 439153277007819763221524495)
    ·
      refine ⟨658729915511729644832286743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439153277007819763221524495 658729915511729644832286743)
      ·
        refine ⟨988094873267594467248430115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658729915511729644832286743 988094873267594467248430115)
        ·
          refine ⟨1482142309901391700872645173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988094873267594467248430115 1482142309901391700872645173)
          ·
            refine ⟨138950841553255471956810485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1482142309901391700872645173 138950841553255471956810485)
            ·
              refine ⟨13026641395617700495950983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138950841553255471956810485 13026641395617700495950983)
              ·
                refine ⟨19539962093426550743926475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026641395617700495950983 19539962093426550743926475)
                ·
                  refine ⟨29309943140139826115889713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19539962093426550743926475 29309943140139826115889713)
                  ·
                    refine ⟨21982457355104869586917285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29309943140139826115889713 21982457355104869586917285)
                    ·
                      refine ⟨4121710754082163047546991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21982457355104869586917285 4121710754082163047546991)
                      ·
                        rfl

theorem cell23_8027003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].length) (baseStart_8027003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027003 prefixEnd_8027003 := by exact prefixLift 8027003
  have htrace : WordTrace (prefixWord ++ tailWord_8027003) baseStart_8027003 baseEnd_8027003 := by
    simpa [prefixWord, tailWord_8027003, baseEnd_8027003] using wordTrace_append hprefix tailTrace_8027003
  have hstable : (prefixWord ++ tailWord_8027003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027003).length < 2 ^ (prefixWord ++ tailWord_8027003).sum := by decide
  have hdescent : baseEnd_8027003 < baseStart_8027003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027013 : List Nat := [1, 3, 1, 1, 3, 3, 4, 7]
def baseStart_8027013 : Nat := 118140960795 + 8027013 * 2 ^ 59
def prefixEnd_8027013 : Nat := 4983230072969 + 3 ^ 40 * 8027013 * 2
def baseEnd_8027013 : Nat := 152656144032915111423035

theorem tailTrace_8027013 : CollatzResearch.WordTrace tailWord_8027013 prefixEnd_8027013 152656144032915111423035 := by
  unfold tailWord_8027013
  simp only [CollatzResearch.WordTrace]
  refine ⟨292769216068510280522213693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195179477379006853681475795 292769216068510280522213693)
  ·
    refine ⟨109788456025691355195830135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292769216068510280522213693 109788456025691355195830135)
    ·
      refine ⟨164682684038537032793745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109788456025691355195830135 164682684038537032793745203)
      ·
        refine ⟨247024026057805549190617805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164682684038537032793745203 247024026057805549190617805)
        ·
          refine ⟨92634009771677080946481677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247024026057805549190617805 92634009771677080946481677)
          ·
            refine ⟨34737753664378905354930629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92634009771677080946481677 34737753664378905354930629)
            ·
              refine ⟨6513328812071044754049493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34737753664378905354930629 6513328812071044754049493)
              ·
                refine ⟨152656144032915111423035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6513328812071044754049493 152656144032915111423035)
                ·
                  rfl

theorem cell23_8027013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 7].length) (baseStart_8027013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027013 prefixEnd_8027013 := by exact prefixLift 8027013
  have htrace : WordTrace (prefixWord ++ tailWord_8027013) baseStart_8027013 baseEnd_8027013 := by
    simpa [prefixWord, tailWord_8027013, baseEnd_8027013] using wordTrace_append hprefix tailTrace_8027013
  have hstable : (prefixWord ++ tailWord_8027013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027013).length < 2 ^ (prefixWord ++ tailWord_8027013).sum := by decide
  have hdescent : baseEnd_8027013 < baseStart_8027013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027040 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_8027040 : Nat := 118140960795 + 8027040 * 2 ^ 59
def prefixEnd_8027040 : Nat := 4983230072969 + 3 ^ 40 * 8027040 * 2
def baseEnd_8027040 : Nat := 4121729752866379402784321

theorem tailTrace_8027040 : CollatzResearch.WordTrace tailWord_8027040 prefixEnd_8027040 4121729752866379402784321 := by
  unfold tailWord_8027040
  simp only [CollatzResearch.WordTrace]
  refine ⟨146385100419706232066723287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195180133892941642755631049 146385100419706232066723287)
  ·
    refine ⟨219577650629559348100084931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146385100419706232066723287 219577650629559348100084931)
    ·
      refine ⟨329366475944339022150127397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219577650629559348100084931 329366475944339022150127397)
      ·
        refine ⟨61756214239563566653148887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329366475944339022150127397 61756214239563566653148887)
        ·
          refine ⟨92634321359345349979723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61756214239563566653148887 92634321359345349979723331)
          ·
            refine ⟨138951482039018024969584997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92634321359345349979723331 138951482039018024969584997)
            ·
              refine ⟨26053402882315879681797187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138951482039018024969584997 26053402882315879681797187)
              ·
                refine ⟨39080104323473819522695781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26053402882315879681797187 39080104323473819522695781)
                ·
                  refine ⟨7327519560651341160505459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39080104323473819522695781 7327519560651341160505459)
                  ·
                    refine ⟨10991279340977011740758189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327519560651341160505459 10991279340977011740758189)
                    ·
                      refine ⟨4121729752866379402784321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991279340977011740758189 4121729752866379402784321)
                      ·
                        rfl

theorem cell23_8027040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_8027040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027040 prefixEnd_8027040 := by exact prefixLift 8027040
  have htrace : WordTrace (prefixWord ++ tailWord_8027040) baseStart_8027040 baseEnd_8027040 := by
    simpa [prefixWord, tailWord_8027040, baseEnd_8027040] using wordTrace_append hprefix tailTrace_8027040
  have hstable : (prefixWord ++ tailWord_8027040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027040).length < 2 ^ (prefixWord ++ tailWord_8027040).sum := by decide
  have hdescent : baseEnd_8027040 < baseStart_8027040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027078 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_8027078 : Nat := 118140960795 + 8027078 * 2 ^ 59
def prefixEnd_8027078 : Nat := 4983230072969 + 3 ^ 40 * 8027078 * 2
def baseEnd_8027078 : Nat := 4121749265131250254109147

theorem tailTrace_8027078 : CollatzResearch.WordTrace tailWord_8027078 prefixEnd_8027078 4121749265131250254109147 := by
  unfold tailWord_8027078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149112087914837394479059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195181057875516531082219925 9149112087914837394479059)
  ·
    refine ⟨13723668131872256091718589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149112087914837394479059 13723668131872256091718589)
    ·
      refine ⟨5146375549452096034394471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13723668131872256091718589 5146375549452096034394471)
      ·
        refine ⟨7719563324178144051591707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146375549452096034394471 7719563324178144051591707)
        ·
          refine ⟨11579344986267216077387561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719563324178144051591707 11579344986267216077387561)
          ·
            refine ⟨8684508739700412058040671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11579344986267216077387561 8684508739700412058040671)
            ·
              refine ⟨13026763109550618087061007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684508739700412058040671 13026763109550618087061007)
              ·
                refine ⟨19540144664325927130591511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026763109550618087061007 19540144664325927130591511)
                ·
                  refine ⟨29310216996488890695887267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19540144664325927130591511 29310216996488890695887267)
                  ·
                    refine ⟨43965325494733336043830901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29310216996488890695887267 43965325494733336043830901)
                    ·
                      refine ⟨4121749265131250254109147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43965325494733336043830901 4121749265131250254109147)
                      ·
                        rfl

theorem cell23_8027078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_8027078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027078 prefixEnd_8027078 := by exact prefixLift 8027078
  have htrace : WordTrace (prefixWord ++ tailWord_8027078) baseStart_8027078 baseEnd_8027078 := by
    simpa [prefixWord, tailWord_8027078, baseEnd_8027078] using wordTrace_append hprefix tailTrace_8027078
  have hstable : (prefixWord ++ tailWord_8027078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027078).length < 2 ^ (prefixWord ++ tailWord_8027078).sum := by decide
  have hdescent : baseEnd_8027078 < baseStart_8027078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027083 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_8027083 : Nat := 118140960795 + 8027083 * 2 ^ 59
def prefixEnd_8027083 : Nat := 4983230072969 + 3 ^ 40 * 8027083 * 2
def baseEnd_8027083 : Nat := 4121751832534522734546623

theorem tailTrace_8027083 : CollatzResearch.WordTrace tailWord_8027083 prefixEnd_8027083 4121751832534522734546623 := by
  unfold tailWord_8027083
  simp only [CollatzResearch.WordTrace]
  refine ⟨292771769178256682477261903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195181179452171121651507935 292771769178256682477261903)
  ·
    refine ⟨439157653767385023715892855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292771769178256682477261903 439157653767385023715892855)
    ·
      refine ⟨658736480651077535573839283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439157653767385023715892855 658736480651077535573839283)
      ·
        refine ⟨988104720976616303360758925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658736480651077535573839283 988104720976616303360758925)
        ·
          refine ⟨370539270366231113760284597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988104720976616303360758925 370539270366231113760284597)
          ·
            refine ⟨34738056596834166915026681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370539270366231113760284597 34738056596834166915026681)
            ·
              refine ⟨26053542447625625186270011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34738056596834166915026681 26053542447625625186270011)
              ·
                refine ⟨39080313671438437779405017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26053542447625625186270011 39080313671438437779405017)
                ·
                  refine ⟨29310235253578828334553763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39080313671438437779405017 29310235253578828334553763)
                  ·
                    refine ⟨43965352880368242501830645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29310235253578828334553763 43965352880368242501830645)
                    ·
                      refine ⟨4121751832534522734546623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43965352880368242501830645 4121751832534522734546623)
                      ·
                        rfl

theorem cell23_8027083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_8027083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027083 prefixEnd_8027083 := by exact prefixLift 8027083
  have htrace : WordTrace (prefixWord ++ tailWord_8027083) baseStart_8027083 baseEnd_8027083 := by
    simpa [prefixWord, tailWord_8027083, baseEnd_8027083] using wordTrace_append hprefix tailTrace_8027083
  have hstable : (prefixWord ++ tailWord_8027083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027083).length < 2 ^ (prefixWord ++ tailWord_8027083).sum := by decide
  have hdescent : baseEnd_8027083 < baseStart_8027083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027084 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_8027084 : Nat := 118140960795 + 8027084 * 2 ^ 59
def prefixEnd_8027084 : Nat := 4983230072969 + 3 ^ 40 * 8027084 * 2
def baseEnd_8027084 : Nat := 4121752346015177230634119

theorem tailTrace_8027084 : CollatzResearch.WordTrace tailWord_8027084 prefixEnd_8027084 4121752346015177230634119 := by
  unfold tailWord_8027084
  simp only [CollatzResearch.WordTrace]
  refine ⟨146385902825626529824024153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195181203767502039765365537 146385902825626529824024153)
  ·
    refine ⟨109789427119219897368018115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146385902825626529824024153 109789427119219897368018115)
    ·
      refine ⟨164684140678829846052027173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109789427119219897368018115 164684140678829846052027173)
      ·
        refine ⟨30878276377280596134755095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164684140678829846052027173 30878276377280596134755095)
        ·
          refine ⟨46317414565920894202132643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30878276377280596134755095 46317414565920894202132643)
          ·
            refine ⟨69476121848881341303198965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46317414565920894202132643 69476121848881341303198965)
            ·
              refine ⟨6513386423332625747174903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69476121848881341303198965 6513386423332625747174903)
              ·
                refine ⟨9770079634998938620762355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513386423332625747174903 9770079634998938620762355)
                ·
                  refine ⟨14655119452498407931143533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770079634998938620762355 14655119452498407931143533)
                  ·
                    refine ⟨5495669794686902974178825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655119452498407931143533 5495669794686902974178825)
                    ·
                      refine ⟨4121752346015177230634119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495669794686902974178825 4121752346015177230634119)
                      ·
                        rfl

theorem cell23_8027084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_8027084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027084 prefixEnd_8027084 := by exact prefixLift 8027084
  have htrace : WordTrace (prefixWord ++ tailWord_8027084) baseStart_8027084 baseEnd_8027084 := by
    simpa [prefixWord, tailWord_8027084, baseEnd_8027084] using wordTrace_append hprefix tailTrace_8027084
  have hstable : (prefixWord ++ tailWord_8027084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027084).length < 2 ^ (prefixWord ++ tailWord_8027084).sum := by decide
  have hdescent : baseEnd_8027084 < baseStart_8027084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027114 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_8027114 : Nat := 118140960795 + 8027114 * 2 ^ 59
def prefixEnd_8027114 : Nat := 4983230072969 + 3 ^ 40 * 8027114 * 2
def baseEnd_8027114 : Nat := 4121767750434812113258981

theorem tailTrace_8027114 : CollatzResearch.WordTrace tailWord_8027114 prefixEnd_8027114 4121767750434812113258981 := by
  unfold tailWord_8027114
  simp only [CollatzResearch.WordTrace]
  refine ⟨73193224960286093692910099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195181933227429583181093597 73193224960286093692910099)
  ·
    refine ⟨109789837440429140539365149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73193224960286093692910099 109789837440429140539365149)
    ·
      refine ⟨41171189040160927702261931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109789837440429140539365149 41171189040160927702261931)
      ·
        refine ⟨61756783560241391553392897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41171189040160927702261931 61756783560241391553392897)
        ·
          refine ⟨46317587670181043665044673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61756783560241391553392897 46317587670181043665044673)
          ·
            refine ⟨34738190752635782748783505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46317587670181043665044673 34738190752635782748783505)
            ·
              refine ⟨26053643064476837061587629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34738190752635782748783505 26053643064476837061587629)
              ·
                refine ⟨9770116149178813898095361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26053643064476837061587629 9770116149178813898095361)
                ·
                  refine ⟨7327587111884110423571521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9770116149178813898095361 7327587111884110423571521)
                  ·
                    refine ⟨5495690333913082817678641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7327587111884110423571521 5495690333913082817678641)
                    ·
                      refine ⟨4121767750434812113258981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495690333913082817678641 4121767750434812113258981)
                      ·
                        rfl

theorem cell23_8027114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_8027114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027114 prefixEnd_8027114 := by exact prefixLift 8027114
  have htrace : WordTrace (prefixWord ++ tailWord_8027114) baseStart_8027114 baseEnd_8027114 := by
    simpa [prefixWord, tailWord_8027114, baseEnd_8027114] using wordTrace_append hprefix tailTrace_8027114
  have hstable : (prefixWord ++ tailWord_8027114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027114).length < 2 ^ (prefixWord ++ tailWord_8027114).sum := by decide
  have hdescent : baseEnd_8027114 < baseStart_8027114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027137 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 5]
def baseStart_8027137 : Nat := 118140960795 + 8027137 * 2 ^ 59
def prefixEnd_8027137 : Nat := 4983230072969 + 3 ^ 40 * 8027137 * 2
def baseEnd_8027137 : Nat := 457975506721096169252375

theorem tailTrace_8027137 : CollatzResearch.WordTrace tailWord_8027137 prefixEnd_8027137 457975506721096169252375 := by
  unfold tailWord_8027137
  simp only [CollatzResearch.WordTrace]
  refine ⟨292773738720061049699727665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195182492480040699799818443 292773738720061049699727665)
  ·
    refine ⟨219580304040045787274795749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292773738720061049699727665 219580304040045787274795749)
    ·
      refine ⟨41171307007508585114024203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219580304040045787274795749 41171307007508585114024203)
      ·
        refine ⟨61756960511262877671036305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41171307007508585114024203 61756960511262877671036305)
        ·
          refine ⟨46317720383447158253277229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61756960511262877671036305 46317720383447158253277229)
          ·
            refine ⟨17369145143792684344978961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46317720383447158253277229 17369145143792684344978961)
            ·
              refine ⟨13026858857844513258734221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369145143792684344978961 13026858857844513258734221)
              ·
                refine ⟨4885072071691692472025333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13026858857844513258734221 4885072071691692472025333)
                ·
                  refine ⟨457975506721096169252375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885072071691692472025333 457975506721096169252375)
                  ·
                    rfl

theorem cell23_8027137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 5].length) (baseStart_8027137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027137 prefixEnd_8027137 := by exact prefixLift 8027137
  have htrace : WordTrace (prefixWord ++ tailWord_8027137) baseStart_8027137 baseEnd_8027137 := by
    simpa [prefixWord, tailWord_8027137, baseEnd_8027137] using wordTrace_append hprefix tailTrace_8027137
  have hstable : (prefixWord ++ tailWord_8027137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027137).length < 2 ^ (prefixWord ++ tailWord_8027137).sum := by decide
  have hdescent : baseEnd_8027137 < baseStart_8027137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027170 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_8027170 : Nat := 118140960795 + 8027170 * 2 ^ 59
def prefixEnd_8027170 : Nat := 4983230072969 + 3 ^ 40 * 8027170 * 2
def baseEnd_8027170 : Nat := 4121796505351463894158723

theorem tailTrace_8027170 : CollatzResearch.WordTrace tailWord_8027170 prefixEnd_8027170 4121796505351463894158723 := by
  unfold tailWord_8027170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73193735582235374083919741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195183294885960997557119309 73193735582235374083919741)
  ·
    refine ⟨27447650843338265281469903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73193735582235374083919741 27447650843338265281469903)
    ·
      refine ⟨41171476265007397922204855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27447650843338265281469903 41171476265007397922204855)
      ·
        refine ⟨61757214397511096883307283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41171476265007397922204855 61757214397511096883307283)
        ·
          refine ⟨92635821596266645324960925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61757214397511096883307283 92635821596266645324960925)
          ·
            refine ⟨34738433098599991996860347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92635821596266645324960925 34738433098599991996860347)
            ·
              refine ⟨52107649647899987995290521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34738433098599991996860347 52107649647899987995290521)
              ·
                refine ⟨39080737235924990996467891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52107649647899987995290521 39080737235924990996467891)
                ·
                  refine ⟨58621105853887486494701837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39080737235924990996467891 58621105853887486494701837)
                  ·
                    refine ⟨21982914695207807435513189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58621105853887486494701837 21982914695207807435513189)
                    ·
                      refine ⟨4121796505351463894158723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21982914695207807435513189 4121796505351463894158723)
                      ·
                        rfl

theorem cell23_8027170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_8027170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027170 prefixEnd_8027170 := by exact prefixLift 8027170
  have htrace : WordTrace (prefixWord ++ tailWord_8027170) baseStart_8027170 baseEnd_8027170 := by
    simpa [prefixWord, tailWord_8027170, baseEnd_8027170] using wordTrace_append hprefix tailTrace_8027170
  have hstable : (prefixWord ++ tailWord_8027170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027170).length < 2 ^ (prefixWord ++ tailWord_8027170).sum := by decide
  have hdescent : baseEnd_8027170 < baseStart_8027170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027180 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_8027180 : Nat := 118140960795 + 8027180 * 2 ^ 59
def prefixEnd_8027180 : Nat := 4983230072969 + 3 ^ 40 * 8027180 * 2
def baseEnd_8027180 : Nat := 1373933880052669618344559

theorem tailTrace_8027180 : CollatzResearch.WordTrace tailWord_8027180 prefixEnd_8027180 1373933880052669618344559 := by
  unfold tailWord_8027180
  simp only [CollatzResearch.WordTrace]
  refine ⟨146387653529452634021771497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195183538039270178695695329 146387653529452634021771497)
  ·
    refine ⟨109790740147089475516328623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146387653529452634021771497 109790740147089475516328623)
    ·
      refine ⟨164686110220634213274492935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109790740147089475516328623 164686110220634213274492935)
      ·
        refine ⟨247029165330951319911739403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164686110220634213274492935 247029165330951319911739403)
        ·
          refine ⟨370543747996426979867609105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247029165330951319911739403 370543747996426979867609105)
          ·
            refine ⟨277907810997320234900706829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370543747996426979867609105 277907810997320234900706829)
            ·
              refine ⟨104215429123995088087765061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277907810997320234900706829 104215429123995088087765061)
              ·
                refine ⟨19540392960749079016455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104215429123995088087765061 19540392960749079016455949)
                ·
                  refine ⟨7327647360280904631170981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19540392960749079016455949 7327647360280904631170981)
                  ·
                    refine ⟨1373933880052669618344559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327647360280904631170981 1373933880052669618344559)
                    ·
                      rfl

theorem cell23_8027180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_8027180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027180 prefixEnd_8027180 := by exact prefixLift 8027180
  have htrace : WordTrace (prefixWord ++ tailWord_8027180) baseStart_8027180 baseEnd_8027180 := by
    simpa [prefixWord, tailWord_8027180, baseEnd_8027180] using wordTrace_append hprefix tailTrace_8027180
  have hstable : (prefixWord ++ tailWord_8027180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027180).length < 2 ^ (prefixWord ++ tailWord_8027180).sum := by decide
  have hdescent : baseEnd_8027180 < baseStart_8027180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027207 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_8027207 : Nat := 118140960795 + 8027207 * 2 ^ 59
def prefixEnd_8027207 : Nat := 4983230072969 + 3 ^ 40 * 8027207 * 2
def baseEnd_8027207 : Nat := 4121815504135680249396053

theorem tailTrace_8027207 : CollatzResearch.WordTrace tailWord_8027207 prefixEnd_8027207 4121815504135680249396053 := by
  unfold tailWord_8027207
  simp only [CollatzResearch.WordTrace]
  refine ⟨292776291829807451654775875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195184194553204967769850583 292776291829807451654775875)
  ·
    refine ⟨439164437744711177482163813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292776291829807451654775875 439164437744711177482163813)
    ·
      refine ⟨82343332077133345777905715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439164437744711177482163813 82343332077133345777905715)
      ·
        refine ⟨123514998115700018666858573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82343332077133345777905715 123514998115700018666858573)
        ·
          refine ⟨46318124293387507000071965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123514998115700018666858573 46318124293387507000071965)
          ·
            refine ⟨17369296610020315125026987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46318124293387507000071965 17369296610020315125026987)
            ·
              refine ⟨26053944915030472687540481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17369296610020315125026987 26053944915030472687540481)
              ·
                refine ⟨19540458686272854515655361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26053944915030472687540481 19540458686272854515655361)
                ·
                  refine ⟨14655344014704640886741521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19540458686272854515655361 14655344014704640886741521)
                  ·
                    refine ⟨10991508011028480665056141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14655344014704640886741521 10991508011028480665056141)
                    ·
                      refine ⟨4121815504135680249396053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991508011028480665056141 4121815504135680249396053)
                      ·
                        rfl

theorem cell23_8027207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_8027207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027207 prefixEnd_8027207 := by exact prefixLift 8027207
  have htrace : WordTrace (prefixWord ++ tailWord_8027207) baseStart_8027207 baseEnd_8027207 := by
    simpa [prefixWord, tailWord_8027207, baseEnd_8027207] using wordTrace_append hprefix tailTrace_8027207
  have hstable : (prefixWord ++ tailWord_8027207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027207).length < 2 ^ (prefixWord ++ tailWord_8027207).sum := by decide
  have hdescent : baseEnd_8027207 < baseStart_8027207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027223 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 9]
def baseStart_8027223 : Nat := 118140960795 + 8027223 * 2 ^ 59
def prefixEnd_8027223 : Nat := 4983230072969 + 3 ^ 40 * 8027223 * 2
def baseEnd_8027223 : Nat := 1373941239942050728931993

theorem tailTrace_8027223 : CollatzResearch.WordTrace tailWord_8027223 prefixEnd_8027223 1373941239942050728931993 := by
  unfold tailWord_8027223
  simp only [CollatzResearch.WordTrace]
  refine ⟨292776875397749486387358323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195184583598499657591572215 292776875397749486387358323)
  ·
    refine ⟨439165313096624229581037485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292776875397749486387358323 439165313096624229581037485)
    ·
      refine ⟨164686992411234086092889057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439165313096624229581037485 164686992411234086092889057)
      ·
        refine ⟨123515244308425564569666793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164686992411234086092889057 123515244308425564569666793)
        ·
          refine ⟨92636433231319173427250095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123515244308425564569666793 92636433231319173427250095)
          ·
            refine ⟨138954649846978760140875143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92636433231319173427250095 138954649846978760140875143)
            ·
              refine ⟨208431974770468140211312715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138954649846978760140875143 208431974770468140211312715)
              ·
                refine ⟨312647962155702210316969073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208431974770468140211312715 312647962155702210316969073)
                ·
                  refine ⟨234485971616776657737726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312647962155702210316969073 234485971616776657737726805)
                  ·
                    refine ⟨1373941239942050728931993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234485971616776657737726805 1373941239942050728931993)
                    ·
                      rfl

theorem cell23_8027223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_8027223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027223 prefixEnd_8027223 := by exact prefixLift 8027223
  have htrace : WordTrace (prefixWord ++ tailWord_8027223) baseStart_8027223 baseEnd_8027223 := by
    simpa [prefixWord, tailWord_8027223, baseEnd_8027223] using wordTrace_append hprefix tailTrace_8027223
  have hstable : (prefixWord ++ tailWord_8027223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027223).length < 2 ^ (prefixWord ++ tailWord_8027223).sum := by decide
  have hdescent : baseEnd_8027223 < baseStart_8027223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027237 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_8027237 : Nat := 118140960795 + 8027237 * 2 ^ 59
def prefixEnd_8027237 : Nat := 4983230072969 + 3 ^ 40 * 8027237 * 2
def baseEnd_8027237 : Nat := 4121830908555315132020915

theorem tailTrace_8027237 : CollatzResearch.WordTrace tailWord_8027237 prefixEnd_8027237 4121830908555315132020915 := by
  unfold tailWord_8027237
  simp only [CollatzResearch.WordTrace]
  refine ⟨292777386019698766778367965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195184924013132511185578643 292777386019698766778367965)
  ·
    refine ⟨109791519757387037541887987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292777386019698766778367965 109791519757387037541887987)
    ·
      refine ⟨164687279636080556312831981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109791519757387037541887987 164687279636080556312831981)
      ·
        refine ⟨61757729863530208617311993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164687279636080556312831981 61757729863530208617311993)
        ·
          refine ⟨46318297397647656462983995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61757729863530208617311993 46318297397647656462983995)
          ·
            refine ⟨69477446096471484694475993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46318297397647656462983995 69477446096471484694475993)
            ·
              refine ⟨52108084572353613520856995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69477446096471484694475993 52108084572353613520856995)
              ·
                refine ⟨78162126858530420281285493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52108084572353613520856995 78162126858530420281285493)
                ·
                  refine ⟨7327699392987226901370515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78162126858530420281285493 7327699392987226901370515)
                  ·
                    refine ⟨10991549089480840352055773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327699392987226901370515 10991549089480840352055773)
                    ·
                      refine ⟨4121830908555315132020915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991549089480840352055773 4121830908555315132020915)
                      ·
                        rfl

theorem cell23_8027237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_8027237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027237 prefixEnd_8027237 := by exact prefixLift 8027237
  have htrace : WordTrace (prefixWord ++ tailWord_8027237) baseStart_8027237 baseEnd_8027237 := by
    simpa [prefixWord, tailWord_8027237, baseEnd_8027237] using wordTrace_append hprefix tailTrace_8027237
  have hstable : (prefixWord ++ tailWord_8027237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027237).length < 2 ^ (prefixWord ++ tailWord_8027237).sum := by decide
  have hdescent : baseEnd_8027237 < baseStart_8027237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027287 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 6]
def baseStart_8027287 : Nat := 118140960795 + 8027287 * 2 ^ 59
def prefixEnd_8027287 : Nat := 4983230072969 + 3 ^ 40 * 8027287 * 2
def baseEnd_8027287 : Nat := 1373952194196013312131895

theorem tailTrace_8027287 : CollatzResearch.WordTrace tailWord_8027287 prefixEnd_8027287 1373952194196013312131895 := by
  unfold tailWord_8027287
  simp only [CollatzResearch.WordTrace]
  refine ⟨292779209669517625317688115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195186139779678416878458743 292779209669517625317688115)
  ·
    refine ⟨439168814504276437976532173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292779209669517625317688115 439168814504276437976532173)
    ·
      refine ⟨164688305439103664241199565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439168814504276437976532173 164688305439103664241199565)
      ·
        refine ⟨61758114539663874090449837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164688305439103664241199565 61758114539663874090449837)
        ·
          refine ⟨23159292952373952783918689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61758114539663874090449837 23159292952373952783918689)
          ·
            refine ⟨17369469714280464587939017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23159292952373952783918689 17369469714280464587939017)
            ·
              refine ⟨13027102285710348440954263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369469714280464587939017 13027102285710348440954263)
              ·
                refine ⟨19540653428565522661431395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13027102285710348440954263 19540653428565522661431395)
                ·
                  refine ⟨29310980142848283992147093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19540653428565522661431395 29310980142848283992147093)
                  ·
                    refine ⟨1373952194196013312131895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29310980142848283992147093 1373952194196013312131895)
                    ·
                      rfl

theorem cell23_8027287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_8027287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027287 prefixEnd_8027287 := by exact prefixLift 8027287
  have htrace : WordTrace (prefixWord ++ tailWord_8027287) baseStart_8027287 baseEnd_8027287 := by
    simpa [prefixWord, tailWord_8027287, baseEnd_8027287] using wordTrace_append hprefix tailTrace_8027287
  have hstable : (prefixWord ++ tailWord_8027287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027287).length < 2 ^ (prefixWord ++ tailWord_8027287).sum := by decide
  have hdescent : baseEnd_8027287 < baseStart_8027287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027294 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_8027294 : Nat := 118140960795 + 8027294 * 2 ^ 59
def prefixEnd_8027294 : Nat := 4983230072969 + 3 ^ 40 * 8027294 * 2
def baseEnd_8027294 : Nat := 4121860176952621409008153

theorem tailTrace_8027294 : CollatzResearch.WordTrace tailWord_8027294 prefixEnd_8027294 4121860176952621409008153 := by
  unfold tailWord_8027294
  simp only [CollatzResearch.WordTrace]
  refine ⟨36597433122561533189149117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195186309986994843675461957 36597433122561533189149117)
  ·
    refine ⟨13724037420960574945930919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36597433122561533189149117 13724037420960574945930919)
    ·
      refine ⟨20586056131440862418896379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724037420960574945930919 20586056131440862418896379)
      ·
        refine ⟨30879084197161293628344569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20586056131440862418896379 30879084197161293628344569)
        ·
          refine ⟨23159313147870970221258427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30879084197161293628344569 23159313147870970221258427)
          ·
            refine ⟨34738969721806455331887641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23159313147870970221258427 34738969721806455331887641)
            ·
              refine ⟨26054227291354841498915731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34738969721806455331887641 26054227291354841498915731)
              ·
                refine ⟨39081340937032262248373597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26054227291354841498915731 39081340937032262248373597)
                ·
                  refine ⟨14655502851387098343140099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39081340937032262248373597 14655502851387098343140099)
                  ·
                    refine ⟨21983254277080647514710149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14655502851387098343140099 21983254277080647514710149)
                    ·
                      refine ⟨4121860176952621409008153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21983254277080647514710149 4121860176952621409008153)
                      ·
                        rfl

theorem cell23_8027294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_8027294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027294 prefixEnd_8027294 := by exact prefixLift 8027294
  have htrace : WordTrace (prefixWord ++ tailWord_8027294) baseStart_8027294 baseEnd_8027294 := by
    simpa [prefixWord, tailWord_8027294, baseEnd_8027294] using wordTrace_append hprefix tailTrace_8027294
  have hstable : (prefixWord ++ tailWord_8027294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027294).length < 2 ^ (prefixWord ++ tailWord_8027294).sum := by decide
  have hdescent : baseEnd_8027294 < baseStart_8027294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027297 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_8027297 : Nat := 118140960795 + 8027297 * 2 ^ 59
def prefixEnd_8027297 : Nat := 4983230072969 + 3 ^ 40 * 8027297 * 2
def baseEnd_8027297 : Nat := 4121861717394584897270639

theorem tailTrace_8027297 : CollatzResearch.WordTrace tailWord_8027297 prefixEnd_8027297 4121861717394584897270639 := by
  unfold tailWord_8027297
  simp only [CollatzResearch.WordTrace]
  refine ⟨292779574399481397025552145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195186382932987598017034763 292779574399481397025552145)
  ·
    refine ⟨219584680799611047769164109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292779574399481397025552145 219584680799611047769164109)
    ·
      refine ⟨82344255299854142913436541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219584680799611047769164109 82344255299854142913436541)
      ·
        refine ⟨30879095737445303592538703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82344255299854142913436541 30879095737445303592538703)
        ·
          refine ⟨46318643606167955388808055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30879095737445303592538703 46318643606167955388808055)
          ·
            refine ⟨69477965409251933083212083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46318643606167955388808055 69477965409251933083212083)
            ·
              refine ⟨104216948113877899624818125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69477965409251933083212083 104216948113877899624818125)
              ·
                refine ⟨39081355542704212359306797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104216948113877899624818125 39081355542704212359306797)
                ·
                  refine ⟨14655508328514079634740049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39081355542704212359306797 14655508328514079634740049)
                  ·
                    refine ⟨10991631246385559726055037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14655508328514079634740049 10991631246385559726055037)
                    ·
                      refine ⟨4121861717394584897270639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991631246385559726055037 4121861717394584897270639)
                      ·
                        rfl

theorem cell23_8027297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_8027297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027297 prefixEnd_8027297 := by exact prefixLift 8027297
  have htrace : WordTrace (prefixWord ++ tailWord_8027297) baseStart_8027297 baseEnd_8027297 := by
    simpa [prefixWord, tailWord_8027297, baseEnd_8027297] using wordTrace_append hprefix tailTrace_8027297
  have hstable : (prefixWord ++ tailWord_8027297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027297).length < 2 ^ (prefixWord ++ tailWord_8027297).sum := by decide
  have hdescent : baseEnd_8027297 < baseStart_8027297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027298 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_8027298 : Nat := 118140960795 + 8027298 * 2 ^ 59
def prefixEnd_8027298 : Nat := 4983230072969 + 3 ^ 40 * 8027298 * 2
def baseEnd_8027298 : Nat := 4121862230875239393358135

theorem tailTrace_8027298 : CollatzResearch.WordTrace tailWord_8027298 prefixEnd_8027298 4121862230875239393358135 := by
  unfold tailWord_8027298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73194902718119443549084637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195186407248318516130892365 73194902718119443549084637)
  ·
    refine ⟨27448088519294791330906739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73194902718119443549084637 27448088519294791330906739)
    ·
      refine ⟨41172132778942186996360109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27448088519294791330906739 41172132778942186996360109)
      ·
        refine ⟨15439549792103320123635041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41172132778942186996360109 15439549792103320123635041)
        ·
          refine ⟨11579662344077490092726281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439549792103320123635041 11579662344077490092726281)
          ·
            refine ⟨8684746758058117569544711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11579662344077490092726281 8684746758058117569544711)
            ·
              refine ⟨13027120137087176354317067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684746758058117569544711 13027120137087176354317067)
              ·
                refine ⟨19540680205630764531475601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13027120137087176354317067 19540680205630764531475601)
                ·
                  refine ⟨14655510154223073398606701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19540680205630764531475601 14655510154223073398606701)
                  ·
                    refine ⟨5495816307833652524477513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655510154223073398606701 5495816307833652524477513)
                    ·
                      refine ⟨4121862230875239393358135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495816307833652524477513 4121862230875239393358135)
                      ·
                        rfl

theorem cell23_8027298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_8027298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027298 prefixEnd_8027298 := by exact prefixLift 8027298
  have htrace : WordTrace (prefixWord ++ tailWord_8027298) baseStart_8027298 baseEnd_8027298 := by
    simpa [prefixWord, tailWord_8027298, baseEnd_8027298] using wordTrace_append hprefix tailTrace_8027298
  have hstable : (prefixWord ++ tailWord_8027298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027298).length < 2 ^ (prefixWord ++ tailWord_8027298).sum := by decide
  have hdescent : baseEnd_8027298 < baseStart_8027298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027311 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 1, 2, 2]
def baseStart_8027311 : Nat := 118140960795 + 8027311 * 2 ^ 59
def prefixEnd_8027311 : Nat := 4983230072969 + 3 ^ 40 * 8027311 * 2
def baseEnd_8027311 : Nat := 4121868906123747842495575

theorem tailTrace_8027311 : CollatzResearch.WordTrace tailWord_8027311 prefixEnd_8027311 4121868906123747842495575 := by
  unfold tailWord_8027311
  simp only [CollatzResearch.WordTrace]
  refine ⟨292780085021430677416561787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195186723347620451611041191 292780085021430677416561787)
  ·
    refine ⟨439170127532146016124842681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292780085021430677416561787 439170127532146016124842681)
    ·
      refine ⟨329377595649109512093632011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439170127532146016124842681 329377595649109512093632011)
      ·
        refine ⟨494066393473664268140448017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329377595649109512093632011 494066393473664268140448017)
        ·
          refine ⟨370549795105248201105336013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494066393473664268140448017 370549795105248201105336013)
          ·
            refine ⟨138956173164468075414501005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370549795105248201105336013 138956173164468075414501005)
            ·
              refine ⟨52108564936675528280437877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138956173164468075414501005 52108564936675528280437877)
              ·
                refine ⟨4885177962813330776291051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52108564936675528280437877 4885177962813330776291051)
                ·
                  refine ⟨7327766944219996164436577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885177962813330776291051 7327766944219996164436577)
                  ·
                    refine ⟨5495825208164997123327433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7327766944219996164436577 5495825208164997123327433)
                    ·
                      refine ⟨4121868906123747842495575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495825208164997123327433 4121868906123747842495575)
                      ·
                        rfl

theorem cell23_8027311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 2, 2].length) (baseStart_8027311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027311 prefixEnd_8027311 := by exact prefixLift 8027311
  have htrace : WordTrace (prefixWord ++ tailWord_8027311) baseStart_8027311 baseEnd_8027311 := by
    simpa [prefixWord, tailWord_8027311, baseEnd_8027311] using wordTrace_append hprefix tailTrace_8027311
  have hstable : (prefixWord ++ tailWord_8027311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027311).length < 2 ^ (prefixWord ++ tailWord_8027311).sum := by decide
  have hdescent : baseEnd_8027311 < baseStart_8027311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027314 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_8027314 : Nat := 118140960795 + 8027314 * 2 ^ 59
def prefixEnd_8027314 : Nat := 4983230072969 + 3 ^ 40 * 8027314 * 2
def baseEnd_8027314 : Nat := 4121870446565711330758061

theorem tailTrace_8027314 : CollatzResearch.WordTrace tailWord_8027314 prefixEnd_8027314 4121870446565711330758061 := by
  unfold tailWord_8027314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73195048610104952232230249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195186796293613205952613997 73195048610104952232230249)
  ·
    refine ⟨54896286457578714174172687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73195048610104952232230249 54896286457578714174172687)
    ·
      refine ⟨82344429686368071261259031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54896286457578714174172687 82344429686368071261259031)
      ·
        refine ⟨123516644529552106891888547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82344429686368071261259031 123516644529552106891888547)
        ·
          refine ⟨185274966794328160337832821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123516644529552106891888547 185274966794328160337832821)
          ·
            refine ⟨17369528136968265031671827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185274966794328160337832821 17369528136968265031671827)
            ·
              refine ⟨26054292205452397547507741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17369528136968265031671827 26054292205452397547507741)
              ·
                refine ⟨9770359577044649080315403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26054292205452397547507741 9770359577044649080315403)
                ·
                  refine ⟨14655539365566973620473105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770359577044649080315403 14655539365566973620473105)
                  ·
                    refine ⟨10991654524175230215354829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14655539365566973620473105 10991654524175230215354829)
                    ·
                      refine ⟨4121870446565711330758061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991654524175230215354829 4121870446565711330758061)
                      ·
                        rfl

theorem cell23_8027314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_8027314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027314 prefixEnd_8027314 := by exact prefixLift 8027314
  have htrace : WordTrace (prefixWord ++ tailWord_8027314) baseStart_8027314 baseEnd_8027314 := by
    simpa [prefixWord, tailWord_8027314, baseEnd_8027314] using wordTrace_append hprefix tailTrace_8027314
  have hstable : (prefixWord ++ tailWord_8027314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027314).length < 2 ^ (prefixWord ++ tailWord_8027314).sum := by decide
  have hdescent : baseEnd_8027314 < baseStart_8027314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027341 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_8027341 : Nat := 118140960795 + 8027341 * 2 ^ 59
def prefixEnd_8027341 : Nat := 4983230072969 + 3 ^ 40 * 8027341 * 2
def baseEnd_8027341 : Nat := 4121884310543382725120437

theorem tailTrace_8027341 : CollatzResearch.WordTrace tailWord_8027341 prefixEnd_8027341 4121884310543382725120437 := by
  unfold tailWord_8027341
  simp only [CollatzResearch.WordTrace]
  refine ⟨292781179211321992540153877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195187452807547995026769251 292781179211321992540153877)
  ·
    refine ⟨13724117775530718400319713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292781179211321992540153877 13724117775530718400319713)
    ·
      refine ⟨10293088331648038800239785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13724117775530718400319713 10293088331648038800239785)
      ·
        refine ⟨7719816248736029100179839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10293088331648038800239785 7719816248736029100179839)
        ·
          refine ⟨11579724373104043650269759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719816248736029100179839 11579724373104043650269759)
          ·
            refine ⟨17369586559656065475404639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579724373104043650269759 17369586559656065475404639)
            ·
              refine ⟨26054379839484098213106959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17369586559656065475404639 26054379839484098213106959)
              ·
                refine ⟨39081569759226147319660439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26054379839484098213106959 39081569759226147319660439)
                ·
                  refine ⟨58622354638839220979490659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39081569759226147319660439 58622354638839220979490659)
                  ·
                    refine ⟨87933531958258831469235989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58622354638839220979490659 87933531958258831469235989)
                    ·
                      refine ⟨4121884310543382725120437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87933531958258831469235989 4121884310543382725120437)
                      ·
                        rfl

theorem cell23_8027341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_8027341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027341 prefixEnd_8027341 := by exact prefixLift 8027341
  have htrace : WordTrace (prefixWord ++ tailWord_8027341) baseStart_8027341 baseEnd_8027341 := by
    simpa [prefixWord, tailWord_8027341, baseEnd_8027341] using wordTrace_append hprefix tailTrace_8027341
  have hstable : (prefixWord ++ tailWord_8027341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027341).length < 2 ^ (prefixWord ++ tailWord_8027341).sum := by decide
  have hdescent : baseEnd_8027341 < baseStart_8027341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027348 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8027348 : Nat := 118140960795 + 8027348 * 2 ^ 59
def prefixEnd_8027348 : Nat := 4983230072969 + 3 ^ 40 * 8027348 * 2
def baseEnd_8027348 : Nat := 4121887904907964197732905

theorem tailTrace_8027348 : CollatzResearch.WordTrace tailWord_8027348 prefixEnd_8027348 4121887904907964197732905 := by
  unfold tailWord_8027348
  simp only [CollatzResearch.WordTrace]
  refine ⟨146390717261148316367829349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195187623014864421823772465 146390717261148316367829349)
  ·
    refine ⟨27448259486465309318968003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146390717261148316367829349 27448259486465309318968003)
    ·
      refine ⟨41172389229697963978452005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27448259486465309318968003 41172389229697963978452005)
      ·
        refine ⟨7719822980568368245959751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41172389229697963978452005 7719822980568368245959751)
        ·
          refine ⟨11579734470852552368939627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719822980568368245959751 11579734470852552368939627)
          ·
            refine ⟨17369601706278828553409441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579734470852552368939627 17369601706278828553409441)
            ·
              refine ⟨13027201279709121415057081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369601706278828553409441 13027201279709121415057081)
              ·
                refine ⟨9770400959781841061292811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13027201279709121415057081 9770400959781841061292811)
                ·
                  refine ⟨14655601439672761591939217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770400959781841061292811 14655601439672761591939217)
                  ·
                    refine ⟨10991701079754571193954413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14655601439672761591939217 10991701079754571193954413)
                    ·
                      refine ⟨4121887904907964197732905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991701079754571193954413 4121887904907964197732905)
                      ·
                        rfl

theorem cell23_8027348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8027348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027348 prefixEnd_8027348 := by exact prefixLift 8027348
  have htrace : WordTrace (prefixWord ++ tailWord_8027348) baseStart_8027348 baseEnd_8027348 := by
    simpa [prefixWord, tailWord_8027348, baseEnd_8027348] using wordTrace_append hprefix tailTrace_8027348
  have hstable : (prefixWord ++ tailWord_8027348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027348).length < 2 ^ (prefixWord ++ tailWord_8027348).sum := by decide
  have hdescent : baseEnd_8027348 < baseStart_8027348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027401 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 2, 2, 2]
def baseStart_8027401 : Nat := 118140960795 + 8027401 * 2 ^ 59
def prefixEnd_8027401 : Nat := 4983230072969 + 3 ^ 40 * 8027401 * 2
def baseEnd_8027401 : Nat := 4121915119382652490370161

theorem tailTrace_8027401 : CollatzResearch.WordTrace tailWord_8027401 prefixEnd_8027401 4121915119382652490370161 := by
  unfold tailWord_8027401
  simp only [CollatzResearch.WordTrace]
  refine ⟨292783367591104622787338057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195188911727403081858225371 292783367591104622787338057)
  ·
    refine ⟨219587525693328467090503543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292783367591104622787338057 219587525693328467090503543)
    ·
      refine ⟨329381288539992700635755315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219587525693328467090503543 329381288539992700635755315)
      ·
        refine ⟨494071932809989050953632973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329381288539992700635755315 494071932809989050953632973)
        ·
          refine ⟨185276974803745894107612365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494071932809989050953632973 185276974803745894107612365)
          ·
            refine ⟨69478865551404710290354637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185276974803745894107612365 69478865551404710290354637)
            ·
              refine ⟨26054574581776766358882989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69478865551404710290354637 26054574581776766358882989)
              ·
                refine ⟨9770465468166287384581121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26054574581776766358882989 9770465468166287384581121)
                ·
                  refine ⟨7327849101124715538435841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9770465468166287384581121 7327849101124715538435841)
                  ·
                    refine ⟨5495886825843536653826881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7327849101124715538435841 5495886825843536653826881)
                    ·
                      refine ⟨4121915119382652490370161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495886825843536653826881 4121915119382652490370161)
                      ·
                        rfl

theorem cell23_8027401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2, 2].length) (baseStart_8027401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027401 prefixEnd_8027401 := by exact prefixLift 8027401
  have htrace : WordTrace (prefixWord ++ tailWord_8027401) baseStart_8027401 baseEnd_8027401 := by
    simpa [prefixWord, tailWord_8027401, baseEnd_8027401] using wordTrace_append hprefix tailTrace_8027401
  have hstable : (prefixWord ++ tailWord_8027401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027401).length < 2 ^ (prefixWord ++ tailWord_8027401).sum := by decide
  have hdescent : baseEnd_8027401 < baseStart_8027401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027422 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_8027422 : Nat := 118140960795 + 8027422 * 2 ^ 59
def prefixEnd_8027422 : Nat := 4983230072969 + 3 ^ 40 * 8027422 * 2
def baseEnd_8027422 : Nat := 4121925902476396908207565

theorem tailTrace_8027422 : CollatzResearch.WordTrace tailWord_8027422 prefixEnd_8027422 4121925902476396908207565 := by
  unfold tailWord_8027422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598016690503567921731565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195189422349352362249235013 36598016690503567921731565)
  ·
    refine ⟨13724256258938837970649337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36598016690503567921731565 13724256258938837970649337)
    ·
      refine ⟨10293192194204128477987003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13724256258938837970649337 10293192194204128477987003)
      ·
        refine ⟨15439788291306192716980505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293192194204128477987003 15439788291306192716980505)
        ·
          refine ⟨11579841218479644537735379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439788291306192716980505 11579841218479644537735379)
          ·
            refine ⟨17369761827719466806603069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579841218479644537735379 17369761827719466806603069)
            ·
              refine ⟨6513660685394800052476151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17369761827719466806603069 6513660685394800052476151)
              ·
                refine ⟨9770491028092200078714227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513660685394800052476151 9770491028092200078714227)
                ·
                  refine ⟨14655736542138300118071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770491028092200078714227 14655736542138300118071341)
                  ·
                    refine ⟨5495901203301862544276753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655736542138300118071341 5495901203301862544276753)
                    ·
                      refine ⟨4121925902476396908207565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495901203301862544276753 4121925902476396908207565)
                      ·
                        rfl

theorem cell23_8027422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_8027422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027422 prefixEnd_8027422 := by exact prefixLift 8027422
  have htrace : WordTrace (prefixWord ++ tailWord_8027422) baseStart_8027422 baseEnd_8027422 := by
    simpa [prefixWord, tailWord_8027422, baseEnd_8027422] using wordTrace_append hprefix tailTrace_8027422
  have hstable : (prefixWord ++ tailWord_8027422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027422).length < 2 ^ (prefixWord ++ tailWord_8027422).sum := by decide
  have hdescent : baseEnd_8027422 < baseStart_8027422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027441 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 5]
def baseStart_8027441 : Nat := 118140960795 + 8027441 * 2 ^ 59
def prefixEnd_8027441 : Nat := 4983230072969 + 3 ^ 40 * 8027441 * 2
def baseEnd_8027441 : Nat := 457992850956536925985553

theorem tailTrace_8027441 : CollatzResearch.WordTrace tailWord_8027441 prefixEnd_8027441 457992850956536925985553 := by
  unfold tailWord_8027441
  simp only [CollatzResearch.WordTrace]
  refine ⟨292784826510959709618794177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195189884340639806412529451 292784826510959709618794177)
  ·
    refine ⟨219588619883219782214095633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292784826510959709618794177 219588619883219782214095633)
    ·
      refine ⟨164691464912414836660571725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219588619883219782214095633 164691464912414836660571725)
      ·
        refine ⟨61759299342155563747714397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164691464912414836660571725 61759299342155563747714397)
        ·
          refine ⟨23159737253308336405392899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61759299342155563747714397 23159737253308336405392899)
          ·
            refine ⟨34739605879962504608089349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23159737253308336405392899 34739605879962504608089349)
            ·
              refine ⟨6513676102492969614016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34739605879962504608089349 6513676102492969614016753)
              ·
                refine ⟨4885257076869727210512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513676102492969614016753 4885257076869727210512565)
                ·
                  refine ⟨457992850956536925985553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885257076869727210512565 457992850956536925985553)
                  ·
                    rfl

theorem cell23_8027441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 5].length) (baseStart_8027441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027441 prefixEnd_8027441 := by exact prefixLift 8027441
  have htrace : WordTrace (prefixWord ++ tailWord_8027441) baseStart_8027441 baseEnd_8027441 := by
    simpa [prefixWord, tailWord_8027441, baseEnd_8027441] using wordTrace_append hprefix tailTrace_8027441
  have hstable : (prefixWord ++ tailWord_8027441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027441).length < 2 ^ (prefixWord ++ tailWord_8027441).sum := by decide
  have hdescent : baseEnd_8027441 < baseStart_8027441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027474 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_8027474 : Nat := 118140960795 + 8027474 * 2 ^ 59
def prefixEnd_8027474 : Nat := 4983230072969 + 3 ^ 40 * 8027474 * 2
def baseEnd_8027474 : Nat := 4121952603470430704757325

theorem tailTrace_8027474 : CollatzResearch.WordTrace tailWord_8027474 prefixEnd_8027474 4121952603470430704757325 := by
  unfold tailWord_8027474
  simp only [CollatzResearch.WordTrace]
  refine ⟨73196507529960039063686369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195190686746560104169830317 73196507529960039063686369)
  ·
    refine ⟨54897380647470029297764777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73196507529960039063686369 54897380647470029297764777)
    ·
      refine ⟨41173035485602521973323583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54897380647470029297764777 41173035485602521973323583)
      ·
        refine ⟨61759553228403782959985375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41173035485602521973323583 61759553228403782959985375)
        ·
          refine ⟨92639329842605674439978063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61759553228403782959985375 92639329842605674439978063)
          ·
            refine ⟨138958994763908511659967095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92639329842605674439978063 138958994763908511659967095)
            ·
              refine ⟨208438492145862767489950643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138958994763908511659967095 208438492145862767489950643)
              ·
                refine ⟨312657738218794151234925965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208438492145862767489950643 312657738218794151234925965)
                ·
                  refine ⟨117246651832047806713097237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312657738218794151234925965 117246651832047806713097237)
                  ·
                    refine ⟨5495936804627240939676433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117246651832047806713097237 5495936804627240939676433)
                    ·
                      refine ⟨4121952603470430704757325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495936804627240939676433 4121952603470430704757325)
                      ·
                        rfl

theorem cell23_8027474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_8027474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027474 prefixEnd_8027474 := by exact prefixLift 8027474
  have htrace : WordTrace (prefixWord ++ tailWord_8027474) baseStart_8027474 baseEnd_8027474 := by
    simpa [prefixWord, tailWord_8027474, baseEnd_8027474] using wordTrace_append hprefix tailTrace_8027474
  have hstable : (prefixWord ++ tailWord_8027474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027474).length < 2 ^ (prefixWord ++ tailWord_8027474).sum := by decide
  have hdescent : baseEnd_8027474 < baseStart_8027474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027497 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 6]
def baseStart_8027497 : Nat := 118140960795 + 8027497 * 2 ^ 59
def prefixEnd_8027497 : Nat := 4983230072969 + 3 ^ 40 * 8027497 * 2
def baseEnd_8027497 : Nat := 457996045947276012752191

theorem tailTrace_8027497 : CollatzResearch.WordTrace tailWord_8027497 prefixEnd_8027497 457996045947276012752191 := by
  unfold tailWord_8027497
  simp only [CollatzResearch.WordTrace]
  refine ⟨292786868998756831182832745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195191245999171220788555163 292786868998756831182832745)
  ·
    refine ⟨219590151749067623387124559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292786868998756831182832745 219590151749067623387124559)
    ·
      refine ⟨329385227623601435080686839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219590151749067623387124559 329385227623601435080686839)
      ·
        refine ⟨494077841435402152621030259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329385227623601435080686839 494077841435402152621030259)
        ·
          refine ⟨741116762153103228931545389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494077841435402152621030259 741116762153103228931545389)
          ·
            refine ⟨277918785807413710849329521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741116762153103228931545389 277918785807413710849329521)
            ·
              refine ⟨208439089355560283136997141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277918785807413710849329521 208439089355560283136997141)
              ·
                refine ⟨9770582313541888272046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208439089355560283136997141 9770582313541888272046741)
                ·
                  refine ⟨457996045947276012752191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9770582313541888272046741 457996045947276012752191)
                  ·
                    rfl

theorem cell23_8027497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_8027497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027497 prefixEnd_8027497 := by exact prefixLift 8027497
  have htrace : WordTrace (prefixWord ++ tailWord_8027497) baseStart_8027497 baseEnd_8027497 := by
    simpa [prefixWord, tailWord_8027497, baseEnd_8027497] using wordTrace_append hprefix tailTrace_8027497
  have hstable : (prefixWord ++ tailWord_8027497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027497).length < 2 ^ (prefixWord ++ tailWord_8027497).sum := by decide
  have hdescent : baseEnd_8027497 < baseStart_8027497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027501 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_8027501 : Nat := 118140960795 + 8027501 * 2 ^ 59
def prefixEnd_8027501 : Nat := 4983230072969 + 3 ^ 40 * 8027501 * 2
def baseEnd_8027501 : Nat := 1373988822482700699706567

theorem tailTrace_8027501 : CollatzResearch.WordTrace tailWord_8027501 prefixEnd_8027501 1373988822482700699706567 := by
  unfold tailWord_8027501
  simp only [CollatzResearch.WordTrace]
  refine ⟨292787014890742339865978357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195191343260494893243985571 292787014890742339865978357)
  ·
    refine ⟨27448782646007094362435471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292787014890742339865978357 27448782646007094362435471)
    ·
      refine ⟨41173173969010641543653207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27448782646007094362435471 41173173969010641543653207)
      ·
        refine ⟨61759760953515962315479811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41173173969010641543653207 61759760953515962315479811)
        ·
          refine ⟨92639641430273943473219717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61759760953515962315479811 92639641430273943473219717)
          ·
            refine ⟨17369932768176364401228697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92639641430273943473219717 17369932768176364401228697)
            ·
              refine ⟨13027449576132273300921523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369932768176364401228697 13027449576132273300921523)
              ·
                refine ⟨19541174364198409951382285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13027449576132273300921523 19541174364198409951382285)
                ·
                  refine ⟨7327940386574403731768357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19541174364198409951382285 7327940386574403731768357)
                  ·
                    refine ⟨1373988822482700699706567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327940386574403731768357 1373988822482700699706567)
                    ·
                      rfl

theorem cell23_8027501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_8027501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027501 prefixEnd_8027501 := by exact prefixLift 8027501
  have htrace : WordTrace (prefixWord ++ tailWord_8027501) baseStart_8027501 baseEnd_8027501 := by
    simpa [prefixWord, tailWord_8027501, baseEnd_8027501] using wordTrace_append hprefix tailTrace_8027501
  have hstable : (prefixWord ++ tailWord_8027501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027501).length < 2 ^ (prefixWord ++ tailWord_8027501).sum := by decide
  have hdescent : baseEnd_8027501 < baseStart_8027501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027507 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3]
def baseStart_8027507 : Nat := 118140960795 + 8027507 * 2 ^ 59
def prefixEnd_8027507 : Nat := 4983230072969 + 3 ^ 40 * 8027507 * 2
def baseEnd_8027507 : Nat := 4121969548332029075644673

theorem tailTrace_8027507 : CollatzResearch.WordTrace tailWord_8027507 prefixEnd_8027507 4121969548332029075644673 := by
  unfold tailWord_8027507
  simp only [CollatzResearch.WordTrace]
  refine ⟨292787233728720602890696775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195191489152480401927131183 292787233728720602890696775)
  ·
    refine ⟨439180850593080904336045163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292787233728720602890696775 439180850593080904336045163)
    ·
      refine ⟨658771275889621356504067745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439180850593080904336045163 658771275889621356504067745)
      ·
        refine ⟨494078456917216017378050809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658771275889621356504067745 494078456917216017378050809)
        ·
          refine ⟨370558842687912013033538107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494078456917216017378050809 370558842687912013033538107)
          ·
            refine ⟨555838264031868019550307161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370558842687912013033538107 555838264031868019550307161)
            ·
              refine ⟨416878698023901014662730371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555838264031868019550307161 416878698023901014662730371)
              ·
                refine ⟨625318047035851521994095557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416878698023901014662730371 625318047035851521994095557)
                ·
                  refine ⟨117247133819222160373892917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625318047035851521994095557 117247133819222160373892917)
                  ·
                    refine ⟨10991918795552077535052461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117247133819222160373892917 10991918795552077535052461)
                    ·
                      refine ⟨4121969548332029075644673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10991918795552077535052461 4121969548332029075644673)
                      ·
                        rfl

theorem cell23_8027507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_8027507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027507 prefixEnd_8027507 := by exact prefixLift 8027507
  have htrace : WordTrace (prefixWord ++ tailWord_8027507) baseStart_8027507 baseEnd_8027507 := by
    simpa [prefixWord, tailWord_8027507, baseEnd_8027507] using wordTrace_append hprefix tailTrace_8027507
  have hstable : (prefixWord ++ tailWord_8027507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027507).length < 2 ^ (prefixWord ++ tailWord_8027507).sum := by decide
  have hdescent : baseEnd_8027507 < baseStart_8027507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027517 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_8027517 : Nat := 118140960795 + 8027517 * 2 ^ 59
def prefixEnd_8027517 : Nat := 4983230072969 + 3 ^ 40 * 8027517 * 2
def baseEnd_8027517 : Nat := 4121974683138574036519627

theorem tailTrace_8027517 : CollatzResearch.WordTrace tailWord_8027517 prefixEnd_8027517 4121974683138574036519627 := by
  unfold tailWord_8027517
  simp only [CollatzResearch.WordTrace]
  refine ⟨292787598458684374598560805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195191732305789583065707203 292787598458684374598560805)
  ·
    refine ⟨54897674711003320237230151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292787598458684374598560805 54897674711003320237230151)
    ·
      refine ⟨82346512066504980355845227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54897674711003320237230151 82346512066504980355845227)
      ·
        refine ⟨123519768099757470533767841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82346512066504980355845227 123519768099757470533767841)
        ·
          refine ⟨92639826074818102900325881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123519768099757470533767841 92639826074818102900325881)
          ·
            refine ⟨69479869556113577175244411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92639826074818102900325881 69479869556113577175244411)
            ·
              refine ⟨104219804334170365762866617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69479869556113577175244411 104219804334170365762866617)
              ·
                refine ⟨78164853250627774322149963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104219804334170365762866617 78164853250627774322149963)
                ·
                  refine ⟨117247279875941661483224945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78164853250627774322149963 117247279875941661483224945)
                  ·
                    refine ⟨87935459906956246112418709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117247279875941661483224945 87935459906956246112418709)
                    ·
                      refine ⟨4121974683138574036519627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87935459906956246112418709 4121974683138574036519627)
                      ·
                        rfl

theorem cell23_8027517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_8027517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027517 prefixEnd_8027517 := by exact prefixLift 8027517
  have htrace : WordTrace (prefixWord ++ tailWord_8027517) baseStart_8027517 baseEnd_8027517 := by
    simpa [prefixWord, tailWord_8027517, baseEnd_8027517] using wordTrace_append hprefix tailTrace_8027517
  have hstable : (prefixWord ++ tailWord_8027517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027517).length < 2 ^ (prefixWord ++ tailWord_8027517).sum := by decide
  have hdescent : baseEnd_8027517 < baseStart_8027517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027551 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 4, 3, 2]
def baseStart_8027551 : Nat := 118140960795 + 8027551 * 2 ^ 59
def prefixEnd_8027551 : Nat := 4983230072969 + 3 ^ 40 * 8027551 * 2
def baseEnd_8027551 : Nat := 4121992141480826903494471

theorem tailTrace_8027551 : CollatzResearch.WordTrace tailWord_8027551 prefixEnd_8027551 4121992141480826903494471 := by
  unfold tailWord_8027551
  simp only [CollatzResearch.WordTrace]
  refine ⟨292788838540561198405298507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195192559027040798936865671 292788838540561198405298507)
  ·
    refine ⟨439183257810841797607947761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292788838540561198405298507 439183257810841797607947761)
    ·
      refine ⟨329387443358131348205960821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439183257810841797607947761 329387443358131348205960821)
      ·
        refine ⟨30880072814824813894308827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329387443358131348205960821 30880072814824813894308827)
        ·
          refine ⟨46320109222237220841463241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30880072814824813894308827 46320109222237220841463241)
          ·
            refine ⟨34740081916677915631097431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46320109222237220841463241 34740081916677915631097431)
            ·
              refine ⟨52110122875016873446646147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34740081916677915631097431 52110122875016873446646147)
              ·
                refine ⟨78165184312525310169969221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52110122875016873446646147 78165184312525310169969221)
                ·
                  refine ⟨14655972058598495656869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78165184312525310169969221 14655972058598495656869229)
                  ·
                    refine ⟨5495989521974435871325961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655972058598495656869229 5495989521974435871325961)
                    ·
                      refine ⟨4121992141480826903494471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5495989521974435871325961 4121992141480826903494471)
                      ·
                        rfl

theorem cell23_8027551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_8027551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027551 prefixEnd_8027551 := by exact prefixLift 8027551
  have htrace : WordTrace (prefixWord ++ tailWord_8027551) baseStart_8027551 baseEnd_8027551 := by
    simpa [prefixWord, tailWord_8027551, baseEnd_8027551] using wordTrace_append hprefix tailTrace_8027551
  have hstable : (prefixWord ++ tailWord_8027551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027551).length < 2 ^ (prefixWord ++ tailWord_8027551).sum := by decide
  have hdescent : baseEnd_8027551 < baseStart_8027551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027557 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_8027557 : Nat := 118140960795 + 8027557 * 2 ^ 59
def prefixEnd_8027557 : Nat := 4983230072969 + 3 ^ 40 * 8027557 * 2
def baseEnd_8027557 : Nat := 1373998407454917960006481

theorem tailTrace_8027557 : CollatzResearch.WordTrace tailWord_8027557 prefixEnd_8027557 1373998407454917960006481 := by
  unfold tailWord_8027557
  simp only [CollatzResearch.WordTrace]
  refine ⟨292789057378539461430016925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195192704919026307620011283 292789057378539461430016925)
  ·
    refine ⟨109795896516952298036256347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292789057378539461430016925 109795896516952298036256347)
    ·
      refine ⟨164693844775428447054384521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109795896516952298036256347 164693844775428447054384521)
      ·
        refine ⟨123520383581571335290788391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164693844775428447054384521 123520383581571335290788391)
        ·
          refine ⟨185280575372357002936182587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123520383581571335290788391 185280575372357002936182587)
          ·
            refine ⟨277920863058535504404273881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185280575372357002936182587 277920863058535504404273881)
            ·
              refine ⟨208440647293901628303205411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277920863058535504404273881 208440647293901628303205411)
              ·
                refine ⟨312660970940852442454808117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208440647293901628303205411 312660970940852442454808117)
                ·
                  refine ⟨29311966025704916480138261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312660970940852442454808117 29311966025704916480138261)
                  ·
                    refine ⟨1373998407454917960006481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29311966025704916480138261 1373998407454917960006481)
                    ·
                      rfl

theorem cell23_8027557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_8027557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027557 prefixEnd_8027557 := by exact prefixLift 8027557
  have htrace : WordTrace (prefixWord ++ tailWord_8027557) baseStart_8027557 baseEnd_8027557 := by
    simpa [prefixWord, tailWord_8027557, baseEnd_8027557] using wordTrace_append hprefix tailTrace_8027557
  have hstable : (prefixWord ++ tailWord_8027557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027557).length < 2 ^ (prefixWord ++ tailWord_8027557).sum := by decide
  have hdescent : baseEnd_8027557 < baseStart_8027557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027587 : List Nat := [1, 1, 1, 3, 1, 1, 6, 9]
def baseStart_8027587 : Nat := 118140960795 + 8027587 * 2 ^ 59
def prefixEnd_8027587 : Nat := 4983230072969 + 3 ^ 40 * 8027587 * 2
def baseEnd_8027587 : Nat := 152667060251273657875715

theorem tailTrace_8027587 : CollatzResearch.WordTrace tailWord_8027587 prefixEnd_8027587 152667060251273657875715 := by
  unfold tailWord_8027587
  simp only [CollatzResearch.WordTrace]
  refine ⟨292790151568430776553609015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195193434378953851035739343 292790151568430776553609015)
  ·
    refine ⟨439185227352646164830413523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292790151568430776553609015 439185227352646164830413523)
    ·
      refine ⟨658777841028969247245620285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439185227352646164830413523 658777841028969247245620285)
      ·
        refine ⟨247041690385863467717107607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 658777841028969247245620285 247041690385863467717107607)
        ·
          refine ⟨370562535578795201575661411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247041690385863467717107607 370562535578795201575661411)
          ·
            refine ⟨555843803368192802363492117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370562535578795201575661411 555843803368192802363492117)
            ·
              refine ⟨26055178282884037610788693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 555843803368192802363492117 26055178282884037610788693)
              ·
                refine ⟨152667060251273657875715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26055178282884037610788693 152667060251273657875715)
                ·
                  rfl

theorem cell23_8027587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 9].length) (baseStart_8027587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027587 prefixEnd_8027587 := by exact prefixLift 8027587
  have htrace : WordTrace (prefixWord ++ tailWord_8027587) baseStart_8027587 baseEnd_8027587 := by
    simpa [prefixWord, tailWord_8027587, baseEnd_8027587] using wordTrace_append hprefix tailTrace_8027587
  have hstable : (prefixWord ++ tailWord_8027587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027587).length < 2 ^ (prefixWord ++ tailWord_8027587).sum := by decide
  have hdescent : baseEnd_8027587 < baseStart_8027587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027594 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_8027594 : Nat := 118140960795 + 8027594 * 2 ^ 59
def prefixEnd_8027594 : Nat := 4983230072969 + 3 ^ 40 * 8027594 * 2
def baseEnd_8027594 : Nat := 4122014221148970235256773

theorem tailTrace_8027594 : CollatzResearch.WordTrace tailWord_8027594 prefixEnd_8027594 4122014221148970235256773 := by
  unfold tailWord_8027594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73197601719851354187278459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195193604586270277832742557 73197601719851354187278459)
  ·
    refine ⟨109796402579777031280917689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73197601719851354187278459 109796402579777031280917689)
    ·
      refine ⟨82347301934832773460688267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109796402579777031280917689 82347301934832773460688267)
      ·
        refine ⟨123520952902249160191032401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82347301934832773460688267 123520952902249160191032401)
        ·
          refine ⟨92640714676686870143274301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123520952902249160191032401 92640714676686870143274301)
          ·
            refine ⟨34740268003757576303727863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92640714676686870143274301 34740268003757576303727863)
            ·
              refine ⟨52110402005636364455591795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34740268003757576303727863 52110402005636364455591795)
              ·
                refine ⟨78165603008454546683387693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52110402005636364455591795 78165603008454546683387693)
                ·
                  refine ⟨29312101128170455006270385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78165603008454546683387693 29312101128170455006270385)
                  ·
                    refine ⟨21984075846127841254702789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29312101128170455006270385 21984075846127841254702789)
                    ·
                      refine ⟨4122014221148970235256773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21984075846127841254702789 4122014221148970235256773)
                      ·
                        rfl

theorem cell23_8027594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_8027594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027594 prefixEnd_8027594 := by exact prefixLift 8027594
  have htrace : WordTrace (prefixWord ++ tailWord_8027594) baseStart_8027594 baseEnd_8027594 := by
    simpa [prefixWord, tailWord_8027594, baseEnd_8027594] using wordTrace_append hprefix tailTrace_8027594
  have hstable : (prefixWord ++ tailWord_8027594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027594).length < 2 ^ (prefixWord ++ tailWord_8027594).sum := by decide
  have hdescent : baseEnd_8027594 < baseStart_8027594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027604 : List Nat := [2, 4, 1, 2, 3, 11]
def baseStart_8027604 : Nat := 118140960795 + 8027604 * 2 ^ 59
def prefixEnd_8027604 : Nat := 4983230072969 + 3 ^ 40 * 8027604 * 2
def baseEnd_8027604 : Nat := 16963042617100885580789

theorem tailTrace_8027604 : CollatzResearch.WordTrace tailWord_8027604 prefixEnd_8027604 16963042617100885580789 := by
  unfold tailWord_8027604
  simp only [CollatzResearch.WordTrace]
  refine ⟨146395385804684594228488933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195193847739579458971318577 146395385804684594228488933)
  ·
    refine ⟨27449134838378361417841675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146395385804684594228488933 27449134838378361417841675)
    ·
      refine ⟨41173702257567542126762513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449134838378361417841675 41173702257567542126762513)
      ·
        refine ⟨30880276693175656595071885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41173702257567542126762513 30880276693175656595071885)
        ·
          refine ⟨11580103759940871223151957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30880276693175656595071885 11580103759940871223151957)
          ·
            refine ⟨16963042617100885580789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11580103759940871223151957 16963042617100885580789)
            ·
              rfl

theorem cell23_8027604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 11].length) (baseStart_8027604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027604 prefixEnd_8027604 := by exact prefixLift 8027604
  have htrace : WordTrace (prefixWord ++ tailWord_8027604) baseStart_8027604 baseEnd_8027604 := by
    simpa [prefixWord, tailWord_8027604, baseEnd_8027604] using wordTrace_append hprefix tailTrace_8027604
  have hstable : (prefixWord ++ tailWord_8027604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027604).length < 2 ^ (prefixWord ++ tailWord_8027604).sum := by decide
  have hdescent : baseEnd_8027604 < baseStart_8027604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027615 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 1, 2, 2]
def baseStart_8027615 : Nat := 118140960795 + 8027615 * 2 ^ 59
def prefixEnd_8027615 : Nat := 4983230072969 + 3 ^ 40 * 8027615 * 2
def baseEnd_8027615 : Nat := 4122025004242714653094177

theorem tailTrace_8027615 : CollatzResearch.WordTrace tailWord_8027615 prefixEnd_8027615 4122025004242714653094177 := by
  unfold tailWord_8027615
  simp only [CollatzResearch.WordTrace]
  refine ⟨292791172812329337335628299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195194115208219558223752199 292791172812329337335628299)
  ·
    refine ⟨439186759218494006003442449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292791172812329337335628299 439186759218494006003442449)
    ·
      refine ⟨329390069413870504502581837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439186759218494006003442449 329390069413870504502581837)
      ·
        refine ⟨123521276030201439188468189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329390069413870504502581837 123521276030201439188468189)
        ·
          refine ⟨46320478511325539695675571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123521276030201439188468189 46320478511325539695675571)
          ·
            refine ⟨69480717766988309543513357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46320478511325539695675571 69480717766988309543513357)
            ·
              refine ⟨26055269162620616078817509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69480717766988309543513357 26055269162620616078817509)
              ·
                refine ⟨4885362967991365514778283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26055269162620616078817509 4885362967991365514778283)
                ·
                  refine ⟨7328044451987048272167425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885362967991365514778283 7328044451987048272167425)
                  ·
                    refine ⟨5496033338990286204125569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7328044451987048272167425 5496033338990286204125569)
                    ·
                      refine ⟨4122025004242714653094177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496033338990286204125569 4122025004242714653094177)
                      ·
                        rfl

theorem cell23_8027615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_8027615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027615 prefixEnd_8027615 := by exact prefixLift 8027615
  have htrace : WordTrace (prefixWord ++ tailWord_8027615) baseStart_8027615 baseEnd_8027615 := by
    simpa [prefixWord, tailWord_8027615, baseEnd_8027615] using wordTrace_append hprefix tailTrace_8027615
  have hstable : (prefixWord ++ tailWord_8027615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027615).length < 2 ^ (prefixWord ++ tailWord_8027615).sum := by decide
  have hdescent : baseEnd_8027615 < baseStart_8027615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027621 : List Nat := [1, 3, 1, 5, 1, 3, 1, 8]
def baseStart_8027621 : Nat := 118140960795 + 8027621 * 2 ^ 59
def prefixEnd_8027621 : Nat := 4983230072969 + 3 ^ 40 * 8027621 * 2
def baseEnd_8027621 : Nat := 152667706856542282578487

theorem tailTrace_8027621 : CollatzResearch.WordTrace tailWord_8027621 prefixEnd_8027621 152667706856542282578487 := by
  unfold tailWord_8027621
  simp only [CollatzResearch.WordTrace]
  refine ⟨292791391650307600360346717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195194261100205066906897811 292791391650307600360346717)
  ·
    refine ⟨109796771868865350135130019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292791391650307600360346717 109796771868865350135130019)
    ·
      refine ⟨164695157803298025202695029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109796771868865350135130019 164695157803298025202695029)
      ·
        refine ⟨15440171044059189862752659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164695157803298025202695029 15440171044059189862752659)
        ·
          refine ⟨23160256566088784794128989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15440171044059189862752659 23160256566088784794128989)
          ·
            refine ⟨8685096212283294297798371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23160256566088784794128989 8685096212283294297798371)
            ·
              refine ⟨13027644318424941446697557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685096212283294297798371 13027644318424941446697557)
              ·
                refine ⟨152667706856542282578487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13027644318424941446697557 152667706856542282578487)
                ·
                  rfl

theorem cell23_8027621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 8].length) (baseStart_8027621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027621 prefixEnd_8027621 := by exact prefixLift 8027621
  have htrace : WordTrace (prefixWord ++ tailWord_8027621) baseStart_8027621 baseEnd_8027621 := by
    simpa [prefixWord, tailWord_8027621, baseEnd_8027621] using wordTrace_append hprefix tailTrace_8027621
  have hstable : (prefixWord ++ tailWord_8027621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027621).length < 2 ^ (prefixWord ++ tailWord_8027621).sum := by decide
  have hdescent : baseEnd_8027621 < baseStart_8027621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027652 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_8027652 : Nat := 118140960795 + 8027652 * 2 ^ 59
def prefixEnd_8027652 : Nat := 4983230072969 + 3 ^ 40 * 8027652 * 2
def baseEnd_8027652 : Nat := 4122044003026931008331507

theorem tailTrace_8027652 : CollatzResearch.WordTrace tailWord_8027652 prefixEnd_8027652 4122044003026931008331507 := by
  unfold tailWord_8027652
  simp only [CollatzResearch.WordTrace]
  refine ⟨146396261156597646327362605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195195014875463528436483473 146396261156597646327362605)
  ·
    refine ⟨54898597933724117372760977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146396261156597646327362605 54898597933724117372760977)
    ·
      refine ⟨41173948450293088029570733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54898597933724117372760977 41173948450293088029570733)
      ·
        refine ⟨15440230668859908011089025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41173948450293088029570733 15440230668859908011089025)
        ·
          refine ⟨11580173001644931008316769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15440230668859908011089025 11580173001644931008316769)
          ·
            refine ⟨8685129751233698256237577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580173001644931008316769 8685129751233698256237577)
            ·
              refine ⟨6513847313425273692178183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685129751233698256237577 6513847313425273692178183)
              ·
                refine ⟨9770770970137910538267275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513847313425273692178183 9770770970137910538267275)
                ·
                  refine ⟨14656156455206865807400913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770770970137910538267275 14656156455206865807400913)
                  ·
                    refine ⟨10992117341405149355550685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14656156455206865807400913 10992117341405149355550685)
                    ·
                      refine ⟨4122044003026931008331507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992117341405149355550685 4122044003026931008331507)
                      ·
                        rfl

theorem cell23_8027652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_8027652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027652 prefixEnd_8027652 := by exact prefixLift 8027652
  have htrace : WordTrace (prefixWord ++ tailWord_8027652) baseStart_8027652 baseEnd_8027652 := by
    simpa [prefixWord, tailWord_8027652, baseEnd_8027652] using wordTrace_append hprefix tailTrace_8027652
  have hstable : (prefixWord ++ tailWord_8027652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027652).length < 2 ^ (prefixWord ++ tailWord_8027652).sum := by decide
  have hdescent : baseEnd_8027652 < baseStart_8027652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027674 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_8027674 : Nat := 118140960795 + 8027674 * 2 ^ 59
def prefixEnd_8027674 : Nat := 4983230072969 + 3 ^ 40 * 8027674 * 2
def baseEnd_8027674 : Nat := 4122055299601329922256405

theorem tailTrace_8027674 : CollatzResearch.WordTrace tailWord_8027674 prefixEnd_8027674 4122055299601329922256405 := by
  unfold tailWord_8027674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73198331179778897603006519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195195549812743726941350717 73198331179778897603006519)
  ·
    refine ⟨109797496769668346404509779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73198331179778897603006519 109797496769668346404509779)
    ·
      refine ⟨164696245154502519606764669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109797496769668346404509779 164696245154502519606764669)
      ·
        refine ⟨61761091932938444852536751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164696245154502519606764669 61761091932938444852536751)
        ·
          refine ⟨92641637899407667278805127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61761091932938444852536751 92641637899407667278805127)
          ·
            refine ⟨138962456849111500918207691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92641637899407667278805127 138962456849111500918207691)
            ·
              refine ⟨208443685273667251377311537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138962456849111500918207691 208443685273667251377311537)
              ·
                refine ⟨156332763955250438532983653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208443685273667251377311537 156332763955250438532983653)
                ·
                  refine ⟨29312393241609457224934435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156332763955250438532983653 29312393241609457224934435)
                  ·
                    refine ⟨43968589862414185837401653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29312393241609457224934435 43968589862414185837401653)
                    ·
                      refine ⟨4122055299601329922256405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43968589862414185837401653 4122055299601329922256405)
                      ·
                        rfl

theorem cell23_8027674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_8027674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027674 prefixEnd_8027674 := by exact prefixLift 8027674
  have htrace : WordTrace (prefixWord ++ tailWord_8027674) baseStart_8027674 baseEnd_8027674 := by
    simpa [prefixWord, tailWord_8027674, baseEnd_8027674] using wordTrace_append hprefix tailTrace_8027674
  have hstable : (prefixWord ++ tailWord_8027674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027674).length < 2 ^ (prefixWord ++ tailWord_8027674).sum := by decide
  have hdescent : baseEnd_8027674 < baseStart_8027674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027728 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 5]
def baseStart_8027728 : Nat := 118140960795 + 8027728 * 2 ^ 59
def prefixEnd_8027728 : Nat := 4983230072969 + 3 ^ 40 * 8027728 * 2
def baseEnd_8027728 : Nat := 458009225284074745664573

theorem tailTrace_8027728 : CollatzResearch.WordTrace tailWord_8027728 prefixEnd_8027728 458009225284074745664573 := by
  unfold tailWord_8027728
  simp only [CollatzResearch.WordTrace]
  refine ⟨146397647130459978817245919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195196862840613305089661225 146397647130459978817245919)
  ·
    refine ⟨219596470695689968225868879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146397647130459978817245919 219596470695689968225868879)
    ·
      refine ⟨329394706043534952338803319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219596470695689968225868879 329394706043534952338803319)
      ·
        refine ⟨494092059065302428508204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329394706043534952338803319 494092059065302428508204979)
        ·
          refine ⟨741138088597953642762307469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494092059065302428508204979 741138088597953642762307469)
          ·
            refine ⟨277926783224232616035865301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741138088597953642762307469 277926783224232616035865301)
            ·
              refine ⟨6513908981817951938340593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277926783224232616035865301 6513908981817951938340593)
              ·
                refine ⟨4885431736363463953755445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513908981817951938340593 4885431736363463953755445)
                ·
                  refine ⟨458009225284074745664573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885431736363463953755445 458009225284074745664573)
                  ·
                    rfl

theorem cell23_8027728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 5].length) (baseStart_8027728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027728 prefixEnd_8027728 := by exact prefixLift 8027728
  have htrace : WordTrace (prefixWord ++ tailWord_8027728) baseStart_8027728 baseEnd_8027728 := by
    simpa [prefixWord, tailWord_8027728, baseEnd_8027728] using wordTrace_append hprefix tailTrace_8027728
  have hstable : (prefixWord ++ tailWord_8027728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027728).length < 2 ^ (prefixWord ++ tailWord_8027728).sum := by decide
  have hdescent : baseEnd_8027728 < baseStart_8027728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027851 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4]
def baseStart_8027851 : Nat := 118140960795 + 8027851 * 2 ^ 59
def prefixEnd_8027851 : Nat := 4983230072969 + 3 ^ 40 * 8027851 * 2
def baseEnd_8027851 : Nat := 4122146185677175729743091

theorem tailTrace_8027851 : CollatzResearch.WordTrace tailWord_8027851 prefixEnd_8027851 4122146185677175729743091 := by
  unfold tailWord_8027851
  simp only [CollatzResearch.WordTrace]
  refine ⟨292799780439474349641219407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195199853626316233094146271 292799780439474349641219407)
  ·
    refine ⟨439199670659211524461829111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292799780439474349641219407 439199670659211524461829111)
    ·
      refine ⟨658799505988817286692743667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439199670659211524461829111 658799505988817286692743667)
      ·
        refine ⟨988199258983225930039115501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658799505988817286692743667 988199258983225930039115501)
        ·
          refine ⟨370574722118709723764668313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988199258983225930039115501 370574722118709723764668313)
          ·
            refine ⟨277931041589032292823501235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370574722118709723764668313 277931041589032292823501235)
            ·
              refine ⟨416896562383548439235251853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277931041589032292823501235 416896562383548439235251853)
              ·
                refine ⟨156336210893830664713219445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416896562383548439235251853 156336210893830664713219445)
                ·
                  refine ⟨14656519771296624816864323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156336210893830664713219445 14656519771296624816864323)
                  ·
                    refine ⟨21984779656944937225296485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14656519771296624816864323 21984779656944937225296485)
                    ·
                      refine ⟨4122146185677175729743091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21984779656944937225296485 4122146185677175729743091)
                      ·
                        rfl

theorem cell23_8027851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_8027851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027851 prefixEnd_8027851 := by exact prefixLift 8027851
  have htrace : WordTrace (prefixWord ++ tailWord_8027851) baseStart_8027851 baseEnd_8027851 := by
    simpa [prefixWord, tailWord_8027851, baseEnd_8027851] using wordTrace_append hprefix tailTrace_8027851
  have hstable : (prefixWord ++ tailWord_8027851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027851).length < 2 ^ (prefixWord ++ tailWord_8027851).sum := by decide
  have hdescent : baseEnd_8027851 < baseStart_8027851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027871 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_8027871 : Nat := 118140960795 + 8027871 * 2 ^ 59
def prefixEnd_8027871 : Nat := 4983230072969 + 3 ^ 40 * 8027871 * 2
def baseEnd_8027871 : Nat := 4122156455290265651492999

theorem tailTrace_8027871 : CollatzResearch.WordTrace tailWord_8027871 prefixEnd_8027871 4122156455290265651492999 := by
  unfold tailWord_8027871
  simp only [CollatzResearch.WordTrace]
  refine ⟨292800509899401893056947467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195200339932934595371298311 292800509899401893056947467)
  ·
    refine ⟨439200764849102839585421201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292800509899401893056947467 439200764849102839585421201)
    ·
      refine ⟨329400573636827129689065901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439200764849102839585421201 329400573636827129689065901)
      ·
        refine ⟨123525215113810173633399713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329400573636827129689065901 123525215113810173633399713)
        ·
          refine ⟨92643911335357630225049785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123525215113810173633399713 92643911335357630225049785)
          ·
            refine ⟨69482933501518222668787339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92643911335357630225049785 69482933501518222668787339)
            ·
              refine ⟨104224400252277334003181009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69482933501518222668787339 104224400252277334003181009)
              ·
                refine ⟨78168300189208000502385757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104224400252277334003181009 78168300189208000502385757)
                ·
                  refine ⟨29313112570953000188394659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78168300189208000502385757 29313112570953000188394659)
                  ·
                    refine ⟨43969668856429500282591989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29313112570953000188394659 43969668856429500282591989)
                    ·
                      refine ⟨4122156455290265651492999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43969668856429500282591989 4122156455290265651492999)
                      ·
                        rfl

theorem cell23_8027871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_8027871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027871 prefixEnd_8027871 := by exact prefixLift 8027871
  have htrace : WordTrace (prefixWord ++ tailWord_8027871) baseStart_8027871 baseEnd_8027871 := by
    simpa [prefixWord, tailWord_8027871, baseEnd_8027871] using wordTrace_append hprefix tailTrace_8027871
  have hstable : (prefixWord ++ tailWord_8027871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027871).length < 2 ^ (prefixWord ++ tailWord_8027871).sum := by decide
  have hdescent : baseEnd_8027871 < baseStart_8027871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027881 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_8027881 : Nat := 118140960795 + 8027881 * 2 ^ 59
def prefixEnd_8027881 : Nat := 4983230072969 + 3 ^ 40 * 8027881 * 2
def baseEnd_8027881 : Nat := 4122161590096810612367953

theorem tailTrace_8027881 : CollatzResearch.WordTrace tailWord_8027881 prefixEnd_8027881 4122161590096810612367953 := by
  unfold tailWord_8027881
  simp only [CollatzResearch.WordTrace]
  refine ⟨292800874629365664764811497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195200583086243776509874331 292800874629365664764811497)
  ·
    refine ⟨219600655972024248573608623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292800874629365664764811497 219600655972024248573608623)
    ·
      refine ⟨329400983958036372860412935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219600655972024248573608623 329400983958036372860412935)
      ·
        refine ⟨494101475937054559290619403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329400983958036372860412935 494101475937054559290619403)
        ·
          refine ⟨741152213905581838935929105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494101475937054559290619403 741152213905581838935929105)
          ·
            refine ⟨555864160429186379201946829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741152213905581838935929105 555864160429186379201946829)
            ·
              refine ⟨208449060160944892200730061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555864160429186379201946829 208449060160944892200730061)
              ·
                refine ⟨78168397560354334575273773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208449060160944892200730061 78168397560354334575273773)
                ·
                  refine ⟨29313149085132875465727665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78168397560354334575273773 29313149085132875465727665)
                  ·
                    refine ⟨21984861813849656599295749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29313149085132875465727665 21984861813849656599295749)
                    ·
                      refine ⟨4122161590096810612367953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21984861813849656599295749 4122161590096810612367953)
                      ·
                        rfl

theorem cell23_8027881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_8027881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027881 prefixEnd_8027881 := by exact prefixLift 8027881
  have htrace : WordTrace (prefixWord ++ tailWord_8027881) baseStart_8027881 baseEnd_8027881 := by
    simpa [prefixWord, tailWord_8027881, baseEnd_8027881] using wordTrace_append hprefix tailTrace_8027881
  have hstable : (prefixWord ++ tailWord_8027881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027881).length < 2 ^ (prefixWord ++ tailWord_8027881).sum := by decide
  have hdescent : baseEnd_8027881 < baseStart_8027881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027885 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_8027885 : Nat := 118140960795 + 8027885 * 2 ^ 59
def prefixEnd_8027885 : Nat := 4983230072969 + 3 ^ 40 * 8027885 * 2
def baseEnd_8027885 : Nat := 4122163644019428596717935

theorem tailTrace_8027885 : CollatzResearch.WordTrace tailWord_8027885 prefixEnd_8027885 4122163644019428596717935 := by
  unfold tailWord_8027885
  simp only [CollatzResearch.WordTrace]
  refine ⟨292801020521351173447957109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195200680347567448965304739 292801020521351173447957109)
  ·
    refine ⟨27450095673876672510745979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292801020521351173447957109 27450095673876672510745979)
    ·
      refine ⟨41175143510815008766118969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27450095673876672510745979 41175143510815008766118969)
      ·
        refine ⟨30881357633111256574589227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41175143510815008766118969 30881357633111256574589227)
        ·
          refine ⟨46322036449666884861883841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30881357633111256574589227 46322036449666884861883841)
          ·
            refine ⟨34741527337250163646412881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46322036449666884861883841 34741527337250163646412881)
            ·
              refine ⟨26056145502937622734809661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34741527337250163646412881 26056145502937622734809661)
              ·
                refine ⟨9771054563601608525553623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26056145502937622734809661 9771054563601608525553623)
                ·
                  refine ⟨14656581845402412788330435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771054563601608525553623 14656581845402412788330435)
                  ·
                    refine ⟨21984872768103619182495653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14656581845402412788330435 21984872768103619182495653)
                    ·
                      refine ⟨4122163644019428596717935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21984872768103619182495653 4122163644019428596717935)
                      ·
                        rfl

theorem cell23_8027885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_8027885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027885 prefixEnd_8027885 := by exact prefixLift 8027885
  have htrace : WordTrace (prefixWord ++ tailWord_8027885) baseStart_8027885 baseEnd_8027885 := by
    simpa [prefixWord, tailWord_8027885, baseEnd_8027885] using wordTrace_append hprefix tailTrace_8027885
  have hstable : (prefixWord ++ tailWord_8027885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027885).length < 2 ^ (prefixWord ++ tailWord_8027885).sum := by decide
  have hdescent : baseEnd_8027885 < baseStart_8027885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027908 : List Nat := [2, 3, 2, 2, 1, 3, 2, 8]
def baseStart_8027908 : Nat := 118140960795 + 8027908 * 2 ^ 59
def prefixEnd_8027908 : Nat := 4983230072969 + 3 ^ 40 * 8027908 * 2
def baseEnd_8027908 : Nat := 152673164965721555804827

theorem tailTrace_8027908 : CollatzResearch.WordTrace tailWord_8027908 prefixEnd_8027908 152673164965721555804827 := by
  unfold tailWord_8027908
  simp only [CollatzResearch.WordTrace]
  refine ⟨146400929700133924188022189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195201239600178565584029585 146400929700133924188022189)
  ·
    refine ⟨54900348637550221570508321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146400929700133924188022189 54900348637550221570508321)
    ·
      refine ⟨41175261478162666177881241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54900348637550221570508321 41175261478162666177881241)
      ·
        refine ⟨30881446108621999633410931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41175261478162666177881241 30881446108621999633410931)
        ·
          refine ⟨46322169162932999450116397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30881446108621999633410931 46322169162932999450116397)
          ·
            refine ⟨17370813436099874793793649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46322169162932999450116397 17370813436099874793793649)
            ·
              refine ⟨13028110077074906095345237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17370813436099874793793649 13028110077074906095345237)
              ·
                refine ⟨152673164965721555804827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13028110077074906095345237 152673164965721555804827)
                ·
                  rfl

theorem cell23_8027908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 8].length) (baseStart_8027908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027908 prefixEnd_8027908 := by exact prefixLift 8027908
  have htrace : WordTrace (prefixWord ++ tailWord_8027908) baseStart_8027908 baseEnd_8027908 := by
    simpa [prefixWord, tailWord_8027908, baseEnd_8027908] using wordTrace_append hprefix tailTrace_8027908
  have hstable : (prefixWord ++ tailWord_8027908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027908).length < 2 ^ (prefixWord ++ tailWord_8027908).sum := by decide
  have hdescent : baseEnd_8027908 < baseStart_8027908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027922 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_8027922 : Nat := 118140960795 + 8027922 * 2 ^ 59
def prefixEnd_8027922 : Nat := 4983230072969 + 3 ^ 40 * 8027922 * 2
def baseEnd_8027922 : Nat := 4122182642803644951955265

theorem tailTrace_8027922 : CollatzResearch.WordTrace tailWord_8027922 prefixEnd_8027922 4122182642803644951955265 := by
  unfold tailWord_8027922
  simp only [CollatzResearch.WordTrace]
  refine ⟨73200592505554282191763505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195201580014811419178036013 73200592505554282191763505)
  ·
    refine ⟨54900444379165711643822629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73200592505554282191763505 54900444379165711643822629)
    ·
      refine ⟨10293833321093570933216743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54900444379165711643822629 10293833321093570933216743)
      ·
        refine ⟨15440749981640356399825115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293833321093570933216743 15440749981640356399825115)
        ·
          refine ⟨23161124972460534599737673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15440749981640356399825115 23161124972460534599737673)
          ·
            refine ⟨17370843729345400949803255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23161124972460534599737673 17370843729345400949803255)
            ·
              refine ⟨26056265594018101424704883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17370843729345400949803255 26056265594018101424704883)
              ·
                refine ⟨39084398391027152137057325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26056265594018101424704883 39084398391027152137057325)
                ·
                  refine ⟨14656649396635182051396497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39084398391027152137057325 14656649396635182051396497)
                  ·
                    refine ⟨10992487047476386538547373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14656649396635182051396497 10992487047476386538547373)
                    ·
                      refine ⟨4122182642803644951955265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992487047476386538547373 4122182642803644951955265)
                      ·
                        rfl

theorem cell23_8027922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_8027922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027922 prefixEnd_8027922 := by exact prefixLift 8027922
  have htrace : WordTrace (prefixWord ++ tailWord_8027922) baseStart_8027922 baseEnd_8027922 := by
    simpa [prefixWord, tailWord_8027922, baseEnd_8027922] using wordTrace_append hprefix tailTrace_8027922
  have hstable : (prefixWord ++ tailWord_8027922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027922).length < 2 ^ (prefixWord ++ tailWord_8027922).sum := by decide
  have hdescent : baseEnd_8027922 < baseStart_8027922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027951 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 6]
def baseStart_8027951 : Nat := 118140960795 + 8027951 * 2 ^ 59
def prefixEnd_8027951 : Nat := 4983230072969 + 3 ^ 40 * 8027951 * 2
def baseEnd_8027951 : Nat := 1374065844580875112830877

theorem tailTrace_8027951 : CollatzResearch.WordTrace tailWord_8027951 prefixEnd_8027951 1374065844580875112830877 := by
  unfold tailWord_8027951
  simp only [CollatzResearch.WordTrace]
  refine ⟨292803427739112066719859707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195202285159408044479906471 292803427739112066719859707)
  ·
    refine ⟨439205141608668100079789561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292803427739112066719859707 439205141608668100079789561)
    ·
      refine ⟨329403856206501075059842171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439205141608668100079789561 329403856206501075059842171)
      ·
        refine ⟨494105784309751612589763257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329403856206501075059842171 494105784309751612589763257)
        ·
          refine ⟨370579338232313709442322443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494105784309751612589763257 370579338232313709442322443)
          ·
            refine ⟨555869007348470564163483665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370579338232313709442322443 555869007348470564163483665)
            ·
              refine ⟨416901755511352923122612749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555869007348470564163483665 416901755511352923122612749)
              ·
                refine ⟨156338158316757346170979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416901755511352923122612749 156338158316757346170979781)
                ·
                  refine ⟨29313404684392002407058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156338158316757346170979781 29313404684392002407058709)
                  ·
                    refine ⟨1374065844580875112830877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29313404684392002407058709 1374065844580875112830877)
                    ·
                      rfl

theorem cell23_8027951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_8027951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027951 prefixEnd_8027951 := by exact prefixLift 8027951
  have htrace : WordTrace (prefixWord ++ tailWord_8027951) baseStart_8027951 baseEnd_8027951 := by
    simpa [prefixWord, tailWord_8027951, baseEnd_8027951] using wordTrace_append hprefix tailTrace_8027951
  have hstable : (prefixWord ++ tailWord_8027951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027951).length < 2 ^ (prefixWord ++ tailWord_8027951).sum := by decide
  have hdescent : baseEnd_8027951 < baseStart_8027951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027975 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_8027975 : Nat := 118140960795 + 8027975 * 2 ^ 59
def prefixEnd_8027975 : Nat := 4983230072969 + 3 ^ 40 * 8027975 * 2
def baseEnd_8027975 : Nat := 4122209857278333244592521

theorem tailTrace_8027975 : CollatzResearch.WordTrace tailWord_8027975 prefixEnd_8027975 4122209857278333244592521 := by
  unfold tailWord_8027975
  simp only [CollatzResearch.WordTrace]
  refine ⟨292804303091025118818733379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195202868727350079212488919 292804303091025118818733379)
  ·
    refine ⟨439206454636537678228100069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292804303091025118818733379 439206454636537678228100069)
    ·
      refine ⟨82351210244350814667768763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439206454636537678228100069 82351210244350814667768763)
      ·
        refine ⟨123526815366526222001653145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82351210244350814667768763 123526815366526222001653145)
        ·
          refine ⟨92645111524894666501239859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123526815366526222001653145 92645111524894666501239859)
          ·
            refine ⟨138967667287341999751859789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92645111524894666501239859 138967667287341999751859789)
            ·
              refine ⟨52112875232753249906947421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138967667287341999751859789 52112875232753249906947421)
              ·
                refine ⟨19542328212282468715105283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52112875232753249906947421 19542328212282468715105283)
                ·
                  refine ⟨29313492318423703072657925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19542328212282468715105283 29313492318423703072657925)
                  ·
                    refine ⟨5496279809704444326123361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29313492318423703072657925 5496279809704444326123361)
                    ·
                      refine ⟨4122209857278333244592521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496279809704444326123361 4122209857278333244592521)
                      ·
                        rfl

theorem cell23_8027975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_8027975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027975 prefixEnd_8027975 := by exact prefixLift 8027975
  have htrace : WordTrace (prefixWord ++ tailWord_8027975) baseStart_8027975 baseEnd_8027975 := by
    simpa [prefixWord, tailWord_8027975, baseEnd_8027975] using wordTrace_append hprefix tailTrace_8027975
  have hstable : (prefixWord ++ tailWord_8027975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027975).length < 2 ^ (prefixWord ++ tailWord_8027975).sum := by decide
  have hdescent : baseEnd_8027975 < baseStart_8027975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8027978 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_8027978 : Nat := 118140960795 + 8027978 * 2 ^ 59
def prefixEnd_8027978 : Nat := 4983230072969 + 3 ^ 40 * 8027978 * 2
def baseEnd_8027978 : Nat := 4122211397720296732855007

theorem tailTrace_8027978 : CollatzResearch.WordTrace tailWord_8027978 prefixEnd_8027978 4122211397720296732855007 := by
  unfold tailWord_8027978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73201103127503562582773147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195202941673342833554061725 73201103127503562582773147)
  ·
    refine ⟨109801654691255343874159721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73201103127503562582773147 109801654691255343874159721)
    ·
      refine ⟨82351241018441507905619791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109801654691255343874159721 82351241018441507905619791)
      ·
        refine ⟨123526861527662261858429687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82351241018441507905619791 123526861527662261858429687)
        ·
          refine ⟨185290292291493392787644531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123526861527662261858429687 185290292291493392787644531)
          ·
            refine ⟨277935438437240089181466797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185290292291493392787644531 277935438437240089181466797)
            ·
              refine ⟨104225789413965033443050049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277935438437240089181466797 104225789413965033443050049)
              ·
                refine ⟨78169342060473775082287537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104225789413965033443050049 78169342060473775082287537)
                ·
                  refine ⟨58627006545355331311715653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78169342060473775082287537 58627006545355331311715653)
                  ·
                    refine ⟨10992563727254124620946685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58627006545355331311715653 10992563727254124620946685)
                    ·
                      refine ⟨4122211397720296732855007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992563727254124620946685 4122211397720296732855007)
                      ·
                        rfl

theorem cell23_8027978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_8027978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8027978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8027978 prefixEnd_8027978 := by exact prefixLift 8027978
  have htrace : WordTrace (prefixWord ++ tailWord_8027978) baseStart_8027978 baseEnd_8027978 := by
    simpa [prefixWord, tailWord_8027978, baseEnd_8027978] using wordTrace_append hprefix tailTrace_8027978
  have hstable : (prefixWord ++ tailWord_8027978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8027978).length < 2 ^ (prefixWord ++ tailWord_8027978).sum := by decide
  have hdescent : baseEnd_8027978 < baseStart_8027978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8027978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028122 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_8028122 : Nat := 118140960795 + 8028122 * 2 ^ 59
def prefixEnd_8028122 : Nat := 4983230072969 + 3 ^ 40 * 8028122 * 2
def baseEnd_8028122 : Nat := 458031704326060463272705

theorem tailTrace_8028122 : CollatzResearch.WordTrace tailWord_8028122 prefixEnd_8028122 458031704326060463272705 := by
  unfold tailWord_8028122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73202416155373140731083655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195206443080995041949556413 73202416155373140731083655)
  ·
    refine ⟨109803624233059711096625483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73202416155373140731083655 109803624233059711096625483)
    ·
      refine ⟨164705436349589566644938225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109803624233059711096625483 164705436349589566644938225)
      ·
        refine ⟨123529077262192174983703669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164705436349589566644938225 123529077262192174983703669)
        ·
          refine ⟨11580850993330516404722219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123529077262192174983703669 11580850993330516404722219)
          ·
            refine ⟨17371276489995774607083329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580850993330516404722219 17371276489995774607083329)
            ·
              refine ⟨13028457367496830955312497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17371276489995774607083329 13028457367496830955312497)
              ·
                refine ⟨9771343025622623216484373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028457367496830955312497 9771343025622623216484373)
                ·
                  refine ⟨458031704326060463272705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9771343025622623216484373 458031704326060463272705)
                  ·
                    rfl

theorem cell23_8028122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_8028122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028122 prefixEnd_8028122 := by exact prefixLift 8028122
  have htrace : WordTrace (prefixWord ++ tailWord_8028122) baseStart_8028122 baseEnd_8028122 := by
    simpa [prefixWord, tailWord_8028122, baseEnd_8028122] using wordTrace_append hprefix tailTrace_8028122
  have hstable : (prefixWord ++ tailWord_8028122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028122).length < 2 ^ (prefixWord ++ tailWord_8028122).sum := by decide
  have hdescent : baseEnd_8028122 < baseStart_8028122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028128 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_8028128 : Nat := 118140960795 + 8028128 * 2 ^ 59
def prefixEnd_8028128 : Nat := 4983230072969 + 3 ^ 40 * 8028128 * 2
def baseEnd_8028128 : Nat := 4122288419818471145979317

theorem tailTrace_8028128 : CollatzResearch.WordTrace tailWord_8028128 prefixEnd_8028128 4122288419818471145979317 := by
  unfold tailWord_8028128
  simp only [CollatzResearch.WordTrace]
  refine ⟨146404941729735412974526519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195206588972980550632702025 146404941729735412974526519)
  ·
    refine ⟨219607412594603119461789779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146404941729735412974526519 219607412594603119461789779)
    ·
      refine ⟨329411118891904679192684669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219607412594603119461789779 329411118891904679192684669)
      ·
        refine ⟨123529169584464254697256751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329411118891904679192684669 123529169584464254697256751)
        ·
          refine ⟨185293754376696382045885127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123529169584464254697256751 185293754376696382045885127)
          ·
            refine ⟨277940631565044573068827691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185293754376696382045885127 277940631565044573068827691)
            ·
              refine ⟨416910947347566859603241537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277940631565044573068827691 416910947347566859603241537)
              ·
                refine ⟨312683210510675144702431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416910947347566859603241537 312683210510675144702431153)
                ·
                  refine ⟨234512407883006358526823365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312683210510675144702431153 234512407883006358526823365)
                  ·
                    refine ⟨43971076478063692223779381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234512407883006358526823365 43971076478063692223779381)
                    ·
                      refine ⟨4122288419818471145979317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43971076478063692223779381 4122288419818471145979317)
                      ·
                        rfl

theorem cell23_8028128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_8028128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028128 prefixEnd_8028128 := by exact prefixLift 8028128
  have htrace : WordTrace (prefixWord ++ tailWord_8028128) baseStart_8028128 baseEnd_8028128 := by
    simpa [prefixWord, tailWord_8028128, baseEnd_8028128] using wordTrace_append hprefix tailTrace_8028128
  have hstable : (prefixWord ++ tailWord_8028128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028128).length < 2 ^ (prefixWord ++ tailWord_8028128).sum := by decide
  have hdescent : baseEnd_8028128 < baseStart_8028128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028132 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_8028132 : Nat := 118140960795 + 8028132 * 2 ^ 59
def prefixEnd_8028132 : Nat := 4983230072969 + 3 ^ 40 * 8028132 * 2
def baseEnd_8028132 : Nat := 4122290473741089130329299

theorem tailTrace_8028132 : CollatzResearch.WordTrace tailWord_8028132 prefixEnd_8028132 4122290473741089130329299 := by
  unfold tailWord_8028132
  simp only [CollatzResearch.WordTrace]
  refine ⟨146405014675728167316099325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195206686234304223088132433 146405014675728167316099325)
  ·
    refine ⟨54901880503398062743537247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146405014675728167316099325 54901880503398062743537247)
    ·
      refine ⟨82352820755097094115305871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54901880503398062743537247 82352820755097094115305871)
      ·
        refine ⟨123529231132645641172958807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82352820755097094115305871 123529231132645641172958807)
        ·
          refine ⟨185293846698968461759438211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123529231132645641172958807 185293846698968461759438211)
          ·
            refine ⟨277940770048452692639157317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185293846698968461759438211 277940770048452692639157317)
            ·
              refine ⟨52113894384084879869841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277940770048452692639157317 52113894384084879869841997)
              ·
                refine ⟨19542710394031829951190749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52113894384084879869841997 19542710394031829951190749)
                ·
                  refine ⟨7328516397761936231696531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19542710394031829951190749 7328516397761936231696531)
                  ·
                    refine ⟨10992774596642904347544797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7328516397761936231696531 10992774596642904347544797)
                    ·
                      refine ⟨4122290473741089130329299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992774596642904347544797 4122290473741089130329299)
                      ·
                        rfl

theorem cell23_8028132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_8028132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028132 prefixEnd_8028132 := by exact prefixLift 8028132
  have htrace : WordTrace (prefixWord ++ tailWord_8028132) baseStart_8028132 baseEnd_8028132 := by
    simpa [prefixWord, tailWord_8028132, baseEnd_8028132] using wordTrace_append hprefix tailTrace_8028132
  have hstable : (prefixWord ++ tailWord_8028132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028132).length < 2 ^ (prefixWord ++ tailWord_8028132).sum := by decide
  have hdescent : baseEnd_8028132 < baseStart_8028132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028155 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4]
def baseStart_8028155 : Nat := 118140960795 + 8028155 * 2 ^ 59
def prefixEnd_8028155 : Nat := 4983230072969 + 3 ^ 40 * 8028155 * 2
def baseEnd_8028155 : Nat := 4122302283796142540341693

theorem tailTrace_8028155 : CollatzResearch.WordTrace tailWord_8028155 prefixEnd_8028155 4122302283796142540341693 := by
  unfold tailWord_8028155
  simp only [CollatzResearch.WordTrace]
  refine ⟨292810868230373009560285919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195207245486915339706857279 292810868230373009560285919)
  ·
    refine ⟨439216302345559514340428879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292810868230373009560285919 439216302345559514340428879)
    ·
      refine ⟨658824453518339271510643319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439216302345559514340428879 658824453518339271510643319)
      ·
        refine ⟨988236680277508907265964979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658824453518339271510643319 988236680277508907265964979)
        ·
          refine ⟨1482355020416263360898947469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988236680277508907265964979 1482355020416263360898947469)
          ·
            refine ⟨555883132656098760337105301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1482355020416263360898947469 555883132656098760337105301)
            ·
              refine ⟨26057021843254629390801811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 555883132656098760337105301 26057021843254629390801811)
              ·
                refine ⟨39085532764881944086202717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057021843254629390801811 39085532764881944086202717)
                ·
                  refine ⟨14657074786830729032326019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39085532764881944086202717 14657074786830729032326019)
                  ·
                    refine ⟨21985612180246093548489029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14657074786830729032326019 21985612180246093548489029)
                    ·
                      refine ⟨4122302283796142540341693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21985612180246093548489029 4122302283796142540341693)
                      ·
                        rfl

theorem cell23_8028155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_8028155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028155 prefixEnd_8028155 := by exact prefixLift 8028155
  have htrace : WordTrace (prefixWord ++ tailWord_8028155) baseStart_8028155 baseEnd_8028155 := by
    simpa [prefixWord, tailWord_8028155, baseEnd_8028155] using wordTrace_append hprefix tailTrace_8028155
  have hstable : (prefixWord ++ tailWord_8028155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028155).length < 2 ^ (prefixWord ++ tailWord_8028155).sum := by decide
  have hdescent : baseEnd_8028155 < baseStart_8028155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028165 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_8028165 : Nat := 118140960795 + 8028165 * 2 ^ 59
def prefixEnd_8028165 : Nat := 4983230072969 + 3 ^ 40 * 8028165 * 2
def baseEnd_8028165 : Nat := 1374102472867562500405549

theorem tailTrace_8028165 : CollatzResearch.WordTrace tailWord_8028165 prefixEnd_8028165 1374102472867562500405549 := by
  unfold tailWord_8028165
  simp only [CollatzResearch.WordTrace]
  refine ⟨292811232960336781268149949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195207488640224520845433299 292811232960336781268149949)
  ·
    refine ⟨109804212360126292975556231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292811232960336781268149949 109804212360126292975556231)
    ·
      refine ⟨164706318540189439463334347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109804212360126292975556231 164706318540189439463334347)
      ·
        refine ⟨247059477810284159195001521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164706318540189439463334347 247059477810284159195001521)
        ·
          refine ⟨185294608357713119396251141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247059477810284159195001521 185294608357713119396251141)
          ·
            refine ⟨34742739067071209886797089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185294608357713119396251141 34742739067071209886797089)
            ·
              refine ⟨26057054300303407415097817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34742739067071209886797089 26057054300303407415097817)
              ·
                refine ⟨19542790725227555561323363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26057054300303407415097817 19542790725227555561323363)
                ·
                  refine ⟨29314186087841333341985045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19542790725227555561323363 29314186087841333341985045)
                  ·
                    refine ⟨1374102472867562500405549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29314186087841333341985045 1374102472867562500405549)
                    ·
                      rfl

theorem cell23_8028165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_8028165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028165 prefixEnd_8028165 := by exact prefixLift 8028165
  have htrace : WordTrace (prefixWord ++ tailWord_8028165) baseStart_8028165 baseEnd_8028165 := by
    simpa [prefixWord, tailWord_8028165, baseEnd_8028165] using wordTrace_append hprefix tailTrace_8028165
  have hstable : (prefixWord ++ tailWord_8028165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028165).length < 2 ^ (prefixWord ++ tailWord_8028165).sum := by decide
  have hdescent : baseEnd_8028165 < baseStart_8028165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028172 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_8028172 : Nat := 118140960795 + 8028172 * 2 ^ 59
def prefixEnd_8028172 : Nat := 4983230072969 + 3 ^ 40 * 8028172 * 2
def baseEnd_8028172 : Nat := 4122311012967268973829115

theorem tailTrace_8028172 : CollatzResearch.WordTrace tailWord_8028172 prefixEnd_8028172 4122311012967268973829115 := by
  unfold tailWord_8028172
  simp only [CollatzResearch.WordTrace]
  refine ⟨146405744135655710731827385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195207658847540947642436513 146405744135655710731827385)
  ·
    refine ⟨109804308101741783048870539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146405744135655710731827385 109804308101741783048870539)
    ·
      refine ⟨164706462152612674573305809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109804308101741783048870539 164706462152612674573305809)
      ·
        refine ⟨123529846614459505929979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164706462152612674573305809 123529846614459505929979357)
        ·
          refine ⟨46323692480422314723742259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123529846614459505929979357 46323692480422314723742259)
          ·
            refine ⟨69485538720633472085613389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46323692480422314723742259 69485538720633472085613389)
            ·
              refine ⟨26057077020237552032105021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69485538720633472085613389 26057077020237552032105021)
              ·
                refine ⟨9771403882589082012039383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26057077020237552032105021 9771403882589082012039383)
                ·
                  refine ⟨14657105823883623018059075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771403882589082012039383 14657105823883623018059075)
                  ·
                    refine ⟨21985658735825434527088613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14657105823883623018059075 21985658735825434527088613)
                    ·
                      refine ⟨4122311012967268973829115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21985658735825434527088613 4122311012967268973829115)
                      ·
                        rfl

theorem cell23_8028172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_8028172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028172 prefixEnd_8028172 := by exact prefixLift 8028172
  have htrace : WordTrace (prefixWord ++ tailWord_8028172) baseStart_8028172 baseEnd_8028172 := by
    simpa [prefixWord, tailWord_8028172, baseEnd_8028172] using wordTrace_append hprefix tailTrace_8028172
  have hstable : (prefixWord ++ tailWord_8028172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028172).length < 2 ^ (prefixWord ++ tailWord_8028172).sum := by decide
  have hdescent : baseEnd_8028172 < baseStart_8028172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028173 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 6]
def baseStart_8028173 : Nat := 118140960795 + 8028173 * 2 ^ 59
def prefixEnd_8028173 : Nat := 4983230072969 + 3 ^ 40 * 8028173 * 2
def baseEnd_8028173 : Nat := 458034614049769274435179

theorem tailTrace_8028173 : CollatzResearch.WordTrace tailWord_8028173 prefixEnd_8028173 458034614049769274435179 := by
  unfold tailWord_8028173
  simp only [CollatzResearch.WordTrace]
  refine ⟨292811524744307798634441173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195207683162871865756294115 292811524744307798634441173)
  ·
    refine ⟨6862770111194714030494715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 292811524744307798634441173 6862770111194714030494715)
    ·
      refine ⟨10294155166792071045742073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862770111194714030494715 10294155166792071045742073)
      ·
        refine ⟨7720616375094053284306555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10294155166792071045742073 7720616375094053284306555)
        ·
          refine ⟨11580924562641079926459833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7720616375094053284306555 11580924562641079926459833)
          ·
            refine ⟨8685693421980809944844875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580924562641079926459833 8685693421980809944844875)
            ·
              refine ⟨13028540132971214917267313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685693421980809944844875 13028540132971214917267313)
              ·
                refine ⟨9771405099728411187950485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028540132971214917267313 9771405099728411187950485)
                ·
                  refine ⟨458034614049769274435179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9771405099728411187950485 458034614049769274435179)
                  ·
                    rfl

theorem cell23_8028173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_8028173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028173 prefixEnd_8028173 := by exact prefixLift 8028173
  have htrace : WordTrace (prefixWord ++ tailWord_8028173) baseStart_8028173 baseEnd_8028173 := by
    simpa [prefixWord, tailWord_8028173, baseEnd_8028173] using wordTrace_append hprefix tailTrace_8028173
  have hstable : (prefixWord ++ tailWord_8028173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028173).length < 2 ^ (prefixWord ++ tailWord_8028173).sum := by decide
  have hdescent : baseEnd_8028173 < baseStart_8028173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028202 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_8028202 : Nat := 118140960795 + 8028202 * 2 ^ 59
def prefixEnd_8028202 : Nat := 4983230072969 + 3 ^ 40 * 8028202 * 2
def baseEnd_8028202 : Nat := 4122326417386903856453977

theorem tailTrace_8028202 : CollatzResearch.WordTrace tailWord_8028202 prefixEnd_8028202 4122326417386903856453977 := by
  unfold tailWord_8028202
  simp only [CollatzResearch.WordTrace]
  refine ⟨73203145615300684146811715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195208388307468491058164573 73203145615300684146811715)
  ·
    refine ⟨109804718422951026220217573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73203145615300684146811715 109804718422951026220217573)
    ·
      refine ⟨20588384704303317416290795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109804718422951026220217573 20588384704303317416290795)
      ·
        refine ⟨30882577056454976124436193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588384704303317416290795 30882577056454976124436193)
        ·
          refine ⟨23161932792341232093327145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30882577056454976124436193 23161932792341232093327145)
          ·
            refine ⟨17371449594255924069995359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23161932792341232093327145 17371449594255924069995359)
            ·
              refine ⟨26057174391383886104993039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371449594255924069995359 26057174391383886104993039)
              ·
                refine ⟨39085761587075829157489559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057174391383886104993039 39085761587075829157489559)
                ·
                  refine ⟨58628642380613743736234339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39085761587075829157489559 58628642380613743736234339)
                  ·
                    refine ⟨87942963570920615604351509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58628642380613743736234339 87942963570920615604351509)
                    ·
                      refine ⟨4122326417386903856453977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87942963570920615604351509 4122326417386903856453977)
                      ·
                        rfl

theorem cell23_8028202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_8028202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028202 prefixEnd_8028202 := by exact prefixLift 8028202
  have htrace : WordTrace (prefixWord ++ tailWord_8028202) baseStart_8028202 baseEnd_8028202 := by
    simpa [prefixWord, tailWord_8028202, baseEnd_8028202] using wordTrace_append hprefix tailTrace_8028202
  have hstable : (prefixWord ++ tailWord_8028202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028202).length < 2 ^ (prefixWord ++ tailWord_8028202).sum := by decide
  have hdescent : baseEnd_8028202 < baseStart_8028202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028206 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_8028206 : Nat := 118140960795 + 8028206 * 2 ^ 59
def prefixEnd_8028206 : Nat := 4983230072969 + 3 ^ 40 * 8028206 * 2
def baseEnd_8028206 : Nat := 4122328471309521840803959

theorem tailTrace_8028206 : CollatzResearch.WordTrace tailWord_8028206 prefixEnd_8028206 4122328471309521840803959 := by
  unfold tailWord_8028206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601591044148530658799059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195208485568792163513594981 36601591044148530658799059)
  ·
    refine ⟨54902386566222795988198589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36601591044148530658799059 54902386566222795988198589)
    ·
      refine ⟨20588394962333548495574471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54902386566222795988198589 20588394962333548495574471)
      ·
        refine ⟨30882592443500322743361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588394962333548495574471 30882592443500322743361707)
        ·
          refine ⟨46323888665250484115042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30882592443500322743361707 46323888665250484115042561)
          ·
            refine ⟨34742916498937863086281921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46323888665250484115042561 34742916498937863086281921)
            ·
              refine ⟨26057187374203397314711441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34742916498937863086281921 26057187374203397314711441)
              ·
                refine ⟨19542890530652547986033581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26057187374203397314711441 19542890530652547986033581)
                ·
                  refine ⟨7328583948994705494762593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19542890530652547986033581 7328583948994705494762593)
                  ·
                    refine ⟨5496437961746029121071945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7328583948994705494762593 5496437961746029121071945)
                    ·
                      refine ⟨4122328471309521840803959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496437961746029121071945 4122328471309521840803959)
                      ·
                        rfl

theorem cell23_8028206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_8028206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028206 prefixEnd_8028206 := by exact prefixLift 8028206
  have htrace : WordTrace (prefixWord ++ tailWord_8028206) baseStart_8028206 baseEnd_8028206 := by
    simpa [prefixWord, tailWord_8028206, baseEnd_8028206] using wordTrace_append hprefix tailTrace_8028206
  have hstable : (prefixWord ++ tailWord_8028206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028206).length < 2 ^ (prefixWord ++ tailWord_8028206).sum := by decide
  have hdescent : baseEnd_8028206 < baseStart_8028206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028209 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_8028209 : Nat := 118140960795 + 8028209 * 2 ^ 59
def prefixEnd_8028209 : Nat := 4983230072969 + 3 ^ 40 * 8028209 * 2
def baseEnd_8028209 : Nat := 4122330011751485329066445

theorem tailTrace_8028209 : CollatzResearch.WordTrace tailWord_8028209 prefixEnd_8028209 4122330011751485329066445 := by
  unfold tailWord_8028209
  simp only [CollatzResearch.WordTrace]
  refine ⟨292812837772177376782751681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195208558514784917855167787 292812837772177376782751681)
  ·
    refine ⟨219609628329133032587063761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292812837772177376782751681 219609628329133032587063761)
    ·
      refine ⟨164707221246849774440297821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219609628329133032587063761 164707221246849774440297821)
      ·
        refine ⟨61765207967568665415111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164707221246849774440297821 61765207967568665415111683)
        ·
          refine ⟨92647811951352998122667525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61765207967568665415111683 92647811951352998122667525)
          ·
            refine ⟨17371464740878687148000161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92647811951352998122667525 17371464740878687148000161)
            ·
              refine ⟨13028598555659015361000121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17371464740878687148000161 13028598555659015361000121)
              ·
                refine ⟨9771448916744261520750091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028598555659015361000121 9771448916744261520750091)
                ·
                  refine ⟨14657173375116392281125137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771448916744261520750091 14657173375116392281125137)
                  ·
                    refine ⟨10992880031337294210843853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14657173375116392281125137 10992880031337294210843853)
                    ·
                      refine ⟨4122330011751485329066445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992880031337294210843853 4122330011751485329066445)
                      ·
                        rfl

theorem cell23_8028209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_8028209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028209 prefixEnd_8028209 := by exact prefixLift 8028209
  have htrace : WordTrace (prefixWord ++ tailWord_8028209) baseStart_8028209 baseEnd_8028209 := by
    simpa [prefixWord, tailWord_8028209, baseEnd_8028209] using wordTrace_append hprefix tailTrace_8028209
  have hstable : (prefixWord ++ tailWord_8028209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028209).length < 2 ^ (prefixWord ++ tailWord_8028209).sum := by decide
  have hdescent : baseEnd_8028209 < baseStart_8028209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028256 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3]
def baseStart_8028256 : Nat := 118140960795 + 8028256 * 2 ^ 59
def prefixEnd_8028256 : Nat := 4983230072969 + 3 ^ 40 * 8028256 * 2
def baseEnd_8028256 : Nat := 4122354145342246645178729

theorem tailTrace_8028256 : CollatzResearch.WordTrace tailWord_8028256 prefixEnd_8028256 4122354145342246645178729 := by
  unfold tailWord_8028256
  simp only [CollatzResearch.WordTrace]
  refine ⟨146407276001503551904856311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195209701335338069206475081 146407276001503551904856311)
  ·
    refine ⟨219610914002255327857284467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146407276001503551904856311 219610914002255327857284467)
    ·
      refine ⟨329416371003382991785926701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219610914002255327857284467 329416371003382991785926701)
      ·
        refine ⟨123531139126268621919722513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329416371003382991785926701 123531139126268621919722513)
        ·
          refine ⟨92648354344701466439791885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123531139126268621919722513 92648354344701466439791885)
          ·
            refine ⟨34743132879263049914921957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92648354344701466439791885 34743132879263049914921957)
            ·
              refine ⟨6514337414861821859047867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34743132879263049914921957 6514337414861821859047867)
              ·
                refine ⟨9771506122292732788571801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514337414861821859047867 9771506122292732788571801)
                ·
                  refine ⟨7328629591719549591428851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9771506122292732788571801 7328629591719549591428851)
                  ·
                    refine ⟨10992944387579324387143277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7328629591719549591428851 10992944387579324387143277)
                    ·
                      refine ⟨4122354145342246645178729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10992944387579324387143277 4122354145342246645178729)
                      ·
                        rfl

theorem cell23_8028256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_8028256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028256 prefixEnd_8028256 := by exact prefixLift 8028256
  have htrace : WordTrace (prefixWord ++ tailWord_8028256) baseStart_8028256 baseEnd_8028256 := by
    simpa [prefixWord, tailWord_8028256, baseEnd_8028256] using wordTrace_append hprefix tailTrace_8028256
  have hstable : (prefixWord ++ tailWord_8028256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028256).length < 2 ^ (prefixWord ++ tailWord_8028256).sum := by decide
  have hdescent : baseEnd_8028256 < baseStart_8028256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028265 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_8028265 : Nat := 118140960795 + 8028265 * 2 ^ 59
def prefixEnd_8028265 : Nat := 4983230072969 + 3 ^ 40 * 8028265 * 2
def baseEnd_8028265 : Nat := 4122358766668137109966187

theorem tailTrace_8028265 : CollatzResearch.WordTrace tailWord_8028265 prefixEnd_8028265 4122358766668137109966187 := by
  unfold tailWord_8028265
  simp only [CollatzResearch.WordTrace]
  refine ⟨292814880259974498346790249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195209920173316332231193499 292814880259974498346790249)
  ·
    refine ⟨219611160194980873760092687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292814880259974498346790249 219611160194980873760092687)
    ·
      refine ⟨329416740292471310640139031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219611160194980873760092687 329416740292471310640139031)
      ·
        refine ⟨494125110438706965960208547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329416740292471310640139031 494125110438706965960208547)
        ·
          refine ⟨741187665658060448940312821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494125110438706965960208547 741187665658060448940312821)
          ·
            refine ⟨69486343655443167088154327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 741187665658060448940312821 69486343655443167088154327)
            ·
              refine ⟨104229515483164750632231491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69486343655443167088154327 104229515483164750632231491)
              ·
                refine ⟨156344273224747125948347237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104229515483164750632231491 156344273224747125948347237)
                ·
                  refine ⟨29314551229640086115315107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156344273224747125948347237 29314551229640086115315107)
                  ·
                    refine ⟨43971826844460129172972661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29314551229640086115315107 43971826844460129172972661)
                    ·
                      refine ⟨4122358766668137109966187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43971826844460129172972661 4122358766668137109966187)
                      ·
                        rfl

theorem cell23_8028265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_8028265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028265 prefixEnd_8028265 := by exact prefixLift 8028265
  have htrace : WordTrace (prefixWord ++ tailWord_8028265) baseStart_8028265 baseEnd_8028265 := by
    simpa [prefixWord, tailWord_8028265, baseEnd_8028265] using wordTrace_append hprefix tailTrace_8028265
  have hstable : (prefixWord ++ tailWord_8028265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028265).length < 2 ^ (prefixWord ++ tailWord_8028265).sum := by decide
  have hdescent : baseEnd_8028265 < baseStart_8028265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028266 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_8028266 : Nat := 118140960795 + 8028266 * 2 ^ 59
def prefixEnd_8028266 : Nat := 4983230072969 + 3 ^ 40 * 8028266 * 2
def baseEnd_8028266 : Nat := 4122359280148791606053683

theorem tailTrace_8028266 : CollatzResearch.WordTrace tailWord_8028266 prefixEnd_8028266 4122359280148791606053683 := by
  unfold tailWord_8028266
  simp only [CollatzResearch.WordTrace]
  refine ⟨73203729183242718879394163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195209944488647250345051101 73203729183242718879394163)
  ·
    refine ⟨109805593774864078319091245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73203729183242718879394163 109805593774864078319091245)
    ·
      refine ⟨41177097665574029369659217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109805593774864078319091245 41177097665574029369659217)
      ·
        refine ⟨30882823249180522027244413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41177097665574029369659217 30882823249180522027244413)
        ·
          refine ⟨11581058718442695760216655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30882823249180522027244413 11581058718442695760216655)
          ·
            refine ⟨17371588077664043640324983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581058718442695760216655 17371588077664043640324983)
            ·
              refine ⟨26057382116496065460487475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371588077664043640324983 26057382116496065460487475)
              ·
                refine ⟨39086073174744098190731213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057382116496065460487475 39086073174744098190731213)
                ·
                  refine ⟨14657277440529036821524205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39086073174744098190731213 14657277440529036821524205)
                  ·
                    refine ⟨5496479040198388808071577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14657277440529036821524205 5496479040198388808071577)
                    ·
                      refine ⟨4122359280148791606053683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496479040198388808071577 4122359280148791606053683)
                      ·
                        rfl

theorem cell23_8028266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_8028266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028266 prefixEnd_8028266 := by exact prefixLift 8028266
  have htrace : WordTrace (prefixWord ++ tailWord_8028266) baseStart_8028266 baseEnd_8028266 := by
    simpa [prefixWord, tailWord_8028266, baseEnd_8028266] using wordTrace_append hprefix tailTrace_8028266
  have hstable : (prefixWord ++ tailWord_8028266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028266).length < 2 ^ (prefixWord ++ tailWord_8028266).sum := by decide
  have hdescent : baseEnd_8028266 < baseStart_8028266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028279 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_8028279 : Nat := 118140960795 + 8028279 * 2 ^ 59
def prefixEnd_8028279 : Nat := 4983230072969 + 3 ^ 40 * 8028279 * 2
def baseEnd_8028279 : Nat := 4122365955397300055191123

theorem tailTrace_8028279 : CollatzResearch.WordTrace tailWord_8028279 prefixEnd_8028279 4122365955397300055191123 := by
  unfold tailWord_8028279
  simp only [CollatzResearch.WordTrace]
  refine ⟨292815390881923778737799891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195210260587949185825199927 292815390881923778737799891)
  ·
    refine ⟨439223086322885668106699837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292815390881923778737799891 439223086322885668106699837)
    ·
      refine ⟨164708657371082125540012439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439223086322885668106699837 164708657371082125540012439)
      ·
        refine ⟨247062986056623188310018659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164708657371082125540012439 247062986056623188310018659)
        ·
          refine ⟨370594479084934782465027989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247062986056623188310018659 370594479084934782465027989)
          ·
            refine ⟨17371616207106317928048187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 370594479084934782465027989 17371616207106317928048187)
            ·
              refine ⟨26057424310659476892072281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371616207106317928048187 26057424310659476892072281)
              ·
                refine ⟨19543068232994607669054211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26057424310659476892072281 19543068232994607669054211)
                ·
                  refine ⟨29314602349491911503581317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19543068232994607669054211 29314602349491911503581317)
                  ·
                    refine ⟨5496487940529733406921497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29314602349491911503581317 5496487940529733406921497)
                    ·
                      refine ⟨4122365955397300055191123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496487940529733406921497 4122365955397300055191123)
                      ·
                        rfl

theorem cell23_8028279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_8028279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028279 prefixEnd_8028279 := by exact prefixLift 8028279
  have htrace : WordTrace (prefixWord ++ tailWord_8028279) baseStart_8028279 baseEnd_8028279 := by
    simpa [prefixWord, tailWord_8028279, baseEnd_8028279] using wordTrace_append hprefix tailTrace_8028279
  have hstable : (prefixWord ++ tailWord_8028279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028279).length < 2 ^ (prefixWord ++ tailWord_8028279).sum := by decide
  have hdescent : baseEnd_8028279 < baseStart_8028279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028292 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_8028292 : Nat := 118140960795 + 8028292 * 2 ^ 59
def prefixEnd_8028292 : Nat := 4983230072969 + 3 ^ 40 * 8028292 * 2
def baseEnd_8028292 : Nat := 4122372630645808504328563

theorem tailTrace_8028292 : CollatzResearch.WordTrace tailWord_8028292 prefixEnd_8028292 4122372630645808504328563 := by
  unfold tailWord_8028292
  simp only [CollatzResearch.WordTrace]
  refine ⟨146407932515438340979011565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195210576687251121305348753 146407932515438340979011565)
  ·
    refine ⟨54902974693289377867129337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146407932515438340979011565 54902974693289377867129337)
    ·
      refine ⟨41177231019967033400347003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54902974693289377867129337 41177231019967033400347003)
      ·
        refine ⟨61765846529950550100520505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41177231019967033400347003 61765846529950550100520505)
        ·
          refine ⟨46324384897462912575390379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61765846529950550100520505 46324384897462912575390379)
          ·
            refine ⟨69486577346194368863085569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46324384897462912575390379 69486577346194368863085569)
            ·
              refine ⟨52114933009645776647314177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69486577346194368863085569 52114933009645776647314177)
              ·
                refine ⟨39086199757234332485485633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52114933009645776647314177 39086199757234332485485633)
                ·
                  refine ⟨29314649817925749364114225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39086199757234332485485633 29314649817925749364114225)
                  ·
                    refine ⟨21985987363444312023085669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29314649817925749364114225 21985987363444312023085669)
                    ·
                      refine ⟨4122372630645808504328563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21985987363444312023085669 4122372630645808504328563)
                      ·
                        rfl

theorem cell23_8028292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_8028292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028292 prefixEnd_8028292 := by exact prefixLift 8028292
  have htrace : WordTrace (prefixWord ++ tailWord_8028292) baseStart_8028292 baseEnd_8028292 := by
    simpa [prefixWord, tailWord_8028292, baseEnd_8028292] using wordTrace_append hprefix tailTrace_8028292
  have hstable : (prefixWord ++ tailWord_8028292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028292).length < 2 ^ (prefixWord ++ tailWord_8028292).sum := by decide
  have hdescent : baseEnd_8028292 < baseStart_8028292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028295 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_8028295 : Nat := 118140960795 + 8028295 * 2 ^ 59
def prefixEnd_8028295 : Nat := 4983230072969 + 3 ^ 40 * 8028295 * 2
def baseEnd_8028295 : Nat := 4122374171087771992591049

theorem tailTrace_8028295 : CollatzResearch.WordTrace tailWord_8028295 prefixEnd_8028295 4122374171087771992591049 := by
  unfold tailWord_8028295
  simp only [CollatzResearch.WordTrace]
  refine ⟨292815974449865813470382339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195210649633243875646921559 292815974449865813470382339)
  ·
    refine ⟨439223961674798720205573509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292815974449865813470382339 439223961674798720205573509)
    ·
      refine ⟨82354492814024760038545033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439223961674798720205573509 82354492814024760038545033)
      ·
        refine ⟨61765869610518570028908775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82354492814024760038545033 61765869610518570028908775)
        ·
          refine ⟨92648804415777855043363163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61765869610518570028908775 92648804415777855043363163)
          ·
            refine ⟨138973206623666782565044745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92648804415777855043363163 138973206623666782565044745)
            ·
              refine ⟨104229904967750086923783559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138973206623666782565044745 104229904967750086923783559)
              ·
                refine ⟨156344857451625130385675339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104229904967750086923783559 156344857451625130385675339)
                ·
                  refine ⟨234517286177437695578513009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156344857451625130385675339 234517286177437695578513009)
                  ·
                    refine ⟨175887964633078271683884757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234517286177437695578513009 175887964633078271683884757)
                    ·
                      refine ⟨4122374171087771992591049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175887964633078271683884757 4122374171087771992591049)
                      ·
                        rfl

theorem cell23_8028295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_8028295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028295 prefixEnd_8028295 := by exact prefixLift 8028295
  have htrace : WordTrace (prefixWord ++ tailWord_8028295) baseStart_8028295 baseEnd_8028295 := by
    simpa [prefixWord, tailWord_8028295, baseEnd_8028295] using wordTrace_append hprefix tailTrace_8028295
  have hstable : (prefixWord ++ tailWord_8028295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028295).length < 2 ^ (prefixWord ++ tailWord_8028295).sum := by decide
  have hdescent : baseEnd_8028295 < baseStart_8028295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028334 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_8028334 : Nat := 118140960795 + 8028334 * 2 ^ 59
def prefixEnd_8028334 : Nat := 4983230072969 + 3 ^ 40 * 8028334 * 2
def baseEnd_8028334 : Nat := 4122394196833297340003371

theorem tailTrace_8028334 : CollatzResearch.WordTrace tailWord_8028334 prefixEnd_8028334 4122394196833297340003371 := by
  unfold tailWord_8028334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602174612090565391381507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195211597931149682087368037 36602174612090565391381507)
  ·
    refine ⟨54903261918135848087072261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36602174612090565391381507 54903261918135848087072261)
    ·
      refine ⟨10294361609650471516326049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54903261918135848087072261 10294361609650471516326049)
      ·
        refine ⟨7720771207237853637244537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10294361609650471516326049 7720771207237853637244537)
        ·
          refine ⟨5790578405428390227933403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7720771207237853637244537 5790578405428390227933403)
          ·
            refine ⟨8685867608142585341900105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790578405428390227933403 8685867608142585341900105)
            ·
              refine ⟨6514400706106939006425079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685867608142585341900105 6514400706106939006425079)
              ·
                refine ⟨9771601059160408509637619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514400706106939006425079 9771601059160408509637619)
                ·
                  refine ⟨14657401588740612764456429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771601059160408509637619 14657401588740612764456429)
                  ·
                    refine ⟨5496525595777729786671161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14657401588740612764456429 5496525595777729786671161)
                    ·
                      refine ⟨4122394196833297340003371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496525595777729786671161 4122394196833297340003371)
                      ·
                        rfl

theorem cell23_8028334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_8028334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028334 prefixEnd_8028334 := by exact prefixLift 8028334
  have htrace : WordTrace (prefixWord ++ tailWord_8028334) baseStart_8028334 baseEnd_8028334 := by
    simpa [prefixWord, tailWord_8028334, baseEnd_8028334] using wordTrace_append hprefix tailTrace_8028334
  have hstable : (prefixWord ++ tailWord_8028334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028334).length < 2 ^ (prefixWord ++ tailWord_8028334).sum := by decide
  have hdescent : baseEnd_8028334 < baseStart_8028334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028369 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_8028369 : Nat := 118140960795 + 8028369 * 2 ^ 59
def prefixEnd_8028369 : Nat := 4983230072969 + 3 ^ 40 * 8028369 * 2
def baseEnd_8028369 : Nat := 4122412168656204703065709

theorem tailTrace_8028369 : CollatzResearch.WordTrace tailWord_8028369 prefixEnd_8028369 4122412168656204703065709 := by
  unfold tailWord_8028369
  simp only [CollatzResearch.WordTrace]
  refine ⟨292818673451597724108576161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195212448967731816072384107 292818673451597724108576161)
  ·
    refine ⟨219614005088698293081432121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292818673451597724108576161 219614005088698293081432121)
    ·
      refine ⟨164710503816523719811074091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219614005088698293081432121 164710503816523719811074091)
      ·
        refine ⟨247065755724785579716611137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164710503816523719811074091 247065755724785579716611137)
        ·
          refine ⟨185299316793589184787458353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247065755724785579716611137 185299316793589184787458353)
          ·
            refine ⟨138974487595191888590593765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185299316793589184787458353 138974487595191888590593765)
            ·
              refine ⟨26057716424098479110736331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138974487595191888590593765 26057716424098479110736331)
              ·
                refine ⟨39086574636147718666104497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057716424098479110736331 39086574636147718666104497)
                ·
                  refine ⟨29314930977110788999578373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39086574636147718666104497 29314930977110788999578373)
                  ·
                    refine ⟨5496549558208272937420945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29314930977110788999578373 5496549558208272937420945)
                    ·
                      refine ⟨4122412168656204703065709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496549558208272937420945 4122412168656204703065709)
                      ·
                        rfl

theorem cell23_8028369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_8028369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028369 prefixEnd_8028369 := by exact prefixLift 8028369
  have htrace : WordTrace (prefixWord ++ tailWord_8028369) baseStart_8028369 baseEnd_8028369 := by
    simpa [prefixWord, tailWord_8028369, baseEnd_8028369] using wordTrace_append hprefix tailTrace_8028369
  have hstable : (prefixWord ++ tailWord_8028369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028369).length < 2 ^ (prefixWord ++ tailWord_8028369).sum := by decide
  have hdescent : baseEnd_8028369 < baseStart_8028369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028389 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_8028389 : Nat := 118140960795 + 8028389 * 2 ^ 59
def prefixEnd_8028389 : Nat := 4983230072969 + 3 ^ 40 * 8028389 * 2
def baseEnd_8028389 : Nat := 4122422438269294624815617

theorem tailTrace_8028389 : CollatzResearch.WordTrace tailWord_8028389 prefixEnd_8028389 4122422438269294624815617 := by
  unfold tailWord_8028389
  simp only [CollatzResearch.WordTrace]
  refine ⟨292819402911525267524304221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195212935274350178349536147 292819402911525267524304221)
  ·
    refine ⟨109807276091821975321614083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292819402911525267524304221 109807276091821975321614083)
    ·
      refine ⟨164710914137732962982421125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109807276091821975321614083 164710914137732962982421125)
      ·
        refine ⟨30883296400824930559203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164710914137732962982421125 30883296400824930559203961)
        ·
          refine ⟨23162472300618697919402971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30883296400824930559203961 23162472300618697919402971)
          ·
            refine ⟨34743708450928046879104457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162472300618697919402971 34743708450928046879104457)
            ·
              refine ⟨26057781338196035159328343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34743708450928046879104457 26057781338196035159328343)
              ·
                refine ⟨39086672007294052738992515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057781338196035159328343 39086672007294052738992515)
                ·
                  refine ⟨58630008010941079108488773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39086672007294052738992515 58630008010941079108488773)
                  ·
                    refine ⟨10993126502051452332841645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58630008010941079108488773 10993126502051452332841645)
                    ·
                      refine ⟨4122422438269294624815617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10993126502051452332841645 4122422438269294624815617)
                      ·
                        rfl

theorem cell23_8028389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_8028389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028389 prefixEnd_8028389 := by exact prefixLift 8028389
  have htrace : WordTrace (prefixWord ++ tailWord_8028389) baseStart_8028389 baseEnd_8028389 := by
    simpa [prefixWord, tailWord_8028389, baseEnd_8028389] using wordTrace_append hprefix tailTrace_8028389
  have hstable : (prefixWord ++ tailWord_8028389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028389).length < 2 ^ (prefixWord ++ tailWord_8028389).sum := by decide
  have hdescent : baseEnd_8028389 < baseStart_8028389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028392 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 8]
def baseStart_8028392 : Nat := 118140960795 + 8028392 * 2 ^ 59
def prefixEnd_8028392 : Nat := 4983230072969 + 3 ^ 40 * 8028392 * 2
def baseEnd_8028392 : Nat := 458047108745695345897567

theorem tailTrace_8028392 : CollatzResearch.WordTrace tailWord_8028392 prefixEnd_8028392 458047108745695345897567 := by
  unfold tailWord_8028392
  simp only [CollatzResearch.WordTrace]
  refine ⟨146409756165257199518331715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195213008220342932691108953 146409756165257199518331715)
  ·
    refine ⟨219614634247885799277497573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146409756165257199518331715 219614634247885799277497573)
    ·
      refine ⟨41177743921478587364530795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219614634247885799277497573 41177743921478587364530795)
      ·
        refine ⟨61766615882217881046796193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41177743921478587364530795 61766615882217881046796193)
        ·
          refine ⟨46324961911663410785097145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61766615882217881046796193 46324961911663410785097145)
          ·
            refine ⟨34743721433747558088822859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46324961911663410785097145 34743721433747558088822859)
            ·
              refine ⟨52115582150621337133234289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34743721433747558088822859 52115582150621337133234289)
              ·
                refine ⟨39086686612966002849925717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52115582150621337133234289 39086686612966002849925717)
                ·
                  refine ⟨458047108745695345897567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39086686612966002849925717 458047108745695345897567)
                  ·
                    rfl

theorem cell23_8028392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_8028392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028392 prefixEnd_8028392 := by exact prefixLift 8028392
  have htrace : WordTrace (prefixWord ++ tailWord_8028392) baseStart_8028392 baseEnd_8028392 := by
    simpa [prefixWord, tailWord_8028392, baseEnd_8028392] using wordTrace_append hprefix tailTrace_8028392
  have hstable : (prefixWord ++ tailWord_8028392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028392).length < 2 ^ (prefixWord ++ tailWord_8028392).sum := by decide
  have hdescent : baseEnd_8028392 < baseStart_8028392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028439 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 3, 5]
def baseStart_8028439 : Nat := 118140960795 + 8028439 * 2 ^ 59
def prefixEnd_8028439 : Nat := 4983230072969 + 3 ^ 40 * 8028439 * 2
def baseEnd_8028439 : Nat := 1374149370767339809730129

theorem tailTrace_8028439 : CollatzResearch.WordTrace tailWord_8028439 prefixEnd_8028439 1374149370767339809730129 := by
  unfold tailWord_8028439
  simp only [CollatzResearch.WordTrace]
  refine ⟨292821226561344126063624371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195214151040896084042416247 292821226561344126063624371)
  ·
    refine ⟨439231839842016189095436557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292821226561344126063624371 439231839842016189095436557)
    ·
      refine ⟨164711939940756070910788709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439231839842016189095436557 164711939940756070910788709)
      ·
        refine ⟨30883488738891763295772883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164711939940756070910788709 30883488738891763295772883)
        ·
          refine ⟨46325233108337644943659325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30883488738891763295772883 46325233108337644943659325)
          ·
            refine ⟨17371962415626616853872247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46325233108337644943659325 17371962415626616853872247)
            ·
              refine ⟨26057943623439925280808371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371962415626616853872247 26057943623439925280808371)
              ·
                refine ⟨39086915435159887921212557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057943623439925280808371 39086915435159887921212557)
                ·
                  refine ⟨14657593288184957970454709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39086915435159887921212557 14657593288184957970454709)
                  ·
                    refine ⟨1374149370767339809730129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14657593288184957970454709 1374149370767339809730129)
                    ·
                      rfl

theorem cell23_8028439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_8028439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028439 prefixEnd_8028439 := by exact prefixLift 8028439
  have htrace : WordTrace (prefixWord ++ tailWord_8028439) baseStart_8028439 baseEnd_8028439 := by
    simpa [prefixWord, tailWord_8028439, baseEnd_8028439] using wordTrace_append hprefix tailTrace_8028439
  have hstable : (prefixWord ++ tailWord_8028439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028439).length < 2 ^ (prefixWord ++ tailWord_8028439).sum := by decide
  have hdescent : baseEnd_8028439 < baseStart_8028439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028472 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_8028472 : Nat := 118140960795 + 8028472 * 2 ^ 59
def prefixEnd_8028472 : Nat := 4983230072969 + 3 ^ 40 * 8028472 * 2
def baseEnd_8028472 : Nat := 4122465057163617800077735

theorem tailTrace_8028472 : CollatzResearch.WordTrace tailWord_8028472 prefixEnd_8028472 4122465057163617800077735 := by
  unfold tailWord_8028472
  simp only [CollatzResearch.WordTrace]
  refine ⟨146411215085112286349787835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195214953446816381799717113 146411215085112286349787835)
  ·
    refine ⟨219616822627668429524681753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146411215085112286349787835 219616822627668429524681753)
    ·
      refine ⟨164712616970751322143511315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219616822627668429524681753 164712616970751322143511315)
      ·
        refine ⟨247068925456126983215266973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164712616970751322143511315 247068925456126983215266973)
        ·
          refine ⟨92650847046047618705725115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247068925456126983215266973 92650847046047618705725115)
          ·
            refine ⟨138976270569071428058587673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92650847046047618705725115 138976270569071428058587673)
            ·
              refine ⟨104232202926803571043940755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138976270569071428058587673 104232202926803571043940755)
              ·
                refine ⟨156348304390205356565911133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104232202926803571043940755 156348304390205356565911133)
                ·
                  refine ⟨58630614146327008712216675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156348304390205356565911133 58630614146327008712216675)
                  ·
                    refine ⟨87945921219490513068325013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58630614146327008712216675 87945921219490513068325013)
                    ·
                      refine ⟨4122465057163617800077735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87945921219490513068325013 4122465057163617800077735)
                      ·
                        rfl

theorem cell23_8028472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_8028472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028472 prefixEnd_8028472 := by exact prefixLift 8028472
  have htrace : WordTrace (prefixWord ++ tailWord_8028472) baseStart_8028472 baseEnd_8028472 := by
    simpa [prefixWord, tailWord_8028472, baseEnd_8028472] using wordTrace_append hprefix tailTrace_8028472
  have hstable : (prefixWord ++ tailWord_8028472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028472).length < 2 ^ (prefixWord ++ tailWord_8028472).sum := by decide
  have hdescent : baseEnd_8028472 < baseStart_8028472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028479 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_8028479 : Nat := 118140960795 + 8028479 * 2 ^ 59
def prefixEnd_8028479 : Nat := 4983230072969 + 3 ^ 40 * 8028479 * 2
def baseEnd_8028479 : Nat := 4122468651528199272690203

theorem tailTrace_8028479 : CollatzResearch.WordTrace tailWord_8028479 prefixEnd_8028479 4122468651528199272690203 := by
  unfold tailWord_8028479
  simp only [CollatzResearch.WordTrace]
  refine ⟨292822685481199212895080491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195215123654132808596720327 292822685481199212895080491)
  ·
    refine ⟨439234028221798819342620737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292822685481199212895080491 439234028221798819342620737)
    ·
      refine ⟨329425521166349114506965553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439234028221798819342620737 329425521166349114506965553)
      ·
        refine ⟨247069140874761835880224165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329425521166349114506965553 247069140874761835880224165)
        ·
          refine ⟨46325463914017844227542031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247069140874761835880224165 46325463914017844227542031)
          ·
            refine ⟨69488195871026766341313047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46325463914017844227542031 69488195871026766341313047)
            ·
              refine ⟨104232293806540149511969571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69488195871026766341313047 104232293806540149511969571)
              ·
                refine ⟨156348440709810224267954357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104232293806540149511969571 156348440709810224267954357)
                ·
                  refine ⟨14657666316544708525120721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156348440709810224267954357 14657666316544708525120721)
                  ·
                    refine ⟨10993249737408531393840541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14657666316544708525120721 10993249737408531393840541)
                    ·
                      refine ⟨4122468651528199272690203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10993249737408531393840541 4122468651528199272690203)
                      ·
                        rfl

theorem cell23_8028479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_8028479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028479 prefixEnd_8028479 := by exact prefixLift 8028479
  have htrace : WordTrace (prefixWord ++ tailWord_8028479) baseStart_8028479 baseEnd_8028479 := by
    simpa [prefixWord, tailWord_8028479, baseEnd_8028479] using wordTrace_append hprefix tailTrace_8028479
  have hstable : (prefixWord ++ tailWord_8028479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028479).length < 2 ^ (prefixWord ++ tailWord_8028479).sum := by decide
  have hdescent : baseEnd_8028479 < baseStart_8028479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028553 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 1, 3, 2]
def baseStart_8028553 : Nat := 118140960795 + 8028553 * 2 ^ 59
def prefixEnd_8028553 : Nat := 4983230072969 + 3 ^ 40 * 8028553 * 2
def baseEnd_8028553 : Nat := 4122506649096631983164863

theorem tailTrace_8028553 : CollatzResearch.WordTrace tailWord_8028553 prefixEnd_8028553 4122506649096631983164863 := by
  unfold tailWord_8028553
  simp only [CollatzResearch.WordTrace]
  refine ⟨292825384482931123533274313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195216922988620749022182875 292825384482931123533274313)
  ·
    refine ⟨219619038362198342649955735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292825384482931123533274313 219619038362198342649955735)
    ·
      refine ⟨329428557543297513974933603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219619038362198342649955735 329428557543297513974933603)
      ·
        refine ⟨494142836314946270962400405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329428557543297513974933603 494142836314946270962400405)
        ·
          refine ⟨23162945452263106451362519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 494142836314946270962400405 23162945452263106451362519)
          ·
            refine ⟨34744418178394659677043779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162945452263106451362519 34744418178394659677043779)
            ·
              refine ⟨52116627267591989515565669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34744418178394659677043779 52116627267591989515565669)
              ·
                refine ⟨9771867612673498034168563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52116627267591989515565669 9771867612673498034168563)
                ·
                  refine ⟨14657801419010247051252845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771867612673498034168563 14657801419010247051252845)
                  ·
                    refine ⟨5496675532128842644219817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14657801419010247051252845 5496675532128842644219817)
                    ·
                      refine ⟨4122506649096631983164863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496675532128842644219817 4122506649096631983164863)
                      ·
                        rfl

theorem cell23_8028553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3, 2].length) (baseStart_8028553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028553 prefixEnd_8028553 := by exact prefixLift 8028553
  have htrace : WordTrace (prefixWord ++ tailWord_8028553) baseStart_8028553 baseEnd_8028553 := by
    simpa [prefixWord, tailWord_8028553, baseEnd_8028553] using wordTrace_append hprefix tailTrace_8028553
  have hstable : (prefixWord ++ tailWord_8028553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028553).length < 2 ^ (prefixWord ++ tailWord_8028553).sum := by decide
  have hdescent : baseEnd_8028553 < baseStart_8028553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028569 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_8028569 : Nat := 118140960795 + 8028569 * 2 ^ 59
def prefixEnd_8028569 : Nat := 4983230072969 + 3 ^ 40 * 8028569 * 2
def baseEnd_8028569 : Nat := 4122514864787103920564789

theorem tailTrace_8028569 : CollatzResearch.WordTrace tailWord_8028569 prefixEnd_8028569 4122514864787103920564789 := by
  unfold tailWord_8028569
  simp only [CollatzResearch.WordTrace]
  refine ⟨292825968050873158265856761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195217312033915438843904507 292825968050873158265856761)
  ·
    refine ⟨219619476038154868699392571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292825968050873158265856761 219619476038154868699392571)
    ·
      refine ⟨329429214057232303049088857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219619476038154868699392571 329429214057232303049088857)
      ·
        refine ⟨247071910542924227286816643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329429214057232303049088857 247071910542924227286816643)
        ·
          refine ⟨370607865814386340930224965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247071910542924227286816643 370607865814386340930224965)
          ·
            refine ⟨69488974840197438924417181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370607865814386340930224965 69488974840197438924417181)
            ·
              refine ⟨26058365565074039596656443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69488974840197438924417181 26058365565074039596656443)
              ·
                refine ⟨39087548347611059394984665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26058365565074039596656443 39087548347611059394984665)
                ·
                  refine ⟨29315661260708294546238499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39087548347611059394984665 29315661260708294546238499)
                  ·
                    refine ⟨43973491891062441819357749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29315661260708294546238499 43973491891062441819357749)
                    ·
                      refine ⟨4122514864787103920564789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43973491891062441819357749 4122514864787103920564789)
                      ·
                        rfl

theorem cell23_8028569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_8028569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028569 prefixEnd_8028569 := by exact prefixLift 8028569
  have htrace : WordTrace (prefixWord ++ tailWord_8028569) baseStart_8028569 baseEnd_8028569 := by
    simpa [prefixWord, tailWord_8028569, baseEnd_8028569] using wordTrace_append hprefix tailTrace_8028569
  have hstable : (prefixWord ++ tailWord_8028569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028569).length < 2 ^ (prefixWord ++ tailWord_8028569).sum := by decide
  have hdescent : baseEnd_8028569 < baseStart_8028569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028673 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_8028673 : Nat := 118140960795 + 8028673 * 2 ^ 59
def prefixEnd_8028673 : Nat := 4983230072969 + 3 ^ 40 * 8028673 * 2
def baseEnd_8028673 : Nat := 4122568266775171513664311

theorem tailTrace_8028673 : CollatzResearch.WordTrace tailWord_8028673 prefixEnd_8028673 4122568266775171513664311 := by
  unfold tailWord_8028673
  simp only [CollatzResearch.WordTrace]
  refine ⟨292829761242496384027642673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195219840828330922685095115 292829761242496384027642673)
  ·
    refine ⟨219622320931872288020732005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292829761242496384027642673 219622320931872288020732005)
    ·
      refine ⟨41179185174726054003887251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219622320931872288020732005 41179185174726054003887251)
      ·
        refine ⟨61768777762089081005830877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41179185174726054003887251 61768777762089081005830877)
        ·
          refine ⟨23163291660783405377186579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61768777762089081005830877 23163291660783405377186579)
          ·
            refine ⟨34744937491175108065779869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23163291660783405377186579 34744937491175108065779869)
            ·
              refine ⟨13029351559190665524667451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34744937491175108065779869 13029351559190665524667451)
              ·
                refine ⟨19544027338785998287001177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029351559190665524667451 19544027338785998287001177)
                ·
                  refine ⟨14658020504089498715250883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19544027338785998287001177 14658020504089498715250883)
                  ·
                    refine ⟨21987030756134248072876325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14658020504089498715250883 21987030756134248072876325)
                    ·
                      refine ⟨4122568266775171513664311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21987030756134248072876325 4122568266775171513664311)
                      ·
                        rfl

theorem cell23_8028673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_8028673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028673 prefixEnd_8028673 := by exact prefixLift 8028673
  have htrace : WordTrace (prefixWord ++ tailWord_8028673) baseStart_8028673 baseEnd_8028673 := by
    simpa [prefixWord, tailWord_8028673, baseEnd_8028673] using wordTrace_append hprefix tailTrace_8028673
  have hstable : (prefixWord ++ tailWord_8028673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028673).length < 2 ^ (prefixWord ++ tailWord_8028673).sum := by decide
  have hdescent : baseEnd_8028673 < baseStart_8028673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028686 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_8028686 : Nat := 118140960795 + 8028686 * 2 ^ 59
def prefixEnd_8028686 : Nat := 4983230072969 + 3 ^ 40 * 8028686 * 2
def baseEnd_8028686 : Nat := 4122574942023679962801751

theorem tailTrace_8028686 : CollatzResearch.WordTrace tailWord_8028686 prefixEnd_8028686 4122574942023679962801751 := by
  unfold tailWord_8028686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603779423931160905983239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195220156927632858165243941 36603779423931160905983239)
  ·
    refine ⟨54905669135896741358974859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36603779423931160905983239 54905669135896741358974859)
    ·
      refine ⟨82358503703845112038462289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54905669135896741358974859 82358503703845112038462289)
      ·
        refine ⟨61768877777883834028846717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82358503703845112038462289 61768877777883834028846717)
        ·
          refine ⟨23163329166706437760817519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61768877777883834028846717 23163329166706437760817519)
          ·
            refine ⟨34744993750059656641226279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23163329166706437760817519 34744993750059656641226279)
            ·
              refine ⟨52117490625089484961839419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34744993750059656641226279 52117490625089484961839419)
              ·
                refine ⟨78176235937634227442759129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52117490625089484961839419 78176235937634227442759129)
                ·
                  refine ⟨58632176953225670582069347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78176235937634227442759129 58632176953225670582069347)
                  ·
                    refine ⟨87948265429838505873104021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58632176953225670582069347 87948265429838505873104021)
                    ·
                      refine ⟨4122574942023679962801751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87948265429838505873104021 4122574942023679962801751)
                      ·
                        rfl

theorem cell23_8028686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_8028686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028686 prefixEnd_8028686 := by exact prefixLift 8028686
  have htrace : WordTrace (prefixWord ++ tailWord_8028686) baseStart_8028686 baseEnd_8028686 := by
    simpa [prefixWord, tailWord_8028686, baseEnd_8028686] using wordTrace_append hprefix tailTrace_8028686
  have hstable : (prefixWord ++ tailWord_8028686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028686).length < 2 ^ (prefixWord ++ tailWord_8028686).sum := by decide
  have hdescent : baseEnd_8028686 < baseStart_8028686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028696 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 8]
def baseStart_8028696 : Nat := 118140960795 + 8028696 * 2 ^ 59
def prefixEnd_8028696 : Nat := 4983230072969 + 3 ^ 40 * 8028696 * 2
def baseEnd_8028696 : Nat := 458064452981136102630745

theorem tailTrace_8028696 : CollatzResearch.WordTrace tailWord_8028696 prefixEnd_8028696 458064452981136102630745 := by
  unfold tailWord_8028696
  simp only [CollatzResearch.WordTrace]
  refine ⟨146415300060706529477864971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195220400080942039303819961 146415300060706529477864971)
  ·
    refine ⟨219622950091059794216797457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146415300060706529477864971 219622950091059794216797457)
    ·
      refine ⟨164717212568294845662598093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219622950091059794216797457 164717212568294845662598093)
      ·
        refine ⟨61768954713110567123474285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164717212568294845662598093 61768954713110567123474285)
        ·
          refine ⟨23163358017416462671302857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61768954713110567123474285 23163358017416462671302857)
          ·
            refine ⟨17372518513062347003477143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23163358017416462671302857 17372518513062347003477143)
            ·
              refine ⟨26058777769593520505215715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17372518513062347003477143 26058777769593520505215715)
              ·
                refine ⟨39088166654390280757823573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26058777769593520505215715 39088166654390280757823573)
                ·
                  refine ⟨458064452981136102630745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39088166654390280757823573 458064452981136102630745)
                  ·
                    rfl

theorem cell23_8028696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_8028696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028696 prefixEnd_8028696 := by exact prefixLift 8028696
  have htrace : WordTrace (prefixWord ++ tailWord_8028696) baseStart_8028696 baseEnd_8028696 := by
    simpa [prefixWord, tailWord_8028696, baseEnd_8028696] using wordTrace_append hprefix tailTrace_8028696
  have hstable : (prefixWord ++ tailWord_8028696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028696).length < 2 ^ (prefixWord ++ tailWord_8028696).sum := by decide
  have hdescent : baseEnd_8028696 < baseStart_8028696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028700 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_8028700 : Nat := 118140960795 + 8028700 * 2 ^ 59
def prefixEnd_8028700 : Nat := 4983230072969 + 3 ^ 40 * 8028700 * 2
def baseEnd_8028700 : Nat := 1374194043584280969342229

theorem tailTrace_8028700 : CollatzResearch.WordTrace tailWord_8028700 prefixEnd_8028700 1374194043584280969342229 := by
  unfold tailWord_8028700
  simp only [CollatzResearch.WordTrace]
  refine ⟨146415373006699283819437777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195220497342265711759250369 146415373006699283819437777)
  ·
    refine ⟨109811529755024462864578333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146415373006699283819437777 109811529755024462864578333)
    ·
      refine ⟨41179323658134173574216875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109811529755024462864578333 41179323658134173574216875)
      ·
        refine ⟨61768985487201260361325313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41179323658134173574216875 61768985487201260361325313)
        ·
          refine ⟨46326739115400945270993985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61768985487201260361325313 46326739115400945270993985)
          ·
            refine ⟨34745054336550708953245489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46326739115400945270993985 34745054336550708953245489)
            ·
              refine ⟨26058790752413031714934117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34745054336550708953245489 26058790752413031714934117)
              ·
                refine ⟨4886023266077443446550147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26058790752413031714934117 4886023266077443446550147)
                ·
                  refine ⟨7329034899116165169825221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886023266077443446550147 7329034899116165169825221)
                  ·
                    refine ⟨1374194043584280969342229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7329034899116165169825221 1374194043584280969342229)
                    ·
                      rfl

theorem cell23_8028700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_8028700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028700 prefixEnd_8028700 := by exact prefixLift 8028700
  have htrace : WordTrace (prefixWord ++ tailWord_8028700) baseStart_8028700 baseEnd_8028700 := by
    simpa [prefixWord, tailWord_8028700, baseEnd_8028700] using wordTrace_append hprefix tailTrace_8028700
  have hstable : (prefixWord ++ tailWord_8028700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028700).length < 2 ^ (prefixWord ++ tailWord_8028700).sum := by decide
  have hdescent : baseEnd_8028700 < baseStart_8028700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028723 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 3]
def baseStart_8028723 : Nat := 118140960795 + 8028723 * 2 ^ 59
def prefixEnd_8028723 : Nat := 4983230072969 + 3 ^ 40 * 8028723 * 2
def baseEnd_8028723 : Nat := 4122593940807896318039081

theorem tailTrace_8028723 : CollatzResearch.WordTrace tailWord_8028723 prefixEnd_8028723 4122593940807896318039081 := by
  unfold tailWord_8028723
  simp only [CollatzResearch.WordTrace]
  refine ⟨292831584892315242566962823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195221056594876828377975215 292831584892315242566962823)
  ·
    refine ⟨439247377338472863850444235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292831584892315242566962823 439247377338472863850444235)
    ·
      refine ⟨658871066007709295775666353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439247377338472863850444235 658871066007709295775666353)
      ·
        refine ⟨494153299505781971831749765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658871066007709295775666353 494153299505781971831749765)
        ·
          refine ⟨92653743657334119718453081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494153299505781971831749765 92653743657334119718453081)
          ·
            refine ⟨69490307743000589788839811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92653743657334119718453081 69490307743000589788839811)
            ·
              refine ⟨104235461614500884683259717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69490307743000589788839811 104235461614500884683259717)
              ·
                refine ⟨19544149052718915878111197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104235461614500884683259717 19544149052718915878111197)
                ·
                  refine ⟨7329055894769593454291699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19544149052718915878111197 7329055894769593454291699)
                  ·
                    refine ⟨10993583842154390181437549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329055894769593454291699 10993583842154390181437549)
                    ·
                      refine ⟨4122593940807896318039081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10993583842154390181437549 4122593940807896318039081)
                      ·
                        rfl

theorem cell23_8028723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_8028723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028723 prefixEnd_8028723 := by exact prefixLift 8028723
  have htrace : WordTrace (prefixWord ++ tailWord_8028723) baseStart_8028723 baseEnd_8028723 := by
    simpa [prefixWord, tailWord_8028723, baseEnd_8028723] using wordTrace_append hprefix tailTrace_8028723
  have hstable : (prefixWord ++ tailWord_8028723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028723).length < 2 ^ (prefixWord ++ tailWord_8028723).sum := by decide
  have hdescent : baseEnd_8028723 < baseStart_8028723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028743 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 1, 5]
def baseStart_8028743 : Nat := 118140960795 + 8028743 * 2 ^ 59
def prefixEnd_8028743 : Nat := 4983230072969 + 3 ^ 40 * 8028743 * 2
def baseEnd_8028743 : Nat := 1374201403473662079929663

theorem tailTrace_8028743 : CollatzResearch.WordTrace tailWord_8028743 prefixEnd_8028743 1374201403473662079929663 := by
  unfold tailWord_8028743
  simp only [CollatzResearch.WordTrace]
  refine ⟨292832314352242785982690883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195221542901495190655127255 292832314352242785982690883)
  ·
    refine ⟨439248471528364178974036325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292832314352242785982690883 439248471528364178974036325)
    ·
      refine ⟨82359088411568283557631811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439248471528364178974036325 82359088411568283557631811)
      ·
        refine ⟨123538632617352425336447717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82359088411568283557631811 123538632617352425336447717)
        ·
          refine ⟨23163493615753579750583947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123538632617352425336447717 23163493615753579750583947)
          ·
            refine ⟨34745240423630369625875921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23163493615753579750583947 34745240423630369625875921)
            ·
              refine ⟨26058930317722777219406941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34745240423630369625875921 26058930317722777219406941)
              ·
                refine ⟨9772098869146041457277603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26058930317722777219406941 9772098869146041457277603)
                ·
                  refine ⟨14658148303719062185916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772098869146041457277603 14658148303719062185916405)
                  ·
                    refine ⟨1374201403473662079929663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14658148303719062185916405 1374201403473662079929663)
                    ·
                      rfl

theorem cell23_8028743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_8028743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028743 prefixEnd_8028743 := by exact prefixLift 8028743
  have htrace : WordTrace (prefixWord ++ tailWord_8028743) baseStart_8028743 baseEnd_8028743 := by
    simpa [prefixWord, tailWord_8028743, baseEnd_8028743] using wordTrace_append hprefix tailTrace_8028743
  have hstable : (prefixWord ++ tailWord_8028743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028743).length < 2 ^ (prefixWord ++ tailWord_8028743).sum := by decide
  have hdescent : baseEnd_8028743 < baseStart_8028743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028780 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_8028780 : Nat := 118140960795 + 8028780 * 2 ^ 59
def prefixEnd_8028780 : Nat := 4983230072969 + 3 ^ 40 * 8028780 * 2
def baseEnd_8028780 : Nat := 4122623209205202595026319

theorem tailTrace_8028780 : CollatzResearch.WordTrace tailWord_8028780 prefixEnd_8028780 4122623209205202595026319 := by
  unfold tailWord_8028780
  simp only [CollatzResearch.WordTrace]
  refine ⟨146416831926554370650893897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195222442568739160867858529 146416831926554370650893897)
  ·
    refine ⟨109812623944915777988170423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146416831926554370650893897 109812623944915777988170423)
    ·
      refine ⟨164718935917373666982255635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109812623944915777988170423 164718935917373666982255635)
      ·
        refine ⟨247078403876060500473383453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164718935917373666982255635 247078403876060500473383453)
        ·
          refine ⟨92654401453522687677518795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247078403876060500473383453 92654401453522687677518795)
          ·
            refine ⟨138981602180284031516278193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92654401453522687677518795 138981602180284031516278193)
            ·
              refine ⟨104236201635213023637208645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138981602180284031516278193 104236201635213023637208645)
              ·
                refine ⟨19544287806602441931976621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104236201635213023637208645 19544287806602441931976621)
                ·
                  refine ⟨7329107927475915724491233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19544287806602441931976621 7329107927475915724491233)
                  ·
                    refine ⟨5496830945606936793368425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7329107927475915724491233 5496830945606936793368425)
                    ·
                      refine ⟨4122623209205202595026319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496830945606936793368425 4122623209205202595026319)
                      ·
                        rfl

theorem cell23_8028780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_8028780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028780 prefixEnd_8028780 := by exact prefixLift 8028780
  have htrace : WordTrace (prefixWord ++ tailWord_8028780) baseStart_8028780 baseEnd_8028780 := by
    simpa [prefixWord, tailWord_8028780, baseEnd_8028780] using wordTrace_append hprefix tailTrace_8028780
  have hstable : (prefixWord ++ tailWord_8028780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028780).length < 2 ^ (prefixWord ++ tailWord_8028780).sum := by decide
  have hdescent : baseEnd_8028780 < baseStart_8028780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028790 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_8028790 : Nat := 118140960795 + 8028790 * 2 ^ 59
def prefixEnd_8028790 : Nat := 4983230072969 + 3 ^ 40 * 8028790 * 2
def baseEnd_8028790 : Nat := 1374209448003915851967091

theorem tailTrace_8028790 : CollatzResearch.WordTrace tailWord_8028790 prefixEnd_8028790 1374209448003915851967091 := by
  unfold tailWord_8028790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302126786442032063103239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195222685722048342006434549 18302126786442032063103239)
  ·
    refine ⟨27453190179663048094654859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18302126786442032063103239 27453190179663048094654859)
    ·
      refine ⟨41179785269494572141982289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27453190179663048094654859 41179785269494572141982289)
      ·
        refine ⟨30884838952120929106486717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41179785269494572141982289 30884838952120929106486717)
        ·
          refine ⟨11581814607045348414932519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30884838952120929106486717 11581814607045348414932519)
          ·
            refine ⟨17372721910568022622398779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581814607045348414932519 17372721910568022622398779)
            ·
              refine ⟨26059082865852033933598169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17372721910568022622398779 26059082865852033933598169)
              ·
                refine ⟨19544312149389025450198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26059082865852033933598169 19544312149389025450198627)
                ·
                  refine ⟨29316468224083538175297941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19544312149389025450198627 29316468224083538175297941)
                  ·
                    refine ⟨1374209448003915851967091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29316468224083538175297941 1374209448003915851967091)
                    ·
                      rfl

theorem cell23_8028790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_8028790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028790 prefixEnd_8028790 := by exact prefixLift 8028790
  have htrace : WordTrace (prefixWord ++ tailWord_8028790) baseStart_8028790 baseEnd_8028790 := by
    simpa [prefixWord, tailWord_8028790, baseEnd_8028790] using wordTrace_append hprefix tailTrace_8028790
  have hstable : (prefixWord ++ tailWord_8028790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028790).length < 2 ^ (prefixWord ++ tailWord_8028790).sum := by decide
  have hdescent : baseEnd_8028790 < baseStart_8028790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028793 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_8028793 : Nat := 118140960795 + 8028793 * 2 ^ 59
def prefixEnd_8028793 : Nat := 4983230072969 + 3 ^ 40 * 8028793 * 2
def baseEnd_8028793 : Nat := 4122629884453711044163759

theorem tailTrace_8028793 : CollatzResearch.WordTrace tailWord_8028793 prefixEnd_8028793 4122629884453711044163759 := by
  unfold tailWord_8028793
  simp only [CollatzResearch.WordTrace]
  refine ⟨292834138002061644522011033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195222758668041096348007355 292834138002061644522011033)
  ·
    refine ⟨219625603501546233391508275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292834138002061644522011033 219625603501546233391508275)
    ·
      refine ⟨329438405252319350087262413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219625603501546233391508275 329438405252319350087262413)
      ·
        refine ⟨123539401969619756282723405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329438405252319350087262413 123539401969619756282723405)
        ·
          refine ⟨46327275738607408606021277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123539401969619756282723405 46327275738607408606021277)
          ·
            refine ⟨17372728401977778227257979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46327275738607408606021277 17372728401977778227257979)
            ·
              refine ⟨26059092602966667340886969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17372728401977778227257979 26059092602966667340886969)
              ·
                refine ⟨19544319452225000505665227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26059092602966667340886969 19544319452225000505665227)
                ·
                  refine ⟨29316479178337500758497841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19544319452225000505665227 29316479178337500758497841)
                  ·
                    refine ⟨21987359383753125568873381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29316479178337500758497841 21987359383753125568873381)
                    ·
                      refine ⟨4122629884453711044163759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21987359383753125568873381 4122629884453711044163759)
                      ·
                        rfl

theorem cell23_8028793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_8028793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028793 prefixEnd_8028793 := by exact prefixLift 8028793
  have htrace : WordTrace (prefixWord ++ tailWord_8028793) baseStart_8028793 baseEnd_8028793 := by
    simpa [prefixWord, tailWord_8028793, baseEnd_8028793] using wordTrace_append hprefix tailTrace_8028793
  have hstable : (prefixWord ++ tailWord_8028793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028793).length < 2 ^ (prefixWord ++ tailWord_8028793).sum := by decide
  have hdescent : baseEnd_8028793 < baseStart_8028793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028797 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_8028797 : Nat := 118140960795 + 8028797 * 2 ^ 59
def prefixEnd_8028797 : Nat := 4983230072969 + 3 ^ 40 * 8028797 * 2
def baseEnd_8028797 : Nat := 4122631938376329028513741

theorem tailTrace_8028797 : CollatzResearch.WordTrace tailWord_8028797 prefixEnd_8028797 4122631938376329028513741 := by
  unfold tailWord_8028797
  simp only [CollatzResearch.WordTrace]
  refine ⟨292834283894047153205156645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195222855929364768803437763 292834283894047153205156645)
  ·
    refine ⟨54906428230133841225966871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292834283894047153205156645 54906428230133841225966871)
    ·
      refine ⟨82359642345200761838950307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54906428230133841225966871 82359642345200761838950307)
      ·
        refine ⟨123539463517801142758425461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82359642345200761838950307 123539463517801142758425461)
        ·
          refine ⟨11581824704793857133602387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123539463517801142758425461 11581824704793857133602387)
          ·
            refine ⟨17372737057190785700403581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581824704793857133602387 17372737057190785700403581)
            ·
              refine ⟨6514776396446544637651343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17372737057190785700403581 6514776396446544637651343)
              ·
                refine ⟨9772164594669816956477015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514776396446544637651343 9772164594669816956477015)
                ·
                  refine ⟨14658246892004725434715523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772164594669816956477015 14658246892004725434715523)
                  ·
                    refine ⟨21987370338007088152073285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14658246892004725434715523 21987370338007088152073285)
                    ·
                      refine ⟨4122631938376329028513741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21987370338007088152073285 4122631938376329028513741)
                      ·
                        rfl

theorem cell23_8028797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_8028797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028797 prefixEnd_8028797 := by exact prefixLift 8028797
  have htrace : WordTrace (prefixWord ++ tailWord_8028797) baseStart_8028797 baseEnd_8028797 := by
    simpa [prefixWord, tailWord_8028797, baseEnd_8028797] using wordTrace_append hprefix tailTrace_8028797
  have hstable : (prefixWord ++ tailWord_8028797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028797).length < 2 ^ (prefixWord ++ tailWord_8028797).sum := by decide
  have hdescent : baseEnd_8028797 < baseStart_8028797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028814 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_8028814 : Nat := 118140960795 + 8028814 * 2 ^ 59
def prefixEnd_8028814 : Nat := 4983230072969 + 3 ^ 40 * 8028814 * 2
def baseEnd_8028814 : Nat := 4122640667547455462001163

theorem tailTrace_8028814 : CollatzResearch.WordTrace tailWord_8028814 prefixEnd_8028814 4122640667547455462001163 := by
  unfold tailWord_8028814
  simp only [CollatzResearch.WordTrace]
  refine ⟨36604362991873195638565687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195223269289990376739016997 36604362991873195638565687)
  ·
    refine ⟨54906544487809793457848531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36604362991873195638565687 54906544487809793457848531)
    ·
      refine ⟨82359816731714690186772797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54906544487809793457848531 82359816731714690186772797)
      ·
        refine ⟨30884931274393008820039799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82359816731714690186772797 30884931274393008820039799)
        ·
          refine ⟨46327396911589513230059699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30884931274393008820039799 46327396911589513230059699)
          ·
            refine ⟨69491095367384269845089549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46327396911589513230059699 69491095367384269845089549)
            ·
              refine ⟨26059160762769101191908581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69491095367384269845089549 26059160762769101191908581)
              ·
                refine ⟨4886092643019206473482859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26059160762769101191908581 4886092643019206473482859)
                ·
                  refine ⟨7329138964528809710224289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886092643019206473482859 7329138964528809710224289)
                  ·
                    refine ⟨5496854223396607282668217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7329138964528809710224289 5496854223396607282668217)
                    ·
                      refine ⟨4122640667547455462001163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496854223396607282668217 4122640667547455462001163)
                      ·
                        rfl

theorem cell23_8028814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_8028814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028814 prefixEnd_8028814 := by exact prefixLift 8028814
  have htrace : WordTrace (prefixWord ++ tailWord_8028814) baseStart_8028814 baseEnd_8028814 := by
    simpa [prefixWord, tailWord_8028814, baseEnd_8028814] using wordTrace_append hprefix tailTrace_8028814
  have hstable : (prefixWord ++ tailWord_8028814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028814).length < 2 ^ (prefixWord ++ tailWord_8028814).sum := by decide
  have hdescent : baseEnd_8028814 < baseStart_8028814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028820 : List Nat := [2, 4, 2, 2, 1, 3, 1, 8]
def baseStart_8028820 : Nat := 118140960795 + 8028820 * 2 ^ 59
def prefixEnd_8028820 : Nat := 4983230072969 + 3 ^ 40 * 8028820 * 2
def baseEnd_8028820 : Nat := 152690509201162312538005

theorem tailTrace_8028820 : CollatzResearch.WordTrace tailWord_8028820 prefixEnd_8028820 152690509201162312538005 := by
  unfold tailWord_8028820
  simp only [CollatzResearch.WordTrace]
  refine ⟨146417561386481914066621957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195223415181975885422162609 146417561386481914066621957)
  ·
    refine ⟨27453292759965358887491617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146417561386481914066621957 27453292759965358887491617)
    ·
      refine ⟨20589969569974019165618713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27453292759965358887491617 20589969569974019165618713)
      ·
        refine ⟨15442477177480514374214035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20589969569974019165618713 15442477177480514374214035)
        ·
          refine ⟨23163715766220771561321053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15442477177480514374214035 23163715766220771561321053)
          ·
            refine ⟨8686393412332789335495395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23163715766220771561321053 8686393412332789335495395)
            ·
              refine ⟨13029590118499184003243093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686393412332789335495395 13029590118499184003243093)
              ·
                refine ⟨152690509201162312538005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13029590118499184003243093 152690509201162312538005)
                ·
                  rfl

theorem cell23_8028820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 8].length) (baseStart_8028820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028820 prefixEnd_8028820 := by exact prefixLift 8028820
  have htrace : WordTrace (prefixWord ++ tailWord_8028820) baseStart_8028820 baseEnd_8028820 := by
    simpa [prefixWord, tailWord_8028820, baseEnd_8028820] using wordTrace_append hprefix tailTrace_8028820
  have hstable : (prefixWord ++ tailWord_8028820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028820).length < 2 ^ (prefixWord ++ tailWord_8028820).sum := by decide
  have hdescent : baseEnd_8028820 < baseStart_8028820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028887 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_8028887 : Nat := 118140960795 + 8028887 * 2 ^ 59
def prefixEnd_8028887 : Nat := 4983230072969 + 3 ^ 40 * 8028887 * 2
def baseEnd_8028887 : Nat := 4122678151635233676388327

theorem tailTrace_8028887 : CollatzResearch.WordTrace tailWord_8028887 prefixEnd_8028887 4122678151635233676388327 := by
  unfold tailWord_8028887
  simp only [CollatzResearch.WordTrace]
  refine ⟨292837566463721098575932915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195225044309147399050621943 292837566463721098575932915)
  ·
    refine ⟨439256349695581647863899373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292837566463721098575932915 439256349695581647863899373)
    ·
      refine ⟨164721131135843117948962265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439256349695581647863899373 164721131135843117948962265)
      ·
        refine ⟨123540848351882338461721699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164721131135843117948962265 123540848351882338461721699)
        ·
          refine ⟨185311272527823507692582549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123540848351882338461721699 185311272527823507692582549)
          ·
            refine ⟨8686465899741726923089807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185311272527823507692582549 8686465899741726923089807)
            ·
              refine ⟨13029698849612590384634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686465899741726923089807 13029698849612590384634711)
              ·
                refine ⟨19544548274418885576952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029698849612590384634711 19544548274418885576952067)
                ·
                  refine ⟨29316822411628328365428101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19544548274418885576952067 29316822411628328365428101)
                  ·
                    refine ⟨5496904202180311568517769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29316822411628328365428101 5496904202180311568517769)
                    ·
                      refine ⟨4122678151635233676388327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5496904202180311568517769 4122678151635233676388327)
                      ·
                        rfl

theorem cell23_8028887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_8028887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028887 prefixEnd_8028887 := by exact prefixLift 8028887
  have htrace : WordTrace (prefixWord ++ tailWord_8028887) baseStart_8028887 baseEnd_8028887 := by
    simpa [prefixWord, tailWord_8028887, baseEnd_8028887] using wordTrace_append hprefix tailTrace_8028887
  have hstable : (prefixWord ++ tailWord_8028887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028887).length < 2 ^ (prefixWord ++ tailWord_8028887).sum := by decide
  have hdescent : baseEnd_8028887 < baseStart_8028887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028943 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_8028943 : Nat := 118140960795 + 8028943 * 2 ^ 59
def prefixEnd_8028943 : Nat := 4983230072969 + 3 ^ 40 * 8028943 * 2
def baseEnd_8028943 : Nat := 4122706906551885457288069

theorem tailTrace_8028943 : CollatzResearch.WordTrace tailWord_8028943 prefixEnd_8028943 4122706906551885457288069 := by
  unfold tailWord_8028943
  simp only [CollatzResearch.WordTrace]
  refine ⟨292839608951518220139971483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195226405967678813426647655 292839608951518220139971483)
  ·
    refine ⟨439259413427277330209957225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292839608951518220139971483 439259413427277330209957225)
    ·
      refine ⟨329444560070457997657467919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439259413427277330209957225 329444560070457997657467919)
      ·
        refine ⟨494166840105686996486201879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329444560070457997657467919 494166840105686996486201879)
        ·
          refine ⟨741250260158530494729302819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494166840105686996486201879 741250260158530494729302819)
          ·
            refine ⟨1111875390237795742093954229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741250260158530494729302819 1111875390237795742093954229)
            ·
              refine ⟨104238317834793350821308209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1111875390237795742093954229 104238317834793350821308209)
              ·
                refine ⟨78178738376095013115981157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104238317834793350821308209 78178738376095013115981157)
                ·
                  refine ⟨14658513445517814959246467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78178738376095013115981157 14658513445517814959246467)
                  ·
                    refine ⟨21987770168276722438869701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14658513445517814959246467 21987770168276722438869701)
                    ·
                      refine ⟨4122706906551885457288069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21987770168276722438869701 4122706906551885457288069)
                      ·
                        rfl

theorem cell23_8028943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_8028943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028943 prefixEnd_8028943 := by exact prefixLift 8028943
  have htrace : WordTrace (prefixWord ++ tailWord_8028943) baseStart_8028943 baseEnd_8028943 := by
    simpa [prefixWord, tailWord_8028943, baseEnd_8028943] using wordTrace_append hprefix tailTrace_8028943
  have hstable : (prefixWord ++ tailWord_8028943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028943).length < 2 ^ (prefixWord ++ tailWord_8028943).sum := by decide
  have hdescent : baseEnd_8028943 < baseStart_8028943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8028960 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_8028960 : Nat := 118140960795 + 8028960 * 2 ^ 59
def prefixEnd_8028960 : Nat := 4983230072969 + 3 ^ 40 * 8028960 * 2
def baseEnd_8028960 : Nat := 4122715635723011890775491

theorem tailTrace_8028960 : CollatzResearch.WordTrace tailWord_8028960 prefixEnd_8028960 4122715635723011890775491 := by
  unfold tailWord_8028960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146420114496228316021670167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195226819328304421362226889 146420114496228316021670167)
  ·
    refine ⟨219630171744342474032505251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146420114496228316021670167 219630171744342474032505251)
    ·
      refine ⟨329445257616513711048757877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219630171744342474032505251 329445257616513711048757877)
      ·
        refine ⟨30885492901548160410821051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329445257616513711048757877 30885492901548160410821051)
        ·
          refine ⟨46328239352322240616231577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30885492901548160410821051 46328239352322240616231577)
          ·
            refine ⟨34746179514241680462173683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46328239352322240616231577 34746179514241680462173683)
            ·
              refine ⟨52119269271362520693260525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34746179514241680462173683 52119269271362520693260525)
              ·
                refine ⟨19544725976760945259972697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52119269271362520693260525 19544725976760945259972697)
                ·
                  refine ⟨14658544482570708944979523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19544725976760945259972697 14658544482570708944979523)
                  ·
                    refine ⟨21987816723856063417469285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14658544482570708944979523 21987816723856063417469285)
                    ·
                      refine ⟨4122715635723011890775491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21987816723856063417469285 4122715635723011890775491)
                      ·
                        rfl

theorem cell23_8028960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_8028960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8028960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8028960 prefixEnd_8028960 := by exact prefixLift 8028960
  have htrace : WordTrace (prefixWord ++ tailWord_8028960) baseStart_8028960 baseEnd_8028960 := by
    simpa [prefixWord, tailWord_8028960, baseEnd_8028960] using wordTrace_append hprefix tailTrace_8028960
  have hstable : (prefixWord ++ tailWord_8028960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8028960).length < 2 ^ (prefixWord ++ tailWord_8028960).sum := by decide
  have hdescent : baseEnd_8028960 < baseStart_8028960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8028960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_8029037 : Nat := 118140960795 + 8029037 * 2 ^ 59
def prefixEnd_8029037 : Nat := 4983230072969 + 3 ^ 40 * 8029037 * 2
def baseEnd_8029037 : Nat := 4122755173733408089512637

theorem tailTrace_8029037 : CollatzResearch.WordTrace tailWord_8029037 prefixEnd_8029037 4122755173733408089512637 := by
  unfold tailWord_8029037
  simp only [CollatzResearch.WordTrace]
  refine ⟨292843037413177674193893365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195228691608785116129262243 292843037413177674193893365)
  ·
    refine ⟨27454034757485406955677503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292843037413177674193893365 27454034757485406955677503)
    ·
      refine ⟨41181052136228110433516255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27454034757485406955677503 41181052136228110433516255)
      ·
        refine ⟨61771578204342165650274383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41181052136228110433516255 61771578204342165650274383)
        ·
          refine ⟨92657367306513248475411575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61771578204342165650274383 92657367306513248475411575)
          ·
            refine ⟨138986050959769872713117363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92657367306513248475411575 138986050959769872713117363)
            ·
              refine ⟨208479076439654809069676045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138986050959769872713117363 208479076439654809069676045)
              ·
                refine ⟨78179653664870553401128517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208479076439654809069676045 78179653664870553401128517)
                ·
                  refine ⟨14658685062163228762711597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78179653664870553401128517 14658685062163228762711597)
                  ·
                    refine ⟨5497006898311210786016849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14658685062163228762711597 5497006898311210786016849)
                    ·
                      refine ⟨4122755173733408089512637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497006898311210786016849 4122755173733408089512637)
                      ·
                        rfl

theorem cell23_8029037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_8029037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029037 prefixEnd_8029037 := by exact prefixLift 8029037
  have htrace : WordTrace (prefixWord ++ tailWord_8029037) baseStart_8029037 baseEnd_8029037 := by
    simpa [prefixWord, tailWord_8029037, baseEnd_8029037] using wordTrace_append hprefix tailTrace_8029037
  have hstable : (prefixWord ++ tailWord_8029037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029037).length < 2 ^ (prefixWord ++ tailWord_8029037).sum := by decide
  have hdescent : baseEnd_8029037 < baseStart_8029037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029043 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 6]
def baseStart_8029043 : Nat := 118140960795 + 8029043 * 2 ^ 59
def prefixEnd_8029043 : Nat := 4983230072969 + 3 ^ 40 * 8029043 * 2
def baseEnd_8029043 : Nat := 1374252751539111688679203

theorem tailTrace_8029043 : CollatzResearch.WordTrace tailWord_8029043 prefixEnd_8029043 1374252751539111688679203 := by
  unfold tailWord_8029043
  simp only [CollatzResearch.WordTrace]
  refine ⟨292843256251155937218611783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195228837500770624812407855 292843256251155937218611783)
  ·
    refine ⟨439264884376733905827917675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292843256251155937218611783 439264884376733905827917675)
    ·
      refine ⟨658897326565100858741876513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439264884376733905827917675 658897326565100858741876513)
      ·
        refine ⟨494172994923825644056407385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658897326565100858741876513 494172994923825644056407385)
        ·
          refine ⟨370629746192869233042305539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494172994923825644056407385 370629746192869233042305539)
          ·
            refine ⟨555944619289303849563458309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370629746192869233042305539 555944619289303849563458309)
            ·
              refine ⟨104239616116744471793148433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 555944619289303849563458309 104239616116744471793148433)
              ·
                refine ⟨78179712087558353844861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104239616116744471793148433 78179712087558353844861325)
                ·
                  refine ⟨29317392032834382691822997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78179712087558353844861325 29317392032834382691822997)
                  ·
                    refine ⟨1374252751539111688679203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29317392032834382691822997 1374252751539111688679203)
                    ·
                      rfl

theorem cell23_8029043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_8029043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029043 prefixEnd_8029043 := by exact prefixLift 8029043
  have htrace : WordTrace (prefixWord ++ tailWord_8029043) baseStart_8029043 baseEnd_8029043 := by
    simpa [prefixWord, tailWord_8029043, baseEnd_8029043] using wordTrace_append hprefix tailTrace_8029043
  have hstable : (prefixWord ++ tailWord_8029043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029043).length < 2 ^ (prefixWord ++ tailWord_8029043).sum := by decide
  have hdescent : baseEnd_8029043 < baseStart_8029043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029087 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_8029087 : Nat := 118140960795 + 8029087 * 2 ^ 59
def prefixEnd_8029087 : Nat := 4983230072969 + 3 ^ 40 * 8029087 * 2
def baseEnd_8029087 : Nat := 4122780847766132893887407

theorem tailTrace_8029087 : CollatzResearch.WordTrace tailWord_8029087 prefixEnd_8029087 4122780847766132893887407 := by
  unfold tailWord_8029087
  simp only [CollatzResearch.WordTrace]
  refine ⟨292844861062996532733213515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195229907375331021822142343 292844861062996532733213515)
  ·
    refine ⟨439267291594494799099820273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292844861062996532733213515 439267291594494799099820273)
    ·
      refine ⟨329450468695871099324865205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439267291594494799099820273 329450468695871099324865205)
      ·
        refine ⟨30885981440237915561706113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329450468695871099324865205 30885981440237915561706113)
        ·
          refine ⟨23164486080178436671279585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30885981440237915561706113 23164486080178436671279585)
          ·
            refine ⟨17373364560133827503459689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23164486080178436671279585 17373364560133827503459689)
            ·
              refine ⟨13030023420100370627594767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17373364560133827503459689 13030023420100370627594767)
              ·
                refine ⟨19545035130150555941392151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030023420100370627594767 19545035130150555941392151)
                ·
                  refine ⟨29317552695225833912088227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19545035130150555941392151 29317552695225833912088227)
                  ·
                    refine ⟨43976329042838750868132341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29317552695225833912088227 43976329042838750868132341)
                    ·
                      refine ⟨4122780847766132893887407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43976329042838750868132341 4122780847766132893887407)
                      ·
                        rfl

theorem cell23_8029087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_8029087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029087 prefixEnd_8029087 := by exact prefixLift 8029087
  have htrace : WordTrace (prefixWord ++ tailWord_8029087) baseStart_8029087 baseEnd_8029087 := by
    simpa [prefixWord, tailWord_8029087, baseEnd_8029087] using wordTrace_append hprefix tailTrace_8029087
  have hstable : (prefixWord ++ tailWord_8029087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029087).length < 2 ^ (prefixWord ++ tailWord_8029087).sum := by decide
  have hdescent : baseEnd_8029087 < baseStart_8029087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029090 : List Nat := [3, 3, 1, 2, 2, 1, 11]
def baseStart_8029090 : Nat := 118140960795 + 8029090 * 2 ^ 59
def prefixEnd_8029090 : Nat := 4983230072969 + 3 ^ 40 * 8029090 * 2
def baseEnd_8029090 : Nat := 50898548002569091137653

theorem tailTrace_8029090 : CollatzResearch.WordTrace tailWord_8029090 prefixEnd_8029090 50898548002569091137653 := by
  unfold tailWord_8029090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73211242620496416061393181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195229980321323776163715149 73211242620496416061393181)
  ·
    refine ⟨27454215982686156023022443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73211242620496416061393181 27454215982686156023022443)
    ·
      refine ⟨41181323974029234034533665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27454215982686156023022443 41181323974029234034533665)
      ·
        refine ⟨30885992980521925525900249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41181323974029234034533665 30885992980521925525900249)
        ·
          refine ⟨23164494735391444144425187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30885992980521925525900249 23164494735391444144425187)
          ·
            refine ⟨34746742103087166216637781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164494735391444144425187 34746742103087166216637781)
            ·
              refine ⟨50898548002569091137653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34746742103087166216637781 50898548002569091137653)
              ·
                rfl

theorem cell23_8029090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 11].length) (baseStart_8029090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029090 prefixEnd_8029090 := by exact prefixLift 8029090
  have htrace : WordTrace (prefixWord ++ tailWord_8029090) baseStart_8029090 baseEnd_8029090 := by
    simpa [prefixWord, tailWord_8029090, baseEnd_8029090] using wordTrace_append hprefix tailTrace_8029090
  have hstable : (prefixWord ++ tailWord_8029090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029090).length < 2 ^ (prefixWord ++ tailWord_8029090).sum := by decide
  have hdescent : baseEnd_8029090 < baseStart_8029090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029100 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_8029100 : Nat := 118140960795 + 8029100 * 2 ^ 59
def prefixEnd_8029100 : Nat := 4983230072969 + 3 ^ 40 * 8029100 * 2
def baseEnd_8029100 : Nat := 4122787523014641343024847

theorem tailTrace_8029100 : CollatzResearch.WordTrace tailWord_8029100 prefixEnd_8029100 4122787523014641343024847 := by
  unfold tailWord_8029100
  simp only [CollatzResearch.WordTrace]
  refine ⟨146422667605974717976718377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195230223474632957302291169 146422667605974717976718377)
  ·
    refine ⟨109817000704481038482538783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146422667605974717976718377 109817000704481038482538783)
    ·
      refine ⟨164725501056721557723808175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109817000704481038482538783 164725501056721557723808175)
      ·
        refine ⟨247088251585082336585712263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164725501056721557723808175 247088251585082336585712263)
        ·
          refine ⟨370632377377623504878568395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247088251585082336585712263 370632377377623504878568395)
          ·
            refine ⟨555948566066435257317852593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370632377377623504878568395 555948566066435257317852593)
            ·
              refine ⟨416961424549826442988389445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555948566066435257317852593 416961424549826442988389445)
              ·
                refine ⟨78180267103092458060323021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416961424549826442988389445 78180267103092458060323021)
                ·
                  refine ⟨29317600163659671772621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78180267103092458060323021 29317600163659671772621133)
                  ·
                    refine ⟨10994100061372376914732925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29317600163659671772621133 10994100061372376914732925)
                    ·
                      refine ⟨4122787523014641343024847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994100061372376914732925 4122787523014641343024847)
                      ·
                        rfl

theorem cell23_8029100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_8029100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029100 prefixEnd_8029100 := by exact prefixLift 8029100
  have htrace : WordTrace (prefixWord ++ tailWord_8029100) baseStart_8029100 baseEnd_8029100 := by
    simpa [prefixWord, tailWord_8029100, baseEnd_8029100] using wordTrace_append hprefix tailTrace_8029100
  have hstable : (prefixWord ++ tailWord_8029100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029100).length < 2 ^ (prefixWord ++ tailWord_8029100).sum := by decide
  have hdescent : baseEnd_8029100 < baseStart_8029100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029151 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_8029151 : Nat := 118140960795 + 8029151 * 2 ^ 59
def prefixEnd_8029151 : Nat := 4983230072969 + 3 ^ 40 * 8029151 * 2
def baseEnd_8029151 : Nat := 4122813710528020643487113

theorem tailTrace_8029151 : CollatzResearch.WordTrace tailWord_8029151 prefixEnd_8029151 4122813710528020643487113 := by
  unfold tailWord_8029151
  simp only [CollatzResearch.WordTrace]
  refine ⟨292847195334764671663543307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195231463556509781109028871 292847195334764671663543307)
  ·
    refine ⟨439270793002147007495314961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292847195334764671663543307 439270793002147007495314961)
    ·
      refine ⟨329453094751610255621486221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439270793002147007495314961 329453094751610255621486221)
      ·
        refine ⟨123544910531853845858057333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329453094751610255621486221 123544910531853845858057333)
        ·
          refine ⟨11582335362361298049192875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123544910531853845858057333 11582335362361298049192875)
          ·
            refine ⟨17373503043541947073789313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11582335362361298049192875 17373503043541947073789313)
            ·
              refine ⟨13030127282656460305341985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17373503043541947073789313 13030127282656460305341985)
              ·
                refine ⟨9772595461992345229006489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030127282656460305341985 9772595461992345229006489)
                ·
                  refine ⟨7329446596494258921754867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9772595461992345229006489 7329446596494258921754867)
                  ·
                    refine ⟨10994169894741388382632301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329446596494258921754867 10994169894741388382632301)
                    ·
                      refine ⟨4122813710528020643487113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994169894741388382632301 4122813710528020643487113)
                      ·
                        rfl

theorem cell23_8029151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_8029151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029151 prefixEnd_8029151 := by exact prefixLift 8029151
  have htrace : WordTrace (prefixWord ++ tailWord_8029151) baseStart_8029151 baseEnd_8029151 := by
    simpa [prefixWord, tailWord_8029151, baseEnd_8029151] using wordTrace_append hprefix tailTrace_8029151
  have hstable : (prefixWord ++ tailWord_8029151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029151).length < 2 ^ (prefixWord ++ tailWord_8029151).sum := by decide
  have hdescent : baseEnd_8029151 < baseStart_8029151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029160 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8029160 : Nat := 118140960795 + 8029160 * 2 ^ 59
def prefixEnd_8029160 : Nat := 4983230072969 + 3 ^ 40 * 8029160 * 2
def baseEnd_8029160 : Nat := 4122818331853911108274571

theorem tailTrace_8029160 : CollatzResearch.WordTrace tailWord_8029160 prefixEnd_8029160 4122818331853911108274571 := by
  unfold tailWord_8029160
  simp only [CollatzResearch.WordTrace]
  refine ⟨146423761795866033100310467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195231682394488044133747289 146423761795866033100310467)
  ·
    refine ⟨219635642693799049650465701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146423761795866033100310467 219635642693799049650465701)
    ·
      refine ⟨41181683005087321809462319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219635642693799049650465701 41181683005087321809462319)
      ·
        refine ⟨61772524507630982714193479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41181683005087321809462319 61772524507630982714193479)
        ·
          refine ⟨92658786761446474071290219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61772524507630982714193479 92658786761446474071290219)
          ·
            refine ⟨138988180142169711106935329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92658786761446474071290219 138988180142169711106935329)
            ·
              refine ⟨104241135106627283330201497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138988180142169711106935329 104241135106627283330201497)
              ·
                refine ⟨78180851329970462497651123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104241135106627283330201497 78180851329970462497651123)
                ·
                  refine ⟨117271276994955693746476685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78180851329970462497651123 117271276994955693746476685)
                  ·
                    refine ⟨43976728873108385154928757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117271276994955693746476685 43976728873108385154928757)
                    ·
                      refine ⟨4122818331853911108274571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43976728873108385154928757 4122818331853911108274571)
                      ·
                        rfl

theorem cell23_8029160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8029160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029160 prefixEnd_8029160 := by exact prefixLift 8029160
  have htrace : WordTrace (prefixWord ++ tailWord_8029160) baseStart_8029160 baseEnd_8029160 := by
    simpa [prefixWord, tailWord_8029160, baseEnd_8029160] using wordTrace_append hprefix tailTrace_8029160
  have hstable : (prefixWord ++ tailWord_8029160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029160).length < 2 ^ (prefixWord ++ tailWord_8029160).sum := by decide
  have hdescent : baseEnd_8029160 < baseStart_8029160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029180 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 9]
def baseStart_8029180 : Nat := 118140960795 + 8029180 * 2 ^ 59
def prefixEnd_8029180 : Nat := 4983230072969 + 3 ^ 40 * 8029180 * 2
def baseEnd_8029180 : Nat := 458092066829666781113831

theorem tailTrace_8029180 : CollatzResearch.WordTrace tailWord_8029180 prefixEnd_8029180 458092066829666781113831 := by
  unfold tailWord_8029180
  simp only [CollatzResearch.WordTrace]
  refine ⟨146424126525829804808174497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195232168701106406410899329 146424126525829804808174497)
  ·
    refine ⟨109818094894372353606130873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146424126525829804808174497 109818094894372353606130873)
    ·
      refine ⟨82363571170779265204598155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109818094894372353606130873 82363571170779265204598155)
      ·
        refine ⟨123545356756168897806897233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82363571170779265204598155 123545356756168897806897233)
        ·
          refine ⟨92659017567126673355172925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123545356756168897806897233 92659017567126673355172925)
          ·
            refine ⟨34747131587672502508189847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92659017567126673355172925 34747131587672502508189847)
            ·
              refine ⟨52120697381508753762284771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34747131587672502508189847 52120697381508753762284771)
              ·
                refine ⟨78181046072263130643427157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52120697381508753762284771 78181046072263130643427157)
                ·
                  refine ⟨458092066829666781113831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78181046072263130643427157 458092066829666781113831)
                  ·
                    rfl

theorem cell23_8029180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_8029180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029180 prefixEnd_8029180 := by exact prefixLift 8029180
  have htrace : WordTrace (prefixWord ++ tailWord_8029180) baseStart_8029180 baseEnd_8029180 := by
    simpa [prefixWord, tailWord_8029180, baseEnd_8029180] using wordTrace_append hprefix tailTrace_8029180
  have hstable : (prefixWord ++ tailWord_8029180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029180).length < 2 ^ (prefixWord ++ tailWord_8029180).sum := by decide
  have hdescent : baseEnd_8029180 < baseStart_8029180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029202 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8029202 : Nat := 118140960795 + 8029202 * 2 ^ 59
def prefixEnd_8029202 : Nat := 4983230072969 + 3 ^ 40 * 8029202 * 2
def baseEnd_8029202 : Nat := 4122839898041399943949379

theorem tailTrace_8029202 : CollatzResearch.WordTrace tailWord_8029202 prefixEnd_8029202 4122839898041399943949379 := by
  unfold tailWord_8029202
  simp only [CollatzResearch.WordTrace]
  refine ⟨73212263864394976843412465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195232703638386604915766573 73212263864394976843412465)
  ·
    refine ⟨54909197898296232632559349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73212263864394976843412465 54909197898296232632559349)
    ·
      refine ⟨5147737302965271809302439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54909197898296232632559349 5147737302965271809302439)
      ·
        refine ⟨7721605954447907713953659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147737302965271809302439 7721605954447907713953659)
        ·
          refine ⟨11582408931671861570930489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721605954447907713953659 11582408931671861570930489)
          ·
            refine ⟨8686806698753896178197867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11582408931671861570930489 8686806698753896178197867)
            ·
              refine ⟨13030210048130844267296801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686806698753896178197867 13030210048130844267296801)
              ·
                refine ⟨9772657536098133200472601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030210048130844267296801 9772657536098133200472601)
                ·
                  refine ⟨7329493152073599900354451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9772657536098133200472601 7329493152073599900354451)
                  ·
                    refine ⟨10994239728110399850531677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329493152073599900354451 10994239728110399850531677)
                    ·
                      refine ⟨4122839898041399943949379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994239728110399850531677 4122839898041399943949379)
                      ·
                        rfl

theorem cell23_8029202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8029202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029202 prefixEnd_8029202 := by exact prefixLift 8029202
  have htrace : WordTrace (prefixWord ++ tailWord_8029202) baseStart_8029202 baseEnd_8029202 := by
    simpa [prefixWord, tailWord_8029202, baseEnd_8029202] using wordTrace_append hprefix tailTrace_8029202
  have hstable : (prefixWord ++ tailWord_8029202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029202).length < 2 ^ (prefixWord ++ tailWord_8029202).sum := by decide
  have hdescent : baseEnd_8029202 < baseStart_8029202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029208 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_8029208 : Nat := 118140960795 + 8029208 * 2 ^ 59
def prefixEnd_8029208 : Nat := 4983230072969 + 3 ^ 40 * 8029208 * 2
def baseEnd_8029208 : Nat := 4122842978925326920474351

theorem tailTrace_8029208 : CollatzResearch.WordTrace tailWord_8029208 prefixEnd_8029208 4122842978925326920474351 := by
  unfold tailWord_8029208
  simp only [CollatzResearch.WordTrace]
  refine ⟨146424637147779085199184139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195232849530372113598912185 146424637147779085199184139)
  ·
    refine ⟨219636955721668627798776209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146424637147779085199184139 219636955721668627798776209)
    ·
      refine ⟨164727716791251470849082157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219636955721668627798776209 164727716791251470849082157)
      ·
        refine ⟨61772893796719301568405809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164727716791251470849082157 61772893796719301568405809)
        ·
          refine ⟨46329670347539476176304357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61772893796719301568405809 46329670347539476176304357)
          ·
            refine ⟨8686813190163651783057067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46329670347539476176304357 8686813190163651783057067)
            ·
              refine ⟨13030219785245477674585601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686813190163651783057067 13030219785245477674585601)
              ·
                refine ⟨9772664838934108255939201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030219785245477674585601 9772664838934108255939201)
                ·
                  refine ⟨7329498629200581191954401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9772664838934108255939201 7329498629200581191954401)
                  ·
                    refine ⟨5497123971900435893965801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7329498629200581191954401 5497123971900435893965801)
                    ·
                      refine ⟨4122842978925326920474351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497123971900435893965801 4122842978925326920474351)
                      ·
                        rfl

theorem cell23_8029208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_8029208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029208 prefixEnd_8029208 := by exact prefixLift 8029208
  have htrace : WordTrace (prefixWord ++ tailWord_8029208) baseStart_8029208 baseEnd_8029208 := by
    simpa [prefixWord, tailWord_8029208, baseEnd_8029208] using wordTrace_append hprefix tailTrace_8029208
  have hstable : (prefixWord ++ tailWord_8029208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029208).length < 2 ^ (prefixWord ++ tailWord_8029208).sum := by decide
  have hdescent : baseEnd_8029208 < baseStart_8029208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029247 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_8029247 : Nat := 118140960795 + 8029247 * 2 ^ 59
def prefixEnd_8029247 : Nat := 4983230072969 + 3 ^ 40 * 8029247 * 2
def baseEnd_8029247 : Nat := 4122863004670852267886671

theorem tailTrace_8029247 : CollatzResearch.WordTrace tailWord_8029247 prefixEnd_8029247 4122863004670852267886671 := by
  unfold tailWord_8029247
  simp only [CollatzResearch.WordTrace]
  refine ⟨292850696742416880059037995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195233797828277920039358663 292850696742416880059037995)
  ·
    refine ⟨439276045113625320088556993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292850696742416880059037995 439276045113625320088556993)
    ·
      refine ⟨329457033835218990066417745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439276045113625320088556993 329457033835218990066417745)
      ·
        refine ⟨247092775376414242549813309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329457033835218990066417745 247092775376414242549813309)
        ·
          refine ⟨92659790766155340956179991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247092775376414242549813309 92659790766155340956179991)
          ·
            refine ⟨138989686149233011434269987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92659790766155340956179991 138989686149233011434269987)
            ·
              refine ⟨208484529223849517151404981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138989686149233011434269987 208484529223849517151404981)
              ·
                refine ⟨19545424614735892232944217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208484529223849517151404981 19545424614735892232944217)
                ·
                  refine ⟨14659068461051919174708163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19545424614735892232944217 14659068461051919174708163)
                  ·
                    refine ⟨21988602691577878762062245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14659068461051919174708163 21988602691577878762062245)
                    ·
                      refine ⟨4122863004670852267886671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21988602691577878762062245 4122863004670852267886671)
                      ·
                        rfl

theorem cell23_8029247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_8029247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029247 prefixEnd_8029247 := by exact prefixLift 8029247
  have htrace : WordTrace (prefixWord ++ tailWord_8029247) baseStart_8029247 baseEnd_8029247 := by
    simpa [prefixWord, tailWord_8029247, baseEnd_8029247] using wordTrace_append hprefix tailTrace_8029247
  have hstable : (prefixWord ++ tailWord_8029247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029247).length < 2 ^ (prefixWord ++ tailWord_8029247).sum := by decide
  have hdescent : baseEnd_8029247 < baseStart_8029247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029267 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3]
def baseStart_8029267 : Nat := 118140960795 + 8029267 * 2 ^ 59
def prefixEnd_8029267 : Nat := 4983230072969 + 3 ^ 40 * 8029267 * 2
def baseEnd_8029267 : Nat := 4122873274283942189636579

theorem tailTrace_8029267 : CollatzResearch.WordTrace tailWord_8029267 prefixEnd_8029267 4122873274283942189636579 := by
  unfold tailWord_8029267
  simp only [CollatzResearch.WordTrace]
  refine ⟨292851426202344423474766055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195234284134896282316510703 292851426202344423474766055)
  ·
    refine ⟨439277139303516635212149083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292851426202344423474766055 439277139303516635212149083)
    ·
      refine ⟨658915708955274952818223625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439277139303516635212149083 658915708955274952818223625)
      ·
        refine ⟨494186781716456214613667719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658915708955274952818223625 494186781716456214613667719)
        ·
          refine ⟨741280172574684321920501579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494186781716456214613667719 741280172574684321920501579)
          ·
            refine ⟨1111920258862026482880752369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741280172574684321920501579 1111920258862026482880752369)
            ·
              refine ⟨833940194146519862160564277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111920258862026482880752369 833940194146519862160564277)
              ·
                refine ⟨78181893201236237077552901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833940194146519862160564277 78181893201236237077552901)
                ·
                  refine ⟨14659104975231794452041169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78181893201236237077552901 14659104975231794452041169)
                  ·
                    refine ⟨10994328731423845839030877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14659104975231794452041169 10994328731423845839030877)
                    ·
                      refine ⟨4122873274283942189636579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994328731423845839030877 4122873274283942189636579)
                      ·
                        rfl

theorem cell23_8029267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_8029267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029267 prefixEnd_8029267 := by exact prefixLift 8029267
  have htrace : WordTrace (prefixWord ++ tailWord_8029267) baseStart_8029267 baseEnd_8029267 := by
    simpa [prefixWord, tailWord_8029267, baseEnd_8029267] using wordTrace_append hprefix tailTrace_8029267
  have hstable : (prefixWord ++ tailWord_8029267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029267).length < 2 ^ (prefixWord ++ tailWord_8029267).sum := by decide
  have hdescent : baseEnd_8029267 < baseStart_8029267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029407 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 7]
def baseStart_8029407 : Nat := 118140960795 + 8029407 * 2 ^ 59
def prefixEnd_8029407 : Nat := 4983230072969 + 3 ^ 40 * 8029407 * 2
def baseEnd_8029407 : Nat := 1374315053858523880628645

theorem tailTrace_8029407 : CollatzResearch.WordTrace tailWord_8029407 prefixEnd_8029407 1374315053858523880628645 := by
  unfold tailWord_8029407
  simp only [CollatzResearch.WordTrace]
  refine ⟨292856532421837227384862475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195237688281224818256574983 292856532421837227384862475)
  ·
    refine ⟨439284798632755841077293713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292856532421837227384862475 439284798632755841077293713)
    ·
      refine ⟨329463598974566880807970285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439284798632755841077293713 329463598974566880807970285)
      ·
        refine ⟨123548849615462580302988857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329463598974566880807970285 123548849615462580302988857)
        ·
          refine ⟨92661637211596935227241643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123548849615462580302988857 92661637211596935227241643)
          ·
            refine ⟨138992455817395402840862465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92661637211596935227241643 138992455817395402840862465)
            ·
              refine ⟨104244341863046552130646849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138992455817395402840862465 104244341863046552130646849)
              ·
                refine ⟨78183256397284914097985137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104244341863046552130646849 78183256397284914097985137)
                ·
                  refine ⟨58637442297963685573488853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78183256397284914097985137 58637442297963685573488853)
                  ·
                    refine ⟨1374315053858523880628645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58637442297963685573488853 1374315053858523880628645)
                    ·
                      rfl

theorem cell23_8029407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_8029407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029407 prefixEnd_8029407 := by exact prefixLift 8029407
  have htrace : WordTrace (prefixWord ++ tailWord_8029407) baseStart_8029407 baseEnd_8029407 := by
    simpa [prefixWord, tailWord_8029407, baseEnd_8029407] using wordTrace_append hprefix tailTrace_8029407
  have hstable : (prefixWord ++ tailWord_8029407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029407).length < 2 ^ (prefixWord ++ tailWord_8029407).sum := by decide
  have hdescent : baseEnd_8029407 < baseStart_8029407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029438 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_8029438 : Nat := 118140960795 + 8029438 * 2 ^ 59
def prefixEnd_8029438 : Nat := 4983230072969 + 3 ^ 40 * 8029438 * 2
def baseEnd_8029438 : Nat := 4122961079475861020598293

theorem tailTrace_8029438 : CollatzResearch.WordTrace tailWord_8029438 prefixEnd_8029438 4122961079475861020598293 := by
  unfold tailWord_8029438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607207885590614959905121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195238442056483279786160645 36607207885590614959905121)
  ·
    refine ⟨27455405914192961219928841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36607207885590614959905121 27455405914192961219928841)
    ·
      refine ⟨20591554435644720914946631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27455405914192961219928841 20591554435644720914946631)
      ·
        refine ⟨30887331653467081372419947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591554435644720914946631 30887331653467081372419947)
        ·
          refine ⟨46330997480200622058629921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887331653467081372419947 46330997480200622058629921)
          ·
            refine ⟨34748248110150466543972441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46330997480200622058629921 34748248110150466543972441)
            ·
              refine ⟨26061186082612849907979331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34748248110150466543972441 26061186082612849907979331)
              ·
                refine ⟨39091779123919274861968997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061186082612849907979331 39091779123919274861968997)
                ·
                  refine ⟨7329708585734864036619187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39091779123919274861968997 7329708585734864036619187)
                  ·
                    refine ⟨10994562878602296054928781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329708585734864036619187 10994562878602296054928781)
                    ·
                      refine ⟨4122961079475861020598293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994562878602296054928781 4122961079475861020598293)
                      ·
                        rfl

theorem cell23_8029438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_8029438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029438 prefixEnd_8029438 := by exact prefixLift 8029438
  have htrace : WordTrace (prefixWord ++ tailWord_8029438) baseStart_8029438 baseEnd_8029438 := by
    simpa [prefixWord, tailWord_8029438, baseEnd_8029438] using wordTrace_append hprefix tailTrace_8029438
  have hstable : (prefixWord ++ tailWord_8029438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029438).length < 2 ^ (prefixWord ++ tailWord_8029438).sum := by decide
  have hdescent : baseEnd_8029438 < baseStart_8029438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029461 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_8029461 : Nat := 118140960795 + 8029461 * 2 ^ 59
def prefixEnd_8029461 : Nat := 4983230072969 + 3 ^ 40 * 8029461 * 2
def baseEnd_8029461 : Nat := 4122972889530914430610687

theorem tailTrace_8029461 : CollatzResearch.WordTrace tailWord_8029461 prefixEnd_8029461 4122972889530914430610687 := by
  unfold tailWord_8029461
  simp only [CollatzResearch.WordTrace]
  refine ⟨292858501963641594607328237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195239001309094396404885491 292858501963641594607328237)
  ·
    refine ⟨109821938236365597977748089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292858501963641594607328237 109821938236365597977748089)
    ·
      refine ⟨82366453677274198483311067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109821938236365597977748089 82366453677274198483311067)
      ·
        refine ⟨123549680515911297724966601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82366453677274198483311067 123549680515911297724966601)
        ·
          refine ⟨92662260386933473293724951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123549680515911297724966601 92662260386933473293724951)
          ·
            refine ⟨138993390580400209940587427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92662260386933473293724951 138993390580400209940587427)
            ·
              refine ⟨208490085870600314910881141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138993390580400209940587427 208490085870600314910881141)
              ·
                refine ⟨19545945550368779522895107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208490085870600314910881141 19545945550368779522895107)
                ·
                  refine ⟨29318918325553169284342661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19545945550368779522895107 29318918325553169284342661)
                  ·
                    refine ⟨5497297186041219240814249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29318918325553169284342661 5497297186041219240814249)
                    ·
                      refine ⟨4122972889530914430610687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497297186041219240814249 4122972889530914430610687)
                      ·
                        rfl

theorem cell23_8029461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_8029461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029461 prefixEnd_8029461 := by exact prefixLift 8029461
  have htrace : WordTrace (prefixWord ++ tailWord_8029461) baseStart_8029461 baseEnd_8029461 := by
    simpa [prefixWord, tailWord_8029461, baseEnd_8029461] using wordTrace_append hprefix tailTrace_8029461
  have hstable : (prefixWord ++ tailWord_8029461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029461).length < 2 ^ (prefixWord ++ tailWord_8029461).sum := by decide
  have hdescent : baseEnd_8029461 < baseStart_8029461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029464 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_8029464 : Nat := 118140960795 + 8029464 * 2 ^ 59
def prefixEnd_8029464 : Nat := 4983230072969 + 3 ^ 40 * 8029464 * 2
def baseEnd_8029464 : Nat := 4122974429972877918873173

theorem tailTrace_8029464 : CollatzResearch.WordTrace tailWord_8029464 prefixEnd_8029464 4122974429972877918873173 := by
  unfold tailWord_8029464
  simp only [CollatzResearch.WordTrace]
  refine ⟨146429305691315363059843723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195239074255087150746458297 146429305691315363059843723)
  ·
    refine ⟨219643958536973044589765585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146429305691315363059843723 219643958536973044589765585)
    ·
      refine ⟨164732968902729783442324189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219643958536973044589765585 164732968902729783442324189)
      ·
        refine ⟨61774863338523668790871571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164732968902729783442324189 61774863338523668790871571)
        ·
          refine ⟨92662295007785503186307357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61774863338523668790871571 92662295007785503186307357)
          ·
            refine ⟨34748360627919563694865259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92662295007785503186307357 34748360627919563694865259)
            ·
              refine ⟨52122540941879345542297889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34748360627919563694865259 52122540941879345542297889)
              ·
                refine ⟨39091905706409509156723417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52122540941879345542297889 39091905706409509156723417)
                ·
                  refine ⟨29318929279807131867542563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39091905706409509156723417 29318929279807131867542563)
                  ·
                    refine ⟨43978393919710697801313845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29318929279807131867542563 43978393919710697801313845)
                    ·
                      refine ⟨4122974429972877918873173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43978393919710697801313845 4122974429972877918873173)
                      ·
                        rfl

theorem cell23_8029464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_8029464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029464 prefixEnd_8029464 := by exact prefixLift 8029464
  have htrace : WordTrace (prefixWord ++ tailWord_8029464) baseStart_8029464 baseEnd_8029464 := by
    simpa [prefixWord, tailWord_8029464, baseEnd_8029464] using wordTrace_append hprefix tailTrace_8029464
  have hstable : (prefixWord ++ tailWord_8029464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029464).length < 2 ^ (prefixWord ++ tailWord_8029464).sum := by decide
  have hdescent : baseEnd_8029464 < baseStart_8029464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029467 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 9]
def baseStart_8029467 : Nat := 118140960795 + 8029467 * 2 ^ 59
def prefixEnd_8029467 : Nat := 4983230072969 + 3 ^ 40 * 8029467 * 2
def baseEnd_8029467 : Nat := 458108441157204600792851

theorem tailTrace_8029467 : CollatzResearch.WordTrace tailWord_8029467 prefixEnd_8029467 458108441157204600792851 := by
  unfold tailWord_8029467
  simp only [CollatzResearch.WordTrace]
  refine ⟨292858720801619857632046655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195239147201079905088031103 292858720801619857632046655)
  ·
    refine ⟨439288081202429786448069983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292858720801619857632046655 439288081202429786448069983)
    ·
      refine ⟨658932121803644679672104975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439288081202429786448069983 658932121803644679672104975)
      ·
        refine ⟨988398182705467019508157463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658932121803644679672104975 988398182705467019508157463)
        ·
          refine ⟨1482597274058200529262236195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988398182705467019508157463 1482597274058200529262236195)
          ·
            refine ⟨2223895911087300793893354293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482597274058200529262236195 2223895911087300793893354293)
            ·
              refine ⟨208490241664434449427501965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2223895911087300793893354293 208490241664434449427501965)
              ·
                refine ⟨78183840624162918535313237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208490241664434449427501965 78183840624162918535313237)
                ·
                  refine ⟨458108441157204600792851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78183840624162918535313237 458108441157204600792851)
                  ·
                    rfl

theorem cell23_8029467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_8029467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029467 prefixEnd_8029467 := by exact prefixLift 8029467
  have htrace : WordTrace (prefixWord ++ tailWord_8029467) baseStart_8029467 baseEnd_8029467 := by
    simpa [prefixWord, tailWord_8029467, baseEnd_8029467] using wordTrace_append hprefix tailTrace_8029467
  have hstable : (prefixWord ++ tailWord_8029467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029467).length < 2 ^ (prefixWord ++ tailWord_8029467).sum := by decide
  have hdescent : baseEnd_8029467 < baseStart_8029467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029482 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_8029482 : Nat := 118140960795 + 8029482 * 2 ^ 59
def prefixEnd_8029482 : Nat := 4983230072969 + 3 ^ 40 * 8029482 * 2
def baseEnd_8029482 : Nat := 4122983672624658848448091

theorem tailTrace_8029482 : CollatzResearch.WordTrace tailWord_8029482 prefixEnd_8029482 4122983672624658848448091 := by
  unfold tailWord_8029482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73214816974141378798460675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195239511931043676795895133 73214816974141378798460675)
  ·
    refine ⟨109822225461212068197691013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73214816974141378798460675 109822225461212068197691013)
    ·
      refine ⟨20591667273977262787067065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109822225461212068197691013 20591667273977262787067065)
      ·
        refine ⟨15443750455482947090300299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20591667273977262787067065 15443750455482947090300299)
        ·
          refine ⟨23165625683224420635450449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15443750455482947090300299 23165625683224420635450449)
          ·
            refine ⟨17374219262418315476587837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23165625683224420635450449 17374219262418315476587837)
            ·
              refine ⟨6515332223406868303720439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17374219262418315476587837 6515332223406868303720439)
              ·
                refine ⟨9772998335110302455580659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515332223406868303720439 9772998335110302455580659)
                ·
                  refine ⟨14659497502665453683370989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772998335110302455580659 14659497502665453683370989)
                  ·
                    refine ⟨5497311563499545131264121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14659497502665453683370989 5497311563499545131264121)
                    ·
                      refine ⟨4122983672624658848448091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497311563499545131264121 4122983672624658848448091)
                      ·
                        rfl

theorem cell23_8029482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_8029482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029482 prefixEnd_8029482 := by exact prefixLift 8029482
  have htrace : WordTrace (prefixWord ++ tailWord_8029482) baseStart_8029482 baseEnd_8029482 := by
    simpa [prefixWord, tailWord_8029482, baseEnd_8029482] using wordTrace_append hprefix tailTrace_8029482
  have hstable : (prefixWord ++ tailWord_8029482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029482).length < 2 ^ (prefixWord ++ tailWord_8029482).sum := by decide
  have hdescent : baseEnd_8029482 < baseStart_8029482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029508 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_8029508 : Nat := 118140960795 + 8029508 * 2 ^ 59
def prefixEnd_8029508 : Nat := 4983230072969 + 3 ^ 40 * 8029508 * 2
def baseEnd_8029508 : Nat := 4122997023121675746722971

theorem tailTrace_8029508 : CollatzResearch.WordTrace tailWord_8029508 prefixEnd_8029508 4122997023121675746722971 := by
  unfold tailWord_8029508
  simp only [CollatzResearch.WordTrace]
  refine ⟨146430108097235660817144589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195240144129647547756192785 146430108097235660817144589)
  ·
    refine ⟨54911290536463372806429221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146430108097235660817144589 54911290536463372806429221)
    ·
      refine ⟨10295866975586882401205479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54911290536463372806429221 10295866975586882401205479)
      ·
        refine ⟨15443800463380323601808219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10295866975586882401205479 15443800463380323601808219)
        ·
          refine ⟨23165700695070485402712329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15443800463380323601808219 23165700695070485402712329)
          ·
            refine ⟨17374275521302864052034247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23165700695070485402712329 17374275521302864052034247)
            ·
              refine ⟨26061413281954296078051371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374275521302864052034247 26061413281954296078051371)
              ·
                refine ⟨39092119922931444117077057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061413281954296078051371 39092119922931444117077057)
                ·
                  refine ⟨29319089942198583087807793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39092119922931444117077057 29319089942198583087807793)
                  ·
                    refine ⟨21989317456648937315855845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29319089942198583087807793 21989317456648937315855845)
                    ·
                      refine ⟨4122997023121675746722971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21989317456648937315855845 4122997023121675746722971)
                      ·
                        rfl

theorem cell23_8029508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_8029508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029508 prefixEnd_8029508 := by exact prefixLift 8029508
  have htrace : WordTrace (prefixWord ++ tailWord_8029508) baseStart_8029508 baseEnd_8029508 := by
    simpa [prefixWord, tailWord_8029508, baseEnd_8029508] using wordTrace_append hprefix tailTrace_8029508
  have hstable : (prefixWord ++ tailWord_8029508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029508).length < 2 ^ (prefixWord ++ tailWord_8029508).sum := by decide
  have hdescent : baseEnd_8029508 < baseStart_8029508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029511 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_8029511 : Nat := 118140960795 + 8029511 * 2 ^ 59
def prefixEnd_8029511 : Nat := 4983230072969 + 3 ^ 40 * 8029511 * 2
def baseEnd_8029511 : Nat := 4122998563563639234985457

theorem tailTrace_8029511 : CollatzResearch.WordTrace tailWord_8029511 prefixEnd_8029511 4122998563563639234985457 := by
  unfold tailWord_8029511
  simp only [CollatzResearch.WordTrace]
  refine ⟨292860325613460453146648387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195240217075640302097765591 292860325613460453146648387)
  ·
    refine ⟨439290488420190679719972581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292860325613460453146648387 439290488420190679719972581)
    ·
      refine ⟨82366966578785752447494859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439290488420190679719972581 82366966578785752447494859)
      ·
        refine ⟨123550449868178628671242289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82366966578785752447494859 123550449868178628671242289)
        ·
          refine ⟨92662837401133971503431717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123550449868178628671242289 92662837401133971503431717)
          ·
            refine ⟨17374282012712619656893447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92662837401133971503431717 17374282012712619656893447)
            ·
              refine ⟨26061423019068929485340171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374282012712619656893447 26061423019068929485340171)
              ·
                refine ⟨39092134528603394228010257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061423019068929485340171 39092134528603394228010257)
                ·
                  refine ⟨29319100896452545671007693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39092134528603394228010257 29319100896452545671007693)
                  ·
                    refine ⟨10994662836169704626627885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29319100896452545671007693 10994662836169704626627885)
                    ·
                      refine ⟨4122998563563639234985457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994662836169704626627885 4122998563563639234985457)
                      ·
                        rfl

theorem cell23_8029511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_8029511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029511 prefixEnd_8029511 := by exact prefixLift 8029511
  have htrace : WordTrace (prefixWord ++ tailWord_8029511) baseStart_8029511 baseEnd_8029511 := by
    simpa [prefixWord, tailWord_8029511, baseEnd_8029511] using wordTrace_append hprefix tailTrace_8029511
  have hstable : (prefixWord ++ tailWord_8029511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029511).length < 2 ^ (prefixWord ++ tailWord_8029511).sum := by decide
  have hdescent : baseEnd_8029511 < baseStart_8029511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029514 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_8029514 : Nat := 118140960795 + 8029514 * 2 ^ 59
def prefixEnd_8029514 : Nat := 4983230072969 + 3 ^ 40 * 8029514 * 2
def baseEnd_8029514 : Nat := 1374333368001867574415981

theorem tailTrace_8029514 : CollatzResearch.WordTrace tailWord_8029514 prefixEnd_8029514 1374333368001867574415981 := by
  unfold tailWord_8029514
  simp only [CollatzResearch.WordTrace]
  refine ⟨73215108758112396164751899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195240290021633056439338397 73215108758112396164751899)
  ·
    refine ⟨109822663137168594247127849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73215108758112396164751899 109822663137168594247127849)
    ·
      refine ⟨82366997352876445685345887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109822663137168594247127849 82366997352876445685345887)
      ·
        refine ⟨123550496029314668528018831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82366997352876445685345887 123550496029314668528018831)
        ·
          refine ⟨185325744043972002792028247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123550496029314668528018831 185325744043972002792028247)
          ·
            refine ⟨277988616065958004188042371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185325744043972002792028247 277988616065958004188042371)
            ·
              refine ⟨416982924098937006282063557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277988616065958004188042371 416982924098937006282063557)
              ·
                refine ⟨78184298268550688677886917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416982924098937006282063557 78184298268550688677886917)
                ·
                  refine ⟨14659555925353254127103797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78184298268550688677886917 14659555925353254127103797)
                  ·
                    refine ⟨1374333368001867574415981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14659555925353254127103797 1374333368001867574415981)
                    ·
                      rfl

theorem cell23_8029514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_8029514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029514 prefixEnd_8029514 := by exact prefixLift 8029514
  have htrace : WordTrace (prefixWord ++ tailWord_8029514) baseStart_8029514 baseEnd_8029514 := by
    simpa [prefixWord, tailWord_8029514, baseEnd_8029514] using wordTrace_append hprefix tailTrace_8029514
  have hstable : (prefixWord ++ tailWord_8029514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029514).length < 2 ^ (prefixWord ++ tailWord_8029514).sum := by decide
  have hdescent : baseEnd_8029514 < baseStart_8029514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029521 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_8029521 : Nat := 118140960795 + 8029521 * 2 ^ 59
def prefixEnd_8029521 : Nat := 4983230072969 + 3 ^ 40 * 8029521 * 2
def baseEnd_8029521 : Nat := 4123003698370184195860411

theorem tailTrace_8029521 : CollatzResearch.WordTrace tailWord_8029521 prefixEnd_8029521 4123003698370184195860411 := by
  unfold tailWord_8029521
  simp only [CollatzResearch.WordTrace]
  refine ⟨292860690343424224854512417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195240460228949483236341611 292860690343424224854512417)
  ·
    refine ⟨219645517757568168640884313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292860690343424224854512417 219645517757568168640884313)
    ·
      refine ⟨164734138318176126480663235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219645517757568168640884313 164734138318176126480663235)
      ·
        refine ⟨247101207477264189720994853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164734138318176126480663235 247101207477264189720994853)
        ·
          refine ⟨46331476401987035572686535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247101207477264189720994853 46331476401987035572686535)
          ·
            refine ⟨69497214602980553359029803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46331476401987035572686535 69497214602980553359029803)
            ·
              refine ⟨104245821904470830038544705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69497214602980553359029803 104245821904470830038544705)
              ·
                refine ⟨78184366428353122528908529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104245821904470830038544705 78184366428353122528908529)
                ·
                  refine ⟨58638274821264841896681397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78184366428353122528908529 58638274821264841896681397)
                  ·
                    refine ⟨5497338264493578927813881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58638274821264841896681397 5497338264493578927813881)
                    ·
                      refine ⟨4123003698370184195860411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497338264493578927813881 4123003698370184195860411)
                      ·
                        rfl

theorem cell23_8029521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_8029521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029521 prefixEnd_8029521 := by exact prefixLift 8029521
  have htrace : WordTrace (prefixWord ++ tailWord_8029521) baseStart_8029521 baseEnd_8029521 := by
    simpa [prefixWord, tailWord_8029521, baseEnd_8029521] using wordTrace_append hprefix tailTrace_8029521
  have hstable : (prefixWord ++ tailWord_8029521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029521).length < 2 ^ (prefixWord ++ tailWord_8029521).sum := by decide
  have hdescent : baseEnd_8029521 < baseStart_8029521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029533 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_8029533 : Nat := 118140960795 + 8029533 * 2 ^ 59
def prefixEnd_8029533 : Nat := 4983230072969 + 3 ^ 40 * 8029533 * 2
def baseEnd_8029533 : Nat := 4123009860138038148910357

theorem tailTrace_8029533 : CollatzResearch.WordTrace tailWord_8029533 prefixEnd_8029533 4123009860138038148910357 := by
  unfold tailWord_8029533
  simp only [CollatzResearch.WordTrace]
  refine ⟨292861128019380750903949253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195240752012920500602632835 292861128019380750903949253)
  ·
    refine ⟨54911461503633890794490485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292861128019380750903949253 54911461503633890794490485)
    ·
      refine ⟨5147949515965677261983483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54911461503633890794490485 5147949515965677261983483)
      ·
        refine ⟨7721924273948515892975225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147949515965677261983483 7721924273948515892975225)
        ·
          refine ⟨5791443205461386919731419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7721924273948515892975225 5791443205461386919731419)
          ·
            refine ⟨8687164808192080379597129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791443205461386919731419 8687164808192080379597129)
            ·
              refine ⟨6515373606144060284697847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687164808192080379597129 6515373606144060284697847)
              ·
                refine ⟨9773060409216090427046771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515373606144060284697847 9773060409216090427046771)
                ·
                  refine ⟨14659590613824135640570157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773060409216090427046771 14659590613824135640570157)
                  ·
                    refine ⟨5497346480184050865213809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14659590613824135640570157 5497346480184050865213809)
                    ·
                      refine ⟨4123009860138038148910357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497346480184050865213809 4123009860138038148910357)
                      ·
                        rfl

theorem cell23_8029533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_8029533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029533 prefixEnd_8029533 := by exact prefixLift 8029533
  have htrace : WordTrace (prefixWord ++ tailWord_8029533) baseStart_8029533 baseEnd_8029533 := by
    simpa [prefixWord, tailWord_8029533, baseEnd_8029533] using wordTrace_append hprefix tailTrace_8029533
  have hstable : (prefixWord ++ tailWord_8029533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029533).length < 2 ^ (prefixWord ++ tailWord_8029533).sum := by decide
  have hdescent : baseEnd_8029533 < baseStart_8029533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029551 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 4, 2]
def baseStart_8029551 : Nat := 118140960795 + 8029551 * 2 ^ 59
def prefixEnd_8029551 : Nat := 4983230072969 + 3 ^ 40 * 8029551 * 2
def baseEnd_8029551 : Nat := 4123019102789819078485273

theorem tailTrace_8029551 : CollatzResearch.WordTrace tailWord_8029551 prefixEnd_8029551 4123019102789819078485273 := by
  unfold tailWord_8029551
  simp only [CollatzResearch.WordTrace]
  refine ⟨292861784533315539978104507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195241189688877026652069671 292861784533315539978104507)
  ·
    refine ⟨439292676799973309967156761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292861784533315539978104507 439292676799973309967156761)
    ·
      refine ⟨329469507599979982475367571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439292676799973309967156761 329469507599979982475367571)
      ·
        refine ⟨494204261399969973713051357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329469507599979982475367571 494204261399969973713051357)
        ·
          refine ⟨185326598024988740142394259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494204261399969973713051357 185326598024988740142394259)
          ·
            refine ⟨277989897037483110213591389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185326598024988740142394259 277989897037483110213591389)
            ·
              refine ⟨104246211389056166330096771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277989897037483110213591389 104246211389056166330096771)
              ·
                refine ⟨156369317083584249495145157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104246211389056166330096771 156369317083584249495145157)
                ·
                  refine ⟨29319246953172046780339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156369317083584249495145157 29319246953172046780339717)
                  ·
                    refine ⟨5497358803719758771313697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29319246953172046780339717 5497358803719758771313697)
                    ·
                      refine ⟨4123019102789819078485273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497358803719758771313697 4123019102789819078485273)
                      ·
                        rfl

theorem cell23_8029551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4, 2].length) (baseStart_8029551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029551 prefixEnd_8029551 := by exact prefixLift 8029551
  have htrace : WordTrace (prefixWord ++ tailWord_8029551) baseStart_8029551 baseEnd_8029551 := by
    simpa [prefixWord, tailWord_8029551, baseEnd_8029551] using wordTrace_append hprefix tailTrace_8029551
  have hstable : (prefixWord ++ tailWord_8029551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029551).length < 2 ^ (prefixWord ++ tailWord_8029551).sum := by decide
  have hdescent : baseEnd_8029551 < baseStart_8029551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029561 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_8029561 : Nat := 118140960795 + 8029561 * 2 ^ 59
def prefixEnd_8029561 : Nat := 4983230072969 + 3 ^ 40 * 8029561 * 2
def baseEnd_8029561 : Nat := 1374341412532121346453409

theorem tailTrace_8029561 : CollatzResearch.WordTrace tailWord_8029561 prefixEnd_8029561 1374341412532121346453409 := by
  unfold tailWord_8029561
  simp only [CollatzResearch.WordTrace]
  refine ⟨292862149263279311685968537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195241432842186207790645691 292862149263279311685968537)
  ·
    refine ⟨219646611947459483764476403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292862149263279311685968537 219646611947459483764476403)
    ·
      refine ⟨329469917921189225646714605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219646611947459483764476403 329469917921189225646714605)
      ·
        refine ⟨123551219220445959617517977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329469917921189225646714605 123551219220445959617517977)
        ·
          refine ⟨92663414415334469713138483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123551219220445959617517977 92663414415334469713138483)
          ·
            refine ⟨138995121623001704569707725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92663414415334469713138483 138995121623001704569707725)
            ·
              refine ⟨52123170608625639213640397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138995121623001704569707725 52123170608625639213640397)
              ·
                refine ⟨19546188978234614705115149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52123170608625639213640397 19546188978234614705115149)
                ·
                  refine ⟨7329820866837980514418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19546188978234614705115149 7329820866837980514418181)
                  ·
                    refine ⟨1374341412532121346453409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7329820866837980514418181 1374341412532121346453409)
                    ·
                      rfl

theorem cell23_8029561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_8029561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029561 prefixEnd_8029561 := by exact prefixLift 8029561
  have htrace : WordTrace (prefixWord ++ tailWord_8029561) baseStart_8029561 baseEnd_8029561 := by
    simpa [prefixWord, tailWord_8029561, baseEnd_8029561] using wordTrace_append hprefix tailTrace_8029561
  have hstable : (prefixWord ++ tailWord_8029561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029561).length < 2 ^ (prefixWord ++ tailWord_8029561).sum := by decide
  have hdescent : baseEnd_8029561 < baseStart_8029561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029564 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_8029564 : Nat := 118140960795 + 8029564 * 2 ^ 59
def prefixEnd_8029564 : Nat := 4983230072969 + 3 ^ 40 * 8029564 * 2
def baseEnd_8029564 : Nat := 4123025778038327527622713

theorem tailTrace_8029564 : CollatzResearch.WordTrace tailWord_8029564 prefixEnd_8029564 4123025778038327527622713 := by
  unfold tailWord_8029564
  simp only [CollatzResearch.WordTrace]
  refine ⟨146431129341134221599163873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195241505788178962132218497 146431129341134221599163873)
  ·
    refine ⟨109823347005850666199372905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146431129341134221599163873 109823347005850666199372905)
    ·
      refine ⟨82367510254387999649529679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109823347005850666199372905 82367510254387999649529679)
      ·
        refine ⟨123551265381581999474294519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82367510254387999649529679 123551265381581999474294519)
        ·
          refine ⟨185326898072372999211441779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123551265381581999474294519 185326898072372999211441779)
          ·
            refine ⟨277990347108559498817162669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185326898072372999211441779 277990347108559498817162669)
            ·
              refine ⟨104246380165709812056436001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277990347108559498817162669 104246380165709812056436001)
              ·
                refine ⟨78184785124282359042327001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104246380165709812056436001 78184785124282359042327001)
                ·
                  refine ⟨58638588843211769281745251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78184785124282359042327001 58638588843211769281745251)
                  ·
                    refine ⟨87957883264817653922617877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58638588843211769281745251 87957883264817653922617877)
                    ·
                      refine ⟨4123025778038327527622713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87957883264817653922617877 4123025778038327527622713)
                      ·
                        rfl

theorem cell23_8029564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_8029564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029564 prefixEnd_8029564 := by exact prefixLift 8029564
  have htrace : WordTrace (prefixWord ++ tailWord_8029564) baseStart_8029564 baseEnd_8029564 := by
    simpa [prefixWord, tailWord_8029564, baseEnd_8029564] using wordTrace_append hprefix tailTrace_8029564
  have hstable : (prefixWord ++ tailWord_8029564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029564).length < 2 ^ (prefixWord ++ tailWord_8029564).sum := by decide
  have hdescent : baseEnd_8029564 < baseStart_8029564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029571 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3]
def baseStart_8029571 : Nat := 118140960795 + 8029571 * 2 ^ 59
def prefixEnd_8029571 : Nat := 4983230072969 + 3 ^ 40 * 8029571 * 2
def baseEnd_8029571 : Nat := 4123029372402909000235181

theorem tailTrace_8029571 : CollatzResearch.WordTrace tailWord_8029571 prefixEnd_8029571 4123029372402909000235181 := by
  unfold tailWord_8029571
  simp only [CollatzResearch.WordTrace]
  refine ⟨292862513993243083393832567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195241675995495388929221711 292862513993243083393832567)
  ·
    refine ⟨439293770989864625090748851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292862513993243083393832567 439293770989864625090748851)
    ·
      refine ⟨658940656484796937636123277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439293770989864625090748851 658940656484796937636123277)
      ·
        refine ⟨247102746181798851613546229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 658940656484796937636123277 247102746181798851613546229)
        ·
          refine ⟨23165882454543642338769959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247102746181798851613546229 23165882454543642338769959)
          ·
            refine ⟨34748823681815463508154939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23165882454543642338769959 34748823681815463508154939)
            ·
              refine ⟨52123235522723195262232409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34748823681815463508154939 52123235522723195262232409)
              ·
                refine ⟨39092426642042396446674307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52123235522723195262232409 39092426642042396446674307)
                ·
                  refine ⟨58638639963063594670011461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39092426642042396446674307 58638639963063594670011461)
                  ·
                    refine ⟨10994744993074424000627149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58638639963063594670011461 10994744993074424000627149)
                    ·
                      refine ⟨4123029372402909000235181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994744993074424000627149 4123029372402909000235181)
                      ·
                        rfl

theorem cell23_8029571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_8029571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029571 prefixEnd_8029571 := by exact prefixLift 8029571
  have htrace : WordTrace (prefixWord ++ tailWord_8029571) baseStart_8029571 baseEnd_8029571 := by
    simpa [prefixWord, tailWord_8029571, baseEnd_8029571] using wordTrace_append hprefix tailTrace_8029571
  have hstable : (prefixWord ++ tailWord_8029571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029571).length < 2 ^ (prefixWord ++ tailWord_8029571).sum := by decide
  have hdescent : baseEnd_8029571 < baseStart_8029571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029588 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_8029588 : Nat := 118140960795 + 8029588 * 2 ^ 59
def prefixEnd_8029588 : Nat := 4983230072969 + 3 ^ 40 * 8029588 * 2
def baseEnd_8029588 : Nat := 4123038101574035433722603

theorem tailTrace_8029588 : CollatzResearch.WordTrace tailWord_8029588 prefixEnd_8029588 4123038101574035433722603 := by
  unfold tailWord_8029588
  simp only [CollatzResearch.WordTrace]
  refine ⟨146431567017090747648600709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195242089356120996864800945 146431567017090747648600709)
  ·
    refine ⟨27455918815704515184112633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146431567017090747648600709 27455918815704515184112633)
    ·
      refine ⟨20591939111778386388084475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27455918815704515184112633 20591939111778386388084475)
      ·
        refine ⟨30887908667667579582126713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591939111778386388084475 30887908667667579582126713)
        ·
          refine ⟨23165931500750684686595035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30887908667667579582126713 23165931500750684686595035)
          ·
            refine ⟨34748897251126027029892553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23165931500750684686595035 34748897251126027029892553)
            ·
              refine ⟨26061672938344520272419415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34748897251126027029892553 26061672938344520272419415)
              ·
                refine ⟨39092509407516780408629123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061672938344520272419415 39092509407516780408629123)
                ·
                  refine ⟨58638764111275170612943685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39092509407516780408629123 58638764111275170612943685)
                  ·
                    refine ⟨10994768270864094489926941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58638764111275170612943685 10994768270864094489926941)
                    ·
                      refine ⟨4123038101574035433722603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994768270864094489926941 4123038101574035433722603)
                      ·
                        rfl

theorem cell23_8029588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_8029588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029588 prefixEnd_8029588 := by exact prefixLift 8029588
  have htrace : WordTrace (prefixWord ++ tailWord_8029588) baseStart_8029588 baseEnd_8029588 := by
    simpa [prefixWord, tailWord_8029588, baseEnd_8029588] using wordTrace_append hprefix tailTrace_8029588
  have hstable : (prefixWord ++ tailWord_8029588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029588).length < 2 ^ (prefixWord ++ tailWord_8029588).sum := by decide
  have hdescent : baseEnd_8029588 < baseStart_8029588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029618 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_8029618 : Nat := 118140960795 + 8029618 * 2 ^ 59
def prefixEnd_8029618 : Nat := 4983230072969 + 3 ^ 40 * 8029618 * 2
def baseEnd_8029618 : Nat := 4123053505993670316347465

theorem tailTrace_8029618 : CollatzResearch.WordTrace tailWord_8029618 prefixEnd_8029618 4123053505993670316347465 := by
  unfold tailWord_8029618
  simp only [CollatzResearch.WordTrace]
  refine ⟨73216057056018202605198377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195242818816048540280529005 73216057056018202605198377)
  ·
    refine ⟨54912042792013651953898783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73216057056018202605198377 54912042792013651953898783)
    ·
      refine ⟨82368064188020477930848175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54912042792013651953898783 82368064188020477930848175)
      ·
        refine ⟨123552096282030716896272263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82368064188020477930848175 123552096282030716896272263)
        ·
          refine ⟨185328144423046075344408395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123552096282030716896272263 185328144423046075344408395)
          ·
            refine ⟨277992216634569113016612593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185328144423046075344408395 277992216634569113016612593)
            ·
              refine ⟨208494162475926834762459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277992216634569113016612593 208494162475926834762459445)
              ·
                refine ⟨19546327732118140758980573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208494162475926834762459445 19546327732118140758980573)
                ·
                  refine ⟨7329872899544302784617715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19546327732118140758980573 7329872899544302784617715)
                  ·
                    refine ⟨10994809349316454176926573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329872899544302784617715 10994809349316454176926573)
                    ·
                      refine ⟨4123053505993670316347465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994809349316454176926573 4123053505993670316347465)
                      ·
                        rfl

theorem cell23_8029618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_8029618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029618 prefixEnd_8029618 := by exact prefixLift 8029618
  have htrace : WordTrace (prefixWord ++ tailWord_8029618) baseStart_8029618 baseEnd_8029618 := by
    simpa [prefixWord, tailWord_8029618, baseEnd_8029618] using wordTrace_append hprefix tailTrace_8029618
  have hstable : (prefixWord ++ tailWord_8029618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029618).length < 2 ^ (prefixWord ++ tailWord_8029618).sum := by decide
  have hdescent : baseEnd_8029618 < baseStart_8029618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029625 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 6]
def baseStart_8029625 : Nat := 118140960795 + 8029625 * 2 ^ 59
def prefixEnd_8029625 : Nat := 4983230072969 + 3 ^ 40 * 8029625 * 2
def baseEnd_8029625 : Nat := 458117455595361309884437

theorem tailTrace_8029625 : CollatzResearch.WordTrace tailWord_8029625 prefixEnd_8029625 458117455595361309884437 := by
  unfold tailWord_8029625
  simp only [CollatzResearch.WordTrace]
  refine ⟨292864483535047450616298329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195242989023364967077532219 292864483535047450616298329)
  ·
    refine ⟨219648362651285587962223747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292864483535047450616298329 219648362651285587962223747)
    ·
      refine ⟨329472543976928381943335621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219648362651285587962223747 329472543976928381943335621)
      ·
        refine ⟨61776101995674071614375429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329472543976928381943335621 61776101995674071614375429)
        ·
          refine ⟨11583019124188888427695393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61776101995674071614375429 11583019124188888427695393)
          ·
            refine ⟨8687264343141666320771545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583019124188888427695393 8687264343141666320771545)
            ·
              refine ⟨6515448257356249740578659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687264343141666320771545 6515448257356249740578659)
              ·
                refine ⟨9773172386034374610867989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515448257356249740578659 9773172386034374610867989)
                ·
                  refine ⟨458117455595361309884437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9773172386034374610867989 458117455595361309884437)
                  ·
                    rfl

theorem cell23_8029625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_8029625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029625 prefixEnd_8029625 := by exact prefixLift 8029625
  have htrace : WordTrace (prefixWord ++ tailWord_8029625) baseStart_8029625 baseEnd_8029625 := by
    simpa [prefixWord, tailWord_8029625, baseEnd_8029625] using wordTrace_append hprefix tailTrace_8029625
  have hstable : (prefixWord ++ tailWord_8029625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029625).length < 2 ^ (prefixWord ++ tailWord_8029625).sum := by decide
  have hdescent : baseEnd_8029625 < baseStart_8029625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029669 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_8029669 : Nat := 118140960795 + 8029669 * 2 ^ 59
def prefixEnd_8029669 : Nat := 4983230072969 + 3 ^ 40 * 8029669 * 2
def baseEnd_8029669 : Nat := 4123079693507049616809731

theorem tailTrace_8029669 : CollatzResearch.WordTrace tailWord_8029669 prefixEnd_8029669 4123079693507049616809731 := by
  unfold tailWord_8029669
  simp only [CollatzResearch.WordTrace]
  refine ⟨292866088346888046130900061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195244058897925364087266707 292866088346888046130900061)
  ·
    refine ⟨109824783130083017299087523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292866088346888046130900061 109824783130083017299087523)
    ·
      refine ⟨164737174695124525948631285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109824783130083017299087523 164737174695124525948631285)
      ·
        refine ⟨15444110127667924307684183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164737174695124525948631285 15444110127667924307684183)
        ·
          refine ⟨23166165191501886461526275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444110127667924307684183 23166165191501886461526275)
          ·
            refine ⟨34749247787252829692289413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23166165191501886461526275 34749247787252829692289413)
            ·
              refine ⟨6515483960109905567304265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34749247787252829692289413 6515483960109905567304265)
              ·
                refine ⟨4886612970082429175478199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515483960109905567304265 4886612970082429175478199)
                ·
                  refine ⟨7329919455123643763217299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886612970082429175478199 7329919455123643763217299)
                  ·
                    refine ⟨10994879182685465644825949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329919455123643763217299 10994879182685465644825949)
                    ·
                      refine ⟨4123079693507049616809731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994879182685465644825949 4123079693507049616809731)
                      ·
                        rfl

theorem cell23_8029669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_8029669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029669 prefixEnd_8029669 := by exact prefixLift 8029669
  have htrace : WordTrace (prefixWord ++ tailWord_8029669) baseStart_8029669 baseEnd_8029669 := by
    simpa [prefixWord, tailWord_8029669, baseEnd_8029669] using wordTrace_append hprefix tailTrace_8029669
  have hstable : (prefixWord ++ tailWord_8029669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029669).length < 2 ^ (prefixWord ++ tailWord_8029669).sum := by decide
  have hdescent : baseEnd_8029669 < baseStart_8029669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029678 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_8029678 : Nat := 118140960795 + 8029678 * 2 ^ 59
def prefixEnd_8029678 : Nat := 4983230072969 + 3 ^ 40 * 8029678 * 2
def baseEnd_8029678 : Nat := 4123084314832940081597189

theorem tailTrace_8029678 : CollatzResearch.WordTrace tailWord_8029678 prefixEnd_8029678 4123084314832940081597189 := by
  unfold tailWord_8029678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608302075481930083497211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195244277735903627111985125 36608302075481930083497211)
  ·
    refine ⟨54912453113222895125245817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36608302075481930083497211 54912453113222895125245817)
    ·
      refine ⟨41184339834917171343934363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54912453113222895125245817 41184339834917171343934363)
      ·
        refine ⟨61776509752375757015901545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41184339834917171343934363 61776509752375757015901545)
        ·
          refine ⟨46332382314281817761926159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61776509752375757015901545 46332382314281817761926159)
          ·
            refine ⟨69498573471422726642889239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46332382314281817761926159 69498573471422726642889239)
            ·
              refine ⟨104247860207134089964333859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69498573471422726642889239 104247860207134089964333859)
              ·
                refine ⟨156371790310701134946500789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104247860207134089964333859 156371790310701134946500789)
                ·
                  refine ⟨14659855341628231401234449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156371790310701134946500789 14659855341628231401234449)
                  ·
                    refine ⟨10994891506221173550925837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14659855341628231401234449 10994891506221173550925837)
                    ·
                      refine ⟨4123084314832940081597189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994891506221173550925837 4123084314832940081597189)
                      ·
                        rfl

theorem cell23_8029678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_8029678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029678 prefixEnd_8029678 := by exact prefixLift 8029678
  have htrace : WordTrace (prefixWord ++ tailWord_8029678) baseStart_8029678 baseEnd_8029678 := by
    simpa [prefixWord, tailWord_8029678, baseEnd_8029678] using wordTrace_append hprefix tailTrace_8029678
  have hstable : (prefixWord ++ tailWord_8029678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029678).length < 2 ^ (prefixWord ++ tailWord_8029678).sum := by decide
  have hdescent : baseEnd_8029678 < baseStart_8029678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029681 : List Nat := [1, 2, 2, 2, 3, 2, 3, 8]
def baseStart_8029681 : Nat := 118140960795 + 8029681 * 2 ^ 59
def prefixEnd_8029681 : Nat := 4983230072969 + 3 ^ 40 * 8029681 * 2
def baseEnd_8029681 : Nat := 152706883528700132217025

theorem tailTrace_8029681 : CollatzResearch.WordTrace tailWord_8029681 prefixEnd_8029681 152706883528700132217025 := by
  unfold tailWord_8029681
  simp only [CollatzResearch.WordTrace]
  refine ⟨292866526022844572180336897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195244350681896381453557931 292866526022844572180336897)
  ·
    refine ⟨219649894517133429135252673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292866526022844572180336897 219649894517133429135252673)
    ·
      refine ⟨164737420887850071851439505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219649894517133429135252673 164737420887850071851439505)
      ·
        refine ⟨123553065665887553888579629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164737420887850071851439505 123553065665887553888579629)
        ·
          refine ⟨46332399624707832708217361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123553065665887553888579629 46332399624707832708217361)
          ·
            refine ⟨34749299718530874531163021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46332399624707832708217361 34749299718530874531163021)
            ·
              refine ⟨13030987394449077949186133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34749299718530874531163021 13030987394449077949186133)
              ·
                refine ⟨152706883528700132217025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13030987394449077949186133 152706883528700132217025)
                ·
                  rfl

theorem cell23_8029681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 8].length) (baseStart_8029681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029681 prefixEnd_8029681 := by exact prefixLift 8029681
  have htrace : WordTrace (prefixWord ++ tailWord_8029681) baseStart_8029681 baseEnd_8029681 := by
    simpa [prefixWord, tailWord_8029681, baseEnd_8029681] using wordTrace_append hprefix tailTrace_8029681
  have hstable : (prefixWord ++ tailWord_8029681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029681).length < 2 ^ (prefixWord ++ tailWord_8029681).sum := by decide
  have hdescent : baseEnd_8029681 < baseStart_8029681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029685 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_8029685 : Nat := 118140960795 + 8029685 * 2 ^ 59
def prefixEnd_8029685 : Nat := 4983230072969 + 3 ^ 40 * 8029685 * 2
def baseEnd_8029685 : Nat := 1374362636399173851403219

theorem tailTrace_8029685 : CollatzResearch.WordTrace tailWord_8029685 prefixEnd_8029685 1374362636399173851403219 := by
  unfold tailWord_8029685
  simp only [CollatzResearch.WordTrace]
  refine ⟨292866671914830080863482509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195244447943220053908988339 292866671914830080863482509)
  ·
    refine ⟨109825001968061280323805941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292866671914830080863482509 109825001968061280323805941)
    ·
      refine ⟨10296093934505745030356807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109825001968061280323805941 10296093934505745030356807)
      ·
        refine ⟨15444140901758617545535211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296093934505745030356807 15444140901758617545535211)
        ·
          refine ⟨23166211352637926318302817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444140901758617545535211 23166211352637926318302817)
          ·
            refine ⟨17374658514478444738727113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23166211352637926318302817 17374658514478444738727113)
            ·
              refine ⟨13030993885858833554045335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17374658514478444738727113 13030993885858833554045335)
              ·
                refine ⟨19546490828788250331068003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030993885858833554045335 19546490828788250331068003)
                ·
                  refine ⟨29319736243182375496602005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19546490828788250331068003 29319736243182375496602005)
                  ·
                    refine ⟨1374362636399173851403219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29319736243182375496602005 1374362636399173851403219)
                    ·
                      rfl

theorem cell23_8029685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_8029685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029685 prefixEnd_8029685 := by exact prefixLift 8029685
  have htrace : WordTrace (prefixWord ++ tailWord_8029685) baseStart_8029685 baseEnd_8029685 := by
    simpa [prefixWord, tailWord_8029685, baseEnd_8029685] using wordTrace_append hprefix tailTrace_8029685
  have hstable : (prefixWord ++ tailWord_8029685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029685).length < 2 ^ (prefixWord ++ tailWord_8029685).sum := by decide
  have hdescent : baseEnd_8029685 < baseStart_8029685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029688 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_8029688 : Nat := 118140960795 + 8029688 * 2 ^ 59
def prefixEnd_8029688 : Nat := 4983230072969 + 3 ^ 40 * 8029688 * 2
def baseEnd_8029688 : Nat := 4123089449639485042472143

theorem tailTrace_8029688 : CollatzResearch.WordTrace tailWord_8029688 prefixEnd_8029688 4123089449639485042472143 := by
  unfold tailWord_8029688
  simp only [CollatzResearch.WordTrace]
  refine ⟨146433390666909606187920859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195244520889212808250561145 146433390666909606187920859)
  ·
    refine ⟨219650086000364409281881289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146433390666909606187920859 219650086000364409281881289)
    ·
      refine ⟨164737564500273306961410967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219650086000364409281881289 164737564500273306961410967)
      ·
        refine ⟨247106346750409960442116451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164737564500273306961410967 247106346750409960442116451)
        ·
          refine ⟨370659520125614940663174677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247106346750409960442116451 370659520125614940663174677)
          ·
            refine ⟨17374665005888200343586313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 370659520125614940663174677 17374665005888200343586313)
            ·
              refine ⟨13030998754416150257689735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17374665005888200343586313 13030998754416150257689735)
              ·
                refine ⟨19546498131624225386534603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030998754416150257689735 19546498131624225386534603)
                ·
                  refine ⟨29319747197436338079801905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19546498131624225386534603 29319747197436338079801905)
                  ·
                    refine ⟨21989810398077253559851429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29319747197436338079801905 21989810398077253559851429)
                    ·
                      refine ⟨4123089449639485042472143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21989810398077253559851429 4123089449639485042472143)
                      ·
                        rfl

theorem cell23_8029688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_8029688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029688 prefixEnd_8029688 := by exact prefixLift 8029688
  have htrace : WordTrace (prefixWord ++ tailWord_8029688) baseStart_8029688 baseEnd_8029688 := by
    simpa [prefixWord, tailWord_8029688, baseEnd_8029688] using wordTrace_append hprefix tailTrace_8029688
  have hstable : (prefixWord ++ tailWord_8029688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029688).length < 2 ^ (prefixWord ++ tailWord_8029688).sum := by decide
  have hdescent : baseEnd_8029688 < baseStart_8029688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029691 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3]
def baseStart_8029691 : Nat := 118140960795 + 8029691 * 2 ^ 59
def prefixEnd_8029691 : Nat := 4983230072969 + 3 ^ 40 * 8029691 * 2
def baseEnd_8029691 : Nat := 4123090990081448530734629

theorem tailTrace_8029691 : CollatzResearch.WordTrace tailWord_8029691 prefixEnd_8029691 4123090990081448530734629 := by
  unfold tailWord_8029691
  simp only [CollatzResearch.WordTrace]
  refine ⟨292866890752808343888200927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195244593835205562592133951 292866890752808343888200927)
  ·
    refine ⟨439300336129212515832301391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292866890752808343888200927 439300336129212515832301391)
    ·
      refine ⟨658950504193818773748452087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439300336129212515832301391 658950504193818773748452087)
      ·
        refine ⟨988425756290728160622678131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658950504193818773748452087 988425756290728160622678131)
        ·
          refine ⟨1482638634436092240934017197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988425756290728160622678131 1482638634436092240934017197)
          ·
            refine ⟨555989487913534590350256449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1482638634436092240934017197 555989487913534590350256449)
            ·
              refine ⟨416992115935150942762692337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555989487913534590350256449 416992115935150942762692337)
              ·
                refine ⟨312744086951363207072019253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416992115935150942762692337 312744086951363207072019253)
                ·
                  refine ⟨29319758151690300663001805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312744086951363207072019253 29319758151690300663001805)
                  ·
                    refine ⟨10994909306883862748625677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29319758151690300663001805 10994909306883862748625677)
                    ·
                      refine ⟨4123090990081448530734629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994909306883862748625677 4123090990081448530734629)
                      ·
                        rfl

theorem cell23_8029691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].length) (baseStart_8029691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029691 prefixEnd_8029691 := by exact prefixLift 8029691
  have htrace : WordTrace (prefixWord ++ tailWord_8029691) baseStart_8029691 baseEnd_8029691 := by
    simpa [prefixWord, tailWord_8029691, baseEnd_8029691] using wordTrace_append hprefix tailTrace_8029691
  have hstable : (prefixWord ++ tailWord_8029691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029691).length < 2 ^ (prefixWord ++ tailWord_8029691).sum := by decide
  have hdescent : baseEnd_8029691 < baseStart_8029691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029709 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_8029709 : Nat := 118140960795 + 8029709 * 2 ^ 59
def prefixEnd_8029709 : Nat := 4983230072969 + 3 ^ 40 * 8029709 * 2
def baseEnd_8029709 : Nat := 4123100232733229460309547

theorem tailTrace_8029709 : CollatzResearch.WordTrace tailWord_8029709 prefixEnd_8029709 4123100232733229460309547 := by
  unfold tailWord_8029709
  simp only [CollatzResearch.WordTrace]
  refine ⟨292867547266743132962356181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195245031511162088641570787 292867547266743132962356181)
  ·
    refine ⟨6864083139064292178805223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 292867547266743132962356181 6864083139064292178805223)
    ·
      refine ⟨10296124708596438268207835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864083139064292178805223 10296124708596438268207835)
      ·
        refine ⟨15444187062894657402311753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296124708596438268207835 15444187062894657402311753)
        ·
          refine ⟨11583140297170993051733815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15444187062894657402311753 11583140297170993051733815)
          ·
            refine ⟨17374710445756489577600723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583140297170993051733815 17374710445756489577600723)
            ·
              refine ⟨26062065668634734366401085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374710445756489577600723 26062065668634734366401085)
              ·
                refine ⟨9773274625738025387400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26062065668634734366401085 9773274625738025387400407)
                ·
                  refine ⟨14659911938607038081100611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773274625738025387400407 14659911938607038081100611)
                  ·
                    refine ⟨21989867907910557121650917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14659911938607038081100611 21989867907910557121650917)
                    ·
                      refine ⟨4123100232733229460309547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21989867907910557121650917 4123100232733229460309547)
                      ·
                        rfl

theorem cell23_8029709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_8029709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029709 prefixEnd_8029709 := by exact prefixLift 8029709
  have htrace : WordTrace (prefixWord ++ tailWord_8029709) baseStart_8029709 baseEnd_8029709 := by
    simpa [prefixWord, tailWord_8029709, baseEnd_8029709] using wordTrace_append hprefix tailTrace_8029709
  have hstable : (prefixWord ++ tailWord_8029709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029709).length < 2 ^ (prefixWord ++ tailWord_8029709).sum := by decide
  have hdescent : baseEnd_8029709 < baseStart_8029709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029725 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_8029725 : Nat := 118140960795 + 8029725 * 2 ^ 59
def prefixEnd_8029725 : Nat := 4983230072969 + 3 ^ 40 * 8029725 * 2
def baseEnd_8029725 : Nat := 4123108448423701397709473

theorem tailTrace_8029725 : CollatzResearch.WordTrace tailWord_8029725 prefixEnd_8029725 4123108448423701397709473 := by
  unfold tailWord_8029725
  simp only [CollatzResearch.WordTrace]
  refine ⟨292868130834685167694938629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195245420556456778463292419 292868130834685167694938629)
  ·
    refine ⟨54912774531503468942800993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292868130834685167694938629 54912774531503468942800993)
    ·
      refine ⟨41184580898627601707100745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54912774531503468942800993 41184580898627601707100745)
      ·
        refine ⟨30888435673970701280325559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41184580898627601707100745 30888435673970701280325559)
        ·
          refine ⟨46332653510956051920488339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30888435673970701280325559 46332653510956051920488339)
          ·
            refine ⟨69498980266434077880732509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46332653510956051920488339 69498980266434077880732509)
            ·
              refine ⟨26062117599912779205274691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69498980266434077880732509 26062117599912779205274691)
              ·
                refine ⟨39093176399869168807912037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26062117599912779205274691 39093176399869168807912037)
                ·
                  refine ⟨7329970574975469151483507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39093176399869168807912037 7329970574975469151483507)
                  ·
                    refine ⟨10994955862463203727225261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329970574975469151483507 10994955862463203727225261)
                    ·
                      refine ⟨4123108448423701397709473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994955862463203727225261 4123108448423701397709473)
                      ·
                        rfl

theorem cell23_8029725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_8029725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029725 prefixEnd_8029725 := by exact prefixLift 8029725
  have htrace : WordTrace (prefixWord ++ tailWord_8029725) baseStart_8029725 baseEnd_8029725 := by
    simpa [prefixWord, tailWord_8029725, baseEnd_8029725] using wordTrace_append hprefix tailTrace_8029725
  have hstable : (prefixWord ++ tailWord_8029725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029725).length < 2 ^ (prefixWord ++ tailWord_8029725).sum := by decide
  have hdescent : baseEnd_8029725 < baseStart_8029725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029742 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_8029742 : Nat := 118140960795 + 8029742 * 2 ^ 59
def prefixEnd_8029742 : Nat := 4983230072969 + 3 ^ 40 * 8029742 * 2
def baseEnd_8029742 : Nat := 4123117177594827831196895

theorem tailTrace_8029742 : CollatzResearch.WordTrace tailWord_8029742 prefixEnd_8029742 4123117177594827831196895 := by
  unfold tailWord_8029742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608593859452947449788435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195245833917082386398871653 36608593859452947449788435)
  ·
    refine ⟨54912890789179421174682653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36608593859452947449788435 54912890789179421174682653)
    ·
      refine ⟨20592334045942282940505995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54912890789179421174682653 20592334045942282940505995)
      ·
        refine ⟨30888501068913424410758993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20592334045942282940505995 30888501068913424410758993)
        ·
          refine ⟨23166375801685068308069245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30888501068913424410758993 23166375801685068308069245)
          ·
            refine ⟨8687390925631900615525967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23166375801685068308069245 8687390925631900615525967)
            ·
              refine ⟨13031086388447850923288951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687390925631900615525967 13031086388447850923288951)
              ·
                refine ⟨19546629582671776384933427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13031086388447850923288951 19546629582671776384933427)
                ·
                  refine ⟨29319944374007664577400141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19546629582671776384933427 29319944374007664577400141)
                  ·
                    refine ⟨10994979140252874216525053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29319944374007664577400141 10994979140252874216525053)
                    ·
                      refine ⟨4123117177594827831196895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10994979140252874216525053 4123117177594827831196895)
                      ·
                        rfl

theorem cell23_8029742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_8029742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029742 prefixEnd_8029742 := by exact prefixLift 8029742
  have htrace : WordTrace (prefixWord ++ tailWord_8029742) baseStart_8029742 baseEnd_8029742 := by
    simpa [prefixWord, tailWord_8029742, baseEnd_8029742] using wordTrace_append hprefix tailTrace_8029742
  have hstable : (prefixWord ++ tailWord_8029742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029742).length < 2 ^ (prefixWord ++ tailWord_8029742).sum := by decide
  have hdescent : baseEnd_8029742 < baseStart_8029742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029752 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_8029752 : Nat := 118140960795 + 8029752 * 2 ^ 59
def prefixEnd_8029752 : Nat := 4983230072969 + 3 ^ 40 * 8029752 * 2
def baseEnd_8029752 : Nat := 4123122312401372792071849

theorem tailTrace_8029752 : CollatzResearch.WordTrace tailWord_8029752 prefixEnd_8029752 4123122312401372792071849 := by
  unfold tailWord_8029752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146434557802793675653085755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195246077070391567537447673 146434557802793675653085755)
  ·
    refine ⟨219651836704190513479628633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146434557802793675653085755 219651836704190513479628633)
    ·
      refine ⟨164738877528142885109721475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219651836704190513479628633 164738877528142885109721475)
      ·
        refine ⟨247108316292214327664582213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164738877528142885109721475 247108316292214327664582213)
        ·
          refine ⟨46332809304790186437109165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247108316292214327664582213 46332809304790186437109165)
          ·
            refine ⟨17374803489296319913915937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46332809304790186437109165 17374803489296319913915937)
            ·
              refine ⟨13031102616972239935436953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17374803489296319913915937 13031102616972239935436953)
              ·
                refine ⟨9773326962729179951577715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13031102616972239935436953 9773326962729179951577715)
                ·
                  refine ⟨14659990444093769927366573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773326962729179951577715 14659990444093769927366573)
                  ·
                    refine ⟨5497496416535163722762465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14659990444093769927366573 5497496416535163722762465)
                    ·
                      refine ⟨4123122312401372792071849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497496416535163722762465 4123122312401372792071849)
                      ·
                        rfl

theorem cell23_8029752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_8029752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029752 prefixEnd_8029752 := by exact prefixLift 8029752
  have htrace : WordTrace (prefixWord ++ tailWord_8029752) baseStart_8029752 baseEnd_8029752 := by
    simpa [prefixWord, tailWord_8029752, baseEnd_8029752] using wordTrace_append hprefix tailTrace_8029752
  have hstable : (prefixWord ++ tailWord_8029752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029752).length < 2 ^ (prefixWord ++ tailWord_8029752).sum := by decide
  have hdescent : baseEnd_8029752 < baseStart_8029752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029765 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_8029765 : Nat := 118140960795 + 8029765 * 2 ^ 59
def prefixEnd_8029765 : Nat := 4983230072969 + 3 ^ 40 * 8029765 * 2
def baseEnd_8029765 : Nat := 4123128987649881241209289

theorem tailTrace_8029765 : CollatzResearch.WordTrace tailWord_8029765 prefixEnd_8029765 4123128987649881241209289 := by
  unfold tailWord_8029765
  simp only [CollatzResearch.WordTrace]
  refine ⟨292869589754540254526394749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195246393169693503017596499 292869589754540254526394749)
  ·
    refine ⟨109826096157952595447398031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292869589754540254526394749 109826096157952595447398031)
    ·
      refine ⟨164739144236928893171097047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109826096157952595447398031 164739144236928893171097047)
      ·
        refine ⟨247108716355393339756645571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164739144236928893171097047 247108716355393339756645571)
        ·
          refine ⟨370663074533090009634968357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247108716355393339756645571 370663074533090009634968357)
          ·
            refine ⟨69499326474954376806556567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370663074533090009634968357 69499326474954376806556567)
            ·
              refine ⟨104248989712431565209834851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69499326474954376806556567 104248989712431565209834851)
              ·
                refine ⟨156373484568647347814752277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104248989712431565209834851 156373484568647347814752277)
                ·
                  refine ⟨7330007089155344428816513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156373484568647347814752277 7330007089155344428816513)
                  ·
                    refine ⟨5497505316866508321612385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330007089155344428816513 5497505316866508321612385)
                    ·
                      refine ⟨4123128987649881241209289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497505316866508321612385 4123128987649881241209289)
                      ·
                        rfl

theorem cell23_8029765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_8029765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029765 prefixEnd_8029765 := by exact prefixLift 8029765
  have htrace : WordTrace (prefixWord ++ tailWord_8029765) baseStart_8029765 baseEnd_8029765 := by
    simpa [prefixWord, tailWord_8029765, baseEnd_8029765] using wordTrace_append hprefix tailTrace_8029765
  have hstable : (prefixWord ++ tailWord_8029765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029765).length < 2 ^ (prefixWord ++ tailWord_8029765).sum := by decide
  have hdescent : baseEnd_8029765 < baseStart_8029765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_8029781 : Nat := 118140960795 + 8029781 * 2 ^ 59
def prefixEnd_8029781 : Nat := 4983230072969 + 3 ^ 40 * 8029781 * 2
def baseEnd_8029781 : Nat := 4123137203340353178609215

theorem tailTrace_8029781 : CollatzResearch.WordTrace tailWord_8029781 prefixEnd_8029781 4123137203340353178609215 := by
  unfold tailWord_8029781
  simp only [CollatzResearch.WordTrace]
  refine ⟨292870173322482289258977197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195246782214988192839318131 292870173322482289258977197)
  ·
    refine ⟨109826314995930858472116449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292870173322482289258977197 109826314995930858472116449)
    ·
      refine ⟨82369736246948143854087337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109826314995930858472116449 82369736246948143854087337)
      ·
        refine ⟨61777302185211107890565503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82369736246948143854087337 61777302185211107890565503)
        ·
          refine ⟨92665953277816661835848255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61777302185211107890565503 92665953277816661835848255)
          ·
            refine ⟨138998929916724992753772383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92665953277816661835848255 138998929916724992753772383)
            ·
              refine ⟨208498394875087489130658575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138998929916724992753772383 208498394875087489130658575)
              ·
                refine ⟨312747592312631233695987863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208498394875087489130658575 312747592312631233695987863)
                ·
                  refine ⟨469121388468946850543981795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312747592312631233695987863 469121388468946850543981795)
                  ·
                    refine ⟨703682082703420275815972693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 469121388468946850543981795 703682082703420275815972693)
                    ·
                      refine ⟨4123137203340353178609215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 703682082703420275815972693 4123137203340353178609215)
                      ·
                        rfl

theorem cell23_8029781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_8029781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029781 prefixEnd_8029781 := by exact prefixLift 8029781
  have htrace : WordTrace (prefixWord ++ tailWord_8029781) baseStart_8029781 baseEnd_8029781 := by
    simpa [prefixWord, tailWord_8029781, baseEnd_8029781] using wordTrace_append hprefix tailTrace_8029781
  have hstable : (prefixWord ++ tailWord_8029781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029781).length < 2 ^ (prefixWord ++ tailWord_8029781).sum := by decide
  have hdescent : baseEnd_8029781 < baseStart_8029781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029799 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_8029799 : Nat := 118140960795 + 8029799 * 2 ^ 59
def prefixEnd_8029799 : Nat := 4983230072969 + 3 ^ 40 * 8029799 * 2
def baseEnd_8029799 : Nat := 4123146445992134108184133

theorem tailTrace_8029799 : CollatzResearch.WordTrace tailWord_8029799 prefixEnd_8029799 4123146445992134108184133 := by
  unfold tailWord_8029799
  simp only [CollatzResearch.WordTrace]
  refine ⟨292870829836417078333132451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195247219890944718888754967 292870829836417078333132451)
  ·
    refine ⟨439306244754625617499698677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292870829836417078333132451 439306244754625617499698677)
    ·
      refine ⟨41184960445746151640596751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439306244754625617499698677 41184960445746151640596751)
      ·
        refine ⟨61777440668619227460895127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41184960445746151640596751 61777440668619227460895127)
        ·
          refine ⟨92666161002928841191342691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61777440668619227460895127 92666161002928841191342691)
          ·
            refine ⟨138999241504393261787014037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92666161002928841191342691 138999241504393261787014037)
            ·
              refine ⟨6515589445518434146266283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138999241504393261787014037 6515589445518434146266283)
              ·
                refine ⟨9773384168277651219399425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515589445518434146266283 9773384168277651219399425)
                ·
                  refine ⟨7330038126208238414549569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9773384168277651219399425 7330038126208238414549569)
                  ·
                    refine ⟨5497528594656178810912177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330038126208238414549569 5497528594656178810912177)
                    ·
                      refine ⟨4123146445992134108184133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497528594656178810912177 4123146445992134108184133)
                      ·
                        rfl

theorem cell23_8029799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_8029799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029799 prefixEnd_8029799 := by exact prefixLift 8029799
  have htrace : WordTrace (prefixWord ++ tailWord_8029799) baseStart_8029799 baseEnd_8029799 := by
    simpa [prefixWord, tailWord_8029799, baseEnd_8029799] using wordTrace_append hprefix tailTrace_8029799
  have hstable : (prefixWord ++ tailWord_8029799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029799).length < 2 ^ (prefixWord ++ tailWord_8029799).sum := by decide
  have hdescent : baseEnd_8029799 < baseStart_8029799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029801 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_8029801 : Nat := 118140960795 + 8029801 * 2 ^ 59
def prefixEnd_8029801 : Nat := 4983230072969 + 3 ^ 40 * 8029801 * 2
def baseEnd_8029801 : Nat := 1374382490984481033453041

theorem tailTrace_8029801 : CollatzResearch.WordTrace tailWord_8029801 prefixEnd_8029801 1374382490984481033453041 := by
  unfold tailWord_8029801
  simp only [CollatzResearch.WordTrace]
  refine ⟨292870902782409832674705257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195247268521606555116470171 292870902782409832674705257)
  ·
    refine ⟨219653177086807374506028943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292870902782409832674705257 219653177086807374506028943)
    ·
      refine ⟨329479765630211061759043415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219653177086807374506028943 329479765630211061759043415)
      ·
        refine ⟨494219648445316592638565123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329479765630211061759043415 494219648445316592638565123)
        ·
          refine ⟨741329472667974888957847685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494219648445316592638565123 741329472667974888957847685)
          ·
            refine ⟨138999276125245291679596441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741329472667974888957847685 138999276125245291679596441)
            ·
              refine ⟨104249457093933968759697331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138999276125245291679596441 104249457093933968759697331)
              ·
                refine ⟨156374185640900953139545997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104249457093933968759697331 156374185640900953139545997)
                ·
                  refine ⟨58640319615337857427329749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156374185640900953139545997 58640319615337857427329749)
                  ·
                    refine ⟨1374382490984481033453041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58640319615337857427329749 1374382490984481033453041)
                    ·
                      rfl

theorem cell23_8029801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_8029801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029801 prefixEnd_8029801 := by exact prefixLift 8029801
  have htrace : WordTrace (prefixWord ++ tailWord_8029801) baseStart_8029801 baseEnd_8029801 := by
    simpa [prefixWord, tailWord_8029801, baseEnd_8029801] using wordTrace_append hprefix tailTrace_8029801
  have hstable : (prefixWord ++ tailWord_8029801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029801).length < 2 ^ (prefixWord ++ tailWord_8029801).sum := by decide
  have hdescent : baseEnd_8029801 < baseStart_8029801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029882 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_8029882 : Nat := 118140960795 + 8029882 * 2 ^ 59
def prefixEnd_8029882 : Nat := 4983230072969 + 3 ^ 40 * 8029882 * 2
def baseEnd_8029882 : Nat := 1374396354962152427815417

theorem tailTrace_8029882 : CollatzResearch.WordTrace tailWord_8029882 prefixEnd_8029882 1374396354962152427815417 := by
  unfold tailWord_8029882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73218464273779095877100975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195249238063410922338935933 73218464273779095877100975)
  ·
    refine ⟨109827696410668643815651463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73218464273779095877100975 109827696410668643815651463)
    ·
      refine ⟨164741544616002965723477195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109827696410668643815651463 164741544616002965723477195)
      ·
        refine ⟨247112316924004448585215793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164741544616002965723477195 247112316924004448585215793)
        ·
          refine ⟨185334237693003336438911845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247112316924004448585215793 185334237693003336438911845)
          ·
            refine ⟨34750169567438125582295971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185334237693003336438911845 34750169567438125582295971)
            ·
              refine ⟨52125254351157188373443957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34750169567438125582295971 52125254351157188373443957)
              ·
                refine ⟨4886742595420986410010371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52125254351157188373443957 4886742595420986410010371)
                ·
                  refine ⟨7330113893131479615015557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886742595420986410010371 7330113893131479615015557)
                  ·
                    refine ⟨1374396354962152427815417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330113893131479615015557 1374396354962152427815417)
                    ·
                      rfl

theorem cell23_8029882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_8029882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029882 prefixEnd_8029882 := by exact prefixLift 8029882
  have htrace : WordTrace (prefixWord ++ tailWord_8029882) baseStart_8029882 baseEnd_8029882 := by
    simpa [prefixWord, tailWord_8029882, baseEnd_8029882] using wordTrace_append hprefix tailTrace_8029882
  have hstable : (prefixWord ++ tailWord_8029882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029882).length < 2 ^ (prefixWord ++ tailWord_8029882).sum := by decide
  have hdescent : baseEnd_8029882 < baseStart_8029882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029939 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 1, 1, 3]
def baseStart_8029939 : Nat := 118140960795 + 8029939 * 2 ^ 59
def prefixEnd_8029939 : Nat := 4983230072969 + 3 ^ 40 * 8029939 * 2
def baseEnd_8029939 : Nat := 4123218333283763560433489

theorem tailTrace_8029939 : CollatzResearch.WordTrace tailWord_8029939 prefixEnd_8029939 4123218333283763560433489 := by
  unfold tailWord_8029939
  simp only [CollatzResearch.WordTrace]
  refine ⟨292875936055909882243228871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195250624037273254828819247 292875936055909882243228871)
  ·
    refine ⟨439313904083864823364843307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292875936055909882243228871 439313904083864823364843307)
    ·
      refine ⟨658970856125797235047264961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439313904083864823364843307 658970856125797235047264961)
      ·
        refine ⟨494228142094347926285448721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658970856125797235047264961 494228142094347926285448721)
        ·
          refine ⟨370671106570760944714086541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494228142094347926285448721 370671106570760944714086541)
          ·
            refine ⟨139001664964035354267782453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370671106570760944714086541 139001664964035354267782453)
            ·
              refine ⟨13031406090378314462604605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139001664964035354267782453 13031406090378314462604605)
              ·
                refine ⟨4886777283891867923476727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13031406090378314462604605 4886777283891867923476727)
                ·
                  refine ⟨7330165925837801885215091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886777283891867923476727 7330165925837801885215091)
                  ·
                    refine ⟨10995248888756702827822637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7330165925837801885215091 10995248888756702827822637)
                    ·
                      refine ⟨4123218333283763560433489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995248888756702827822637 4123218333283763560433489)
                      ·
                        rfl

theorem cell23_8029939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 1, 3].length) (baseStart_8029939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029939 prefixEnd_8029939 := by exact prefixLift 8029939
  have htrace : WordTrace (prefixWord ++ tailWord_8029939) baseStart_8029939 baseEnd_8029939 := by
    simpa [prefixWord, tailWord_8029939, baseEnd_8029939] using wordTrace_append hprefix tailTrace_8029939
  have hstable : (prefixWord ++ tailWord_8029939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029939).length < 2 ^ (prefixWord ++ tailWord_8029939).sum := by decide
  have hdescent : baseEnd_8029939 < baseStart_8029939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029942 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_8029942 : Nat := 118140960795 + 8029942 * 2 ^ 59
def prefixEnd_8029942 : Nat := 4983230072969 + 3 ^ 40 * 8029942 * 2
def baseEnd_8029942 : Nat := 1374406624575242349565325

theorem tailTrace_8029942 : CollatzResearch.WordTrace tailWord_8029942 prefixEnd_8029942 1374406624575242349565325 := by
  unfold tailWord_8029942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304752842181188359724255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195250696983266009170392053 18304752842181188359724255)
  ·
    refine ⟨27457129263271782539586383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18304752842181188359724255 27457129263271782539586383)
    ·
      refine ⟨41185693894907673809379575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27457129263271782539586383 41185693894907673809379575)
      ·
        refine ⟨61778540842361510714069363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41185693894907673809379575 61778540842361510714069363)
        ·
          refine ⟨92667811263542266071104045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61778540842361510714069363 92667811263542266071104045)
          ·
            refine ⟨34750429223828349776664017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92667811263542266071104045 34750429223828349776664017)
            ·
              refine ⟨26062821917871262332498013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34750429223828349776664017 26062821917871262332498013)
              ·
                refine ⟨9773558219201723374686755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26062821917871262332498013 9773558219201723374686755)
                ·
                  refine ⟨14660337328802585062030133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773558219201723374686755 14660337328802585062030133)
                  ·
                    refine ⟨1374406624575242349565325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14660337328802585062030133 1374406624575242349565325)
                    ·
                      rfl

theorem cell23_8029942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_8029942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029942 prefixEnd_8029942 := by exact prefixLift 8029942
  have htrace : WordTrace (prefixWord ++ tailWord_8029942) baseStart_8029942 baseEnd_8029942 := by
    simpa [prefixWord, tailWord_8029942, baseEnd_8029942] using wordTrace_append hprefix tailTrace_8029942
  have hstable : (prefixWord ++ tailWord_8029942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029942).length < 2 ^ (prefixWord ++ tailWord_8029942).sum := by decide
  have hdescent : baseEnd_8029942 < baseStart_8029942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
