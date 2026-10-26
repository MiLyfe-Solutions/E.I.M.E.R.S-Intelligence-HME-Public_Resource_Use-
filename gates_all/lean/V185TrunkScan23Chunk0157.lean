import V185TrunkScan23Chunk0156

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_928269 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_928269 : Nat := 118140960795 + 928269 * 2 ^ 59
def prefixEnd_928269 : Nat := 4983230072969 + 3 ^ 40 * 928269 * 2
def baseEnd_928269 : Nat := 476648173668533876968475

theorem tailTrace_928269 : CollatzResearch.WordTrace tailWord_928269 prefixEnd_928269 476648173668533876968475 := by
  unfold tailWord_928269
  simp only [CollatzResearch.WordTrace]
  refine ⟨33856751874047423568635861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571167916031615712423907 33856751874047423568635861)
  ·
    refine ⟨793517622047986489889903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33856751874047423568635861 793517622047986489889903)
    ·
      refine ⟨1190276433071979734834855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793517622047986489889903 1190276433071979734834855)
      ·
        refine ⟨1785414649607969602252283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190276433071979734834855 1785414649607969602252283)
        ·
          refine ⟨2678121974411954403378425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785414649607969602252283 2678121974411954403378425)
          ·
            refine ⟨2008591480808965802533819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678121974411954403378425 2008591480808965802533819)
            ·
              refine ⟨3012887221213448703800729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008591480808965802533819 3012887221213448703800729)
              ·
                refine ⟨2259665415910086527850547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012887221213448703800729 2259665415910086527850547)
                ·
                  refine ⟨3389498123865129791775821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259665415910086527850547 3389498123865129791775821)
                  ·
                    refine ⟨1271061796449423671915933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389498123865129791775821 1271061796449423671915933)
                    ·
                      refine ⟨476648173668533876968475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271061796449423671915933 476648173668533876968475)
                      ·
                        rfl

theorem cell23_928269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_928269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928269 prefixEnd_928269 := by exact prefixLift 928269
  have htrace : WordTrace (prefixWord ++ tailWord_928269) baseStart_928269 baseEnd_928269 := by
    simpa [prefixWord, tailWord_928269, baseEnd_928269] using wordTrace_append hprefix tailTrace_928269
  have hstable : (prefixWord ++ tailWord_928269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928269).length < 2 ^ (prefixWord ++ tailWord_928269).sum := by decide
  have hdescent : baseEnd_928269 < baseStart_928269 := by decide
  rcases family_descends (prefixWord ++ tailWord_928269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928275 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 4, 2]
def baseStart_928275 : Nat := 118140960795 + 928275 * 2 ^ 59
def prefixEnd_928275 : Nat := 4983230072969 + 3 ^ 40 * 928275 * 2
def baseEnd_928275 : Nat := 476651254552460853493447

theorem tailTrace_928275 : CollatzResearch.WordTrace tailWord_928275 prefixEnd_928275 476651254552460853493447 := by
  unfold tailWord_928275
  simp only [CollatzResearch.WordTrace]
  refine ⟨33856970712025686593354279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571313808017124395569519 33856970712025686593354279)
  ·
    refine ⟨50785456068038529890031419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33856970712025686593354279 50785456068038529890031419)
    ·
      refine ⟨76178184102057794835047129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50785456068038529890031419 76178184102057794835047129)
      ·
        refine ⟨57133638076543346126285347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76178184102057794835047129 57133638076543346126285347)
        ·
          refine ⟨85700457114815019189428021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57133638076543346126285347 85700457114815019189428021)
          ·
            refine ⟨8034417854513908049008877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85700457114815019189428021 8034417854513908049008877)
            ·
              refine ⟨3012906695442715518378329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8034417854513908049008877 3012906695442715518378329)
              ·
                refine ⟨2259680021582036638783747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012906695442715518378329 2259680021582036638783747)
                ·
                  refine ⟨3389520032373054958175621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259680021582036638783747 3389520032373054958175621)
                  ·
                    refine ⟨635535006069947804657929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389520032373054958175621 635535006069947804657929)
                    ·
                      refine ⟨476651254552460853493447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635535006069947804657929 476651254552460853493447)
                      ·
                        rfl

theorem cell23_928275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4, 2].length) (baseStart_928275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928275 prefixEnd_928275 := by exact prefixLift 928275
  have htrace : WordTrace (prefixWord ++ tailWord_928275) baseStart_928275 baseEnd_928275 := by
    simpa [prefixWord, tailWord_928275, baseEnd_928275] using wordTrace_append hprefix tailTrace_928275
  have hstable : (prefixWord ++ tailWord_928275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928275).length < 2 ^ (prefixWord ++ tailWord_928275).sum := by decide
  have hdescent : baseEnd_928275 < baseStart_928275 := by decide
  rcases family_descends (prefixWord ++ tailWord_928275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928281 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 9]
def baseStart_928281 : Nat := 118140960795 + 928281 * 2 ^ 59
def prefixEnd_928281 : Nat := 4983230072969 + 3 ^ 40 * 928281 * 2
def baseEnd_928281 : Nat := 52961592826265314446491

theorem tailTrace_928281 : CollatzResearch.WordTrace tailWord_928281 prefixEnd_928281 52961592826265314446491 := by
  unfold tailWord_928281
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857189550003949618072697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571459700002633078715131 33857189550003949618072697)
  ·
    refine ⟨25392892162502962213554523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33857189550003949618072697 25392892162502962213554523)
    ·
      refine ⟨38089338243754443320331785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25392892162502962213554523 38089338243754443320331785)
      ·
        refine ⟨28567003682815832490248839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38089338243754443320331785 28567003682815832490248839)
        ·
          refine ⟨42850505524223748735373259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28567003682815832490248839 42850505524223748735373259)
          ·
            refine ⟨64275758286335623103059889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42850505524223748735373259 64275758286335623103059889)
            ·
              refine ⟨48206818714751717327294917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64275758286335623103059889 48206818714751717327294917)
              ·
                refine ⟨9038778509015946998867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48206818714751717327294917 9038778509015946998867797)
                ·
                  refine ⟨52961592826265314446491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9038778509015946998867797 52961592826265314446491)
                  ·
                    rfl

theorem cell23_928281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_928281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928281 prefixEnd_928281 := by exact prefixLift 928281
  have htrace : WordTrace (prefixWord ++ tailWord_928281) baseStart_928281 baseEnd_928281 := by
    simpa [prefixWord, tailWord_928281, baseEnd_928281] using wordTrace_append hprefix tailTrace_928281
  have hstable : (prefixWord ++ tailWord_928281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928281).length < 2 ^ (prefixWord ++ tailWord_928281).sum := by decide
  have hdescent : baseEnd_928281 < baseStart_928281 := by decide
  rcases family_descends (prefixWord ++ tailWord_928281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928365 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_928365 : Nat := 118140960795 + 928365 * 2 ^ 59
def prefixEnd_928365 : Nat := 4983230072969 + 3 ^ 40 * 928365 * 2
def baseEnd_928365 : Nat := 476697467811365501368033

theorem tailTrace_928365 : CollatzResearch.WordTrace tailWord_928365 prefixEnd_928365 476697467811365501368033 := by
  unfold tailWord_928365
  simp only [CollatzResearch.WordTrace]
  refine ⟨33860253281699631964130549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22573502187799754642753699 33860253281699631964130549)
  ·
    refine ⟨3174398745159340496637239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33860253281699631964130549 3174398745159340496637239)
    ·
      refine ⟨4761598117739010744955859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174398745159340496637239 4761598117739010744955859)
      ·
        refine ⟨7142397176608516117433789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761598117739010744955859 7142397176608516117433789)
        ·
          refine ⟨2678398941228193544037671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7142397176608516117433789 2678398941228193544037671)
          ·
            refine ⟨4017598411842290316056507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678398941228193544037671 4017598411842290316056507)
            ·
              refine ⟨6026397617763435474084761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017598411842290316056507 6026397617763435474084761)
              ·
                refine ⟨4519798213322576605563571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026397617763435474084761 4519798213322576605563571)
                ·
                  refine ⟨6779697319983864908345357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519798213322576605563571 6779697319983864908345357)
                  ·
                    refine ⟨2542386494993949340629509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6779697319983864908345357 2542386494993949340629509)
                    ·
                      refine ⟨476697467811365501368033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2542386494993949340629509 476697467811365501368033)
                      ·
                        rfl

theorem cell23_928365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_928365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928365 prefixEnd_928365 := by exact prefixLift 928365
  have htrace : WordTrace (prefixWord ++ tailWord_928365) baseStart_928365 baseEnd_928365 := by
    simpa [prefixWord, tailWord_928365, baseEnd_928365] using wordTrace_append hprefix tailTrace_928365
  have hstable : (prefixWord ++ tailWord_928365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928365).length < 2 ^ (prefixWord ++ tailWord_928365).sum := by decide
  have hdescent : baseEnd_928365 < baseStart_928365 := by decide
  rcases family_descends (prefixWord ++ tailWord_928365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928375 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 3, 4]
def baseStart_928375 : Nat := 118140960795 + 928375 * 2 ^ 59
def prefixEnd_928375 : Nat := 4983230072969 + 3 ^ 40 * 928375 * 2
def baseEnd_928375 : Nat := 158900867539303487414329

theorem tailTrace_928375 : CollatzResearch.WordTrace tailWord_928375 prefixEnd_928375 158900867539303487414329 := by
  unfold tailWord_928375
  simp only [CollatzResearch.WordTrace]
  refine ⟨33860618011663403671994579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22573745341108935781329719 33860618011663403671994579)
  ·
    refine ⟨50790927017495105507991869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33860618011663403671994579 50790927017495105507991869)
    ·
      refine ⟨19046597631560664565496951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50790927017495105507991869 19046597631560664565496951)
      ·
        refine ⟨28569896447340996848245427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046597631560664565496951 28569896447340996848245427)
        ·
          refine ⟨42854844671011495272368141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28569896447340996848245427 42854844671011495272368141)
          ·
            refine ⟨16070566751629310727138053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42854844671011495272368141 16070566751629310727138053)
            ·
              refine ⟨3013231265930495761338385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16070566751629310727138053 3013231265930495761338385)
              ·
                refine ⟨2259923449447871821003789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013231265930495761338385 2259923449447871821003789)
                ·
                  refine ⟨847471293542951932876421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2259923449447871821003789 847471293542951932876421)
                  ·
                    refine ⟨158900867539303487414329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847471293542951932876421 158900867539303487414329)
                    ·
                      rfl

theorem cell23_928375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_928375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928375 prefixEnd_928375 := by exact prefixLift 928375
  have htrace : WordTrace (prefixWord ++ tailWord_928375) baseStart_928375 baseEnd_928375 := by
    simpa [prefixWord, tailWord_928375, baseEnd_928375] using wordTrace_append hprefix tailTrace_928375
  have hstable : (prefixWord ++ tailWord_928375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928375).length < 2 ^ (prefixWord ++ tailWord_928375).sum := by decide
  have hdescent : baseEnd_928375 < baseStart_928375 := by decide
  rcases family_descends (prefixWord ++ tailWord_928375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928385 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_928385 : Nat := 118140960795 + 928385 * 2 ^ 59
def prefixEnd_928385 : Nat := 4983230072969 + 3 ^ 40 * 928385 * 2
def baseEnd_928385 : Nat := 476707737424455423117941

theorem tailTrace_928385 : CollatzResearch.WordTrace tailWord_928385 prefixEnd_928385 476707737424455423117941 := by
  unfold tailWord_928385
  simp only [CollatzResearch.WordTrace]
  refine ⟨33860982741627175379858609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22573988494418116919905739 33860982741627175379858609)
  ·
    refine ⟨25395737056220381534893957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33860982741627175379858609 25395737056220381534893957)
    ·
      refine ⟨4761700698041321537792617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25395737056220381534893957 4761700698041321537792617)
      ·
        refine ⟨3571275523530991153344463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761700698041321537792617 3571275523530991153344463)
        ·
          refine ⟨5356913285296486730016695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571275523530991153344463 5356913285296486730016695)
          ·
            refine ⟨8035369927944730095025043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356913285296486730016695 8035369927944730095025043)
            ·
              refine ⟨12053054891917095142537565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035369927944730095025043 12053054891917095142537565)
              ·
                refine ⟨4519895584468910678451587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12053054891917095142537565 4519895584468910678451587)
                ·
                  refine ⟨6779843376703366017677381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519895584468910678451587 6779843376703366017677381)
                  ·
                    refine ⟨1271220633131881128314509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779843376703366017677381 1271220633131881128314509)
                    ·
                      refine ⟨476707737424455423117941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271220633131881128314509 476707737424455423117941)
                      ·
                        rfl

theorem cell23_928385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_928385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928385 prefixEnd_928385 := by exact prefixLift 928385
  have htrace : WordTrace (prefixWord ++ tailWord_928385) baseStart_928385 baseEnd_928385 := by
    simpa [prefixWord, tailWord_928385, baseEnd_928385] using wordTrace_append hprefix tailTrace_928385
  have hstable : (prefixWord ++ tailWord_928385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928385).length < 2 ^ (prefixWord ++ tailWord_928385).sum := by decide
  have hdescent : baseEnd_928385 < baseStart_928385 := by decide
  rcases family_descends (prefixWord ++ tailWord_928385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928402 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_928402 : Nat := 118140960795 + 928402 * 2 ^ 59
def prefixEnd_928402 : Nat := 4983230072969 + 3 ^ 40 * 928402 * 2
def baseEnd_928402 : Nat := 476716466595581856605363

theorem tailTrace_928402 : CollatzResearch.WordTrace tailWord_928402 prefixEnd_928402 476716466595581856605363 := by
  unfold tailWord_928402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465400695641396820806865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22574401855043724855484973 8465400695641396820806865)
  ·
    refine ⟨6349050521731047615605149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8465400695641396820806865 6349050521731047615605149)
    ·
      refine ⟨2380893945649142855851931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6349050521731047615605149 2380893945649142855851931)
      ·
        refine ⟨3571340918473714283777897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380893945649142855851931 3571340918473714283777897)
        ·
          refine ⟨2678505688855285712833423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571340918473714283777897 2678505688855285712833423)
          ·
            refine ⟨4017758533282928569250135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678505688855285712833423 4017758533282928569250135)
            ·
              refine ⟨6026637799924392853875203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017758533282928569250135 6026637799924392853875203)
              ·
                refine ⟨9039956699886589280812805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026637799924392853875203 9039956699886589280812805)
                ·
                  refine ⟨1694991881228735490152401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9039956699886589280812805 1694991881228735490152401)
                  ·
                    refine ⟨1271243910921551617614301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694991881228735490152401 1271243910921551617614301)
                    ·
                      refine ⟨476716466595581856605363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271243910921551617614301 476716466595581856605363)
                      ·
                        rfl

theorem cell23_928402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_928402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928402 prefixEnd_928402 := by exact prefixLift 928402
  have htrace : WordTrace (prefixWord ++ tailWord_928402) baseStart_928402 baseEnd_928402 := by
    simpa [prefixWord, tailWord_928402, baseEnd_928402] using wordTrace_append hprefix tailTrace_928402
  have hstable : (prefixWord ++ tailWord_928402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928402).length < 2 ^ (prefixWord ++ tailWord_928402).sum := by decide
  have hdescent : baseEnd_928402 < baseStart_928402 := by decide
  rcases family_descends (prefixWord ++ tailWord_928402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928409 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 1, 4]
def baseStart_928409 : Nat := 118140960795 + 928409 * 2 ^ 59
def prefixEnd_928409 : Nat := 4983230072969 + 3 ^ 40 * 928409 * 2
def baseEnd_928409 : Nat := 158906686986721109739277

theorem tailTrace_928409 : CollatzResearch.WordTrace tailWord_928409 prefixEnd_928409 158906686986721109739277 := by
  unfold tailWord_928409
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861858093540227478732281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22574572062360151652488187 33861858093540227478732281)
  ·
    refine ⟨25396393570155170609049211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33861858093540227478732281 25396393570155170609049211)
    ·
      refine ⟨38094590355232755913573817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25396393570155170609049211 38094590355232755913573817)
      ·
        refine ⟨28570942766424566935180363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38094590355232755913573817 28570942766424566935180363)
        ·
          refine ⟨42856414149636850402770545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28570942766424566935180363 42856414149636850402770545)
          ·
            refine ⟨32142310612227637802077909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42856414149636850402770545 32142310612227637802077909)
            ·
              refine ⟨753335404974085260986201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32142310612227637802077909 753335404974085260986201)
              ·
                refine ⟨565001553730563945739651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753335404974085260986201 565001553730563945739651)
                ·
                  refine ⟨847502330595845918609477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565001553730563945739651 847502330595845918609477)
                  ·
                    refine ⟨158906686986721109739277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847502330595845918609477 158906686986721109739277)
                    ·
                      rfl

theorem cell23_928409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_928409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928409 prefixEnd_928409 := by exact prefixLift 928409
  have htrace : WordTrace (prefixWord ++ tailWord_928409) baseStart_928409 baseEnd_928409 := by
    simpa [prefixWord, tailWord_928409, baseEnd_928409] using wordTrace_append hprefix tailTrace_928409
  have hstable : (prefixWord ++ tailWord_928409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928409).length < 2 ^ (prefixWord ++ tailWord_928409).sum := by decide
  have hdescent : baseEnd_928409 < baseStart_928409 := by decide
  rcases family_descends (prefixWord ++ tailWord_928409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928435 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 3, 5]
def baseStart_928435 : Nat := 118140960795 + 928435 * 2 ^ 59
def prefixEnd_928435 : Nat := 4983230072969 + 3 ^ 40 * 928435 * 2
def baseEnd_928435 : Nat := 158911137152393409164237

theorem tailTrace_928435 : CollatzResearch.WordTrace tailWord_928435 prefixEnd_928435 158911137152393409164237 := by
  unfold tailWord_928435
  simp only [CollatzResearch.WordTrace]
  refine ⟨33862806391446033919178759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22575204260964022612785839 33862806391446033919178759)
  ·
    refine ⟨50794209587169050878768139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33862806391446033919178759 50794209587169050878768139)
    ·
      refine ⟨76191314380753576318152209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50794209587169050878768139 76191314380753576318152209)
      ·
        refine ⟨57143485785565182238614157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76191314380753576318152209 57143485785565182238614157)
        ·
          refine ⟨21428807169586943339480309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57143485785565182238614157 21428807169586943339480309)
          ·
            refine ⟨2008950672148775938076279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21428807169586943339480309 2008950672148775938076279)
            ·
              refine ⟨3013426008223163907114419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008950672148775938076279 3013426008223163907114419)
              ·
                refine ⟨4520139012334745860671629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013426008223163907114419 4520139012334745860671629)
                ·
                  refine ⟨1695052129625529697751861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4520139012334745860671629 1695052129625529697751861)
                  ·
                    refine ⟨158911137152393409164237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1695052129625529697751861 158911137152393409164237)
                    ·
                      rfl

theorem cell23_928435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].length) (baseStart_928435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928435 prefixEnd_928435 := by exact prefixLift 928435
  have htrace : WordTrace (prefixWord ++ tailWord_928435) baseStart_928435 baseEnd_928435 := by
    simpa [prefixWord, tailWord_928435, baseEnd_928435] using wordTrace_append hprefix tailTrace_928435
  have hstable : (prefixWord ++ tailWord_928435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928435).length < 2 ^ (prefixWord ++ tailWord_928435).sum := by decide
  have hdescent : baseEnd_928435 < baseStart_928435 := by decide
  rcases family_descends (prefixWord ++ tailWord_928435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928492 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_928492 : Nat := 118140960795 + 928492 * 2 ^ 59
def prefixEnd_928492 : Nat := 4983230072969 + 3 ^ 40 * 928492 * 2
def baseEnd_928492 : Nat := 476762679854486504479949

theorem tailTrace_928492 : CollatzResearch.WordTrace tailWord_928492 prefixEnd_928492 476762679854486504479949 := by
  unfold tailWord_928492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932442676119766327001865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22576590234826355102669153 16932442676119766327001865)
  ·
    refine ⟨12699332007089824745251399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16932442676119766327001865 12699332007089824745251399)
    ·
      refine ⟨19048998010634737117877099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699332007089824745251399 19048998010634737117877099)
      ·
        refine ⟨28573497015952105676815649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048998010634737117877099 28573497015952105676815649)
        ·
          refine ⟨21430122761964079257611737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28573497015952105676815649 21430122761964079257611737)
          ·
            refine ⟨16072592071473059443208803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21430122761964079257611737 16072592071473059443208803)
            ·
              refine ⟨24108888107209589164813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16072592071473059443208803 24108888107209589164813205)
              ·
                refine ⟨1130104130025449492100619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24108888107209589164813205 1130104130025449492100619)
                ·
                  refine ⟨1695156195038174238150929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130104130025449492100619 1695156195038174238150929)
                  ·
                    refine ⟨1271367146278630678613197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695156195038174238150929 1271367146278630678613197)
                    ·
                      refine ⟨476762679854486504479949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271367146278630678613197 476762679854486504479949)
                      ·
                        rfl

theorem cell23_928492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_928492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928492 prefixEnd_928492 := by exact prefixLift 928492
  have htrace : WordTrace (prefixWord ++ tailWord_928492) baseStart_928492 baseEnd_928492 := by
    simpa [prefixWord, tailWord_928492, baseEnd_928492] using wordTrace_append hprefix tailTrace_928492
  have hstable : (prefixWord ++ tailWord_928492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928492).length < 2 ^ (prefixWord ++ tailWord_928492).sum := by decide
  have hdescent : baseEnd_928492 < baseStart_928492 := by decide
  rcases family_descends (prefixWord ++ tailWord_928492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928502 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_928502 : Nat := 118140960795 + 928502 * 2 ^ 59
def prefixEnd_928502 : Nat := 4983230072969 + 3 ^ 40 * 928502 * 2
def baseEnd_928502 : Nat := 476767814661031465354903

theorem tailTrace_928502 : CollatzResearch.WordTrace tailWord_928502 prefixEnd_928502 476767814661031465354903 := by
  unfold tailWord_928502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116578130137706522616735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22576833388135536241245173 2116578130137706522616735)
  ·
    refine ⟨3174867195206559783925103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116578130137706522616735 3174867195206559783925103)
    ·
      refine ⟨4762300792809839675887655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174867195206559783925103 4762300792809839675887655)
      ·
        refine ⟨7143451189214759513831483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762300792809839675887655 7143451189214759513831483)
        ·
          refine ⟨10715176783822139270747225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143451189214759513831483 10715176783822139270747225)
          ·
            refine ⟨8036382587866604453060419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10715176783822139270747225 8036382587866604453060419)
            ·
              refine ⟨12054573881799906679590629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036382587866604453060419 12054573881799906679590629)
              ·
                refine ⟨2260232602837482502423243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12054573881799906679590629 2260232602837482502423243)
                ·
                  refine ⟨3390348904256223753634865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260232602837482502423243 3390348904256223753634865)
                  ·
                    refine ⟨2542761678192167815226149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3390348904256223753634865 2542761678192167815226149)
                    ·
                      refine ⟨476767814661031465354903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2542761678192167815226149 476767814661031465354903)
                      ·
                        rfl

theorem cell23_928502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_928502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928502 prefixEnd_928502 := by exact prefixLift 928502
  have htrace : WordTrace (prefixWord ++ tailWord_928502) baseStart_928502 baseEnd_928502 := by
    simpa [prefixWord, tailWord_928502, baseEnd_928502] using wordTrace_append hprefix tailTrace_928502
  have hstable : (prefixWord ++ tailWord_928502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928502).length < 2 ^ (prefixWord ++ tailWord_928502).sum := by decide
  have hdescent : baseEnd_928502 < baseStart_928502 := by decide
  rcases family_descends (prefixWord ++ tailWord_928502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928506 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_928506 : Nat := 118140960795 + 928506 * 2 ^ 59
def prefixEnd_928506 : Nat := 4983230072969 + 3 ^ 40 * 928506 * 2
def baseEnd_928506 : Nat := 476769868583649449704885

theorem tailTrace_928506 : CollatzResearch.WordTrace tailWord_928506 prefixEnd_928506 476769868583649449704885 := by
  unfold tailWord_928506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466348993547203261253343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22576930649459208696675581 8466348993547203261253343)
  ·
    refine ⟨12699523490320804891880015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8466348993547203261253343 12699523490320804891880015)
    ·
      refine ⟨19049285235481207337820023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699523490320804891880015 19049285235481207337820023)
      ·
        refine ⟨28573927853221811006730035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19049285235481207337820023 28573927853221811006730035)
        ·
          refine ⟨42860891779832716510095053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28573927853221811006730035 42860891779832716510095053)
          ·
            refine ⟨16072834417437268691285645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42860891779832716510095053 16072834417437268691285645)
            ·
              refine ⟨6027312906538975759232117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16072834417437268691285645 6027312906538975759232117)
              ·
                refine ⟨565060584988028977428011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6027312906538975759232117 565060584988028977428011)
                ·
                  refine ⟨847590877482043466142017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565060584988028977428011 847590877482043466142017)
                  ·
                    refine ⟨635693158111532599606513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 847590877482043466142017 635693158111532599606513)
                    ·
                      refine ⟨476769868583649449704885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635693158111532599606513 476769868583649449704885)
                      ·
                        rfl

theorem cell23_928506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_928506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928506 prefixEnd_928506 := by exact prefixLift 928506
  have htrace : WordTrace (prefixWord ++ tailWord_928506) baseStart_928506 baseEnd_928506 := by
    simpa [prefixWord, tailWord_928506, baseEnd_928506] using wordTrace_append hprefix tailTrace_928506
  have hstable : (prefixWord ++ tailWord_928506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928506).length < 2 ^ (prefixWord ++ tailWord_928506).sum := by decide
  have hdescent : baseEnd_928506 < baseStart_928506 := by decide
  rcases family_descends (prefixWord ++ tailWord_928506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928579 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 4, 2, 2]
def baseStart_928579 : Nat := 118140960795 + 928579 * 2 ^ 59
def prefixEnd_928579 : Nat := 4983230072969 + 3 ^ 40 * 928579 * 2
def baseEnd_928579 : Nat := 476807352671427664092049

theorem tailTrace_928579 : CollatzResearch.WordTrace tailWord_928579 prefixEnd_928579 476807352671427664092049 := by
  unfold tailWord_928579
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868058502924346512420791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22578705668616231008280527 33868058502924346512420791)
  ·
    refine ⟨50802087754386519768631187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33868058502924346512420791 50802087754386519768631187)
    ·
      refine ⟨76203131631579779652946781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50802087754386519768631187 76203131631579779652946781)
      ·
        refine ⟨28576174361842417369855043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76203131631579779652946781 28576174361842417369855043)
        ·
          refine ⟨42864261542763626054782565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28576174361842417369855043 42864261542763626054782565)
          ·
            refine ⟨8037049039268179885271731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42864261542763626054782565 8037049039268179885271731)
            ·
              refine ⟨12055573558902269827907597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037049039268179885271731 12055573558902269827907597)
              ·
                refine ⟨4520840084588351185465349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12055573558902269827907597 4520840084588351185465349)
                ·
                  refine ⟨847657515860315847274753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4520840084588351185465349 847657515860315847274753)
                  ·
                    refine ⟨635743136895236885456065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 847657515860315847274753 635743136895236885456065)
                    ·
                      refine ⟨476807352671427664092049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635743136895236885456065 476807352671427664092049)
                      ·
                        rfl

theorem cell23_928579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_928579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928579 prefixEnd_928579 := by exact prefixLift 928579
  have htrace : WordTrace (prefixWord ++ tailWord_928579) baseStart_928579 baseEnd_928579 := by
    simpa [prefixWord, tailWord_928579, baseEnd_928579] using wordTrace_append hprefix tailTrace_928579
  have hstable : (prefixWord ++ tailWord_928579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928579).length < 2 ^ (prefixWord ++ tailWord_928579).sum := by decide
  have hdescent : baseEnd_928579 < baseStart_928579 := by decide
  rcases family_descends (prefixWord ++ tailWord_928579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928630 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_928630 : Nat := 118140960795 + 928630 * 2 ^ 59
def prefixEnd_928630 : Nat := 4983230072969 + 3 ^ 40 * 928630 * 2
def baseEnd_928630 : Nat := 476833540184806964554315

theorem tailTrace_928630 : CollatzResearch.WordTrace tailWord_928630 prefixEnd_928630 476833540184806964554315 := by
  unfold tailWord_928630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116869914108723888907959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22579945750493054815018229 2116869914108723888907959)
  ·
    refine ⟨3175304871163085833361939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116869914108723888907959 3175304871163085833361939)
    ·
      refine ⟨4762957306744628750042909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175304871163085833361939 4762957306744628750042909)
      ·
        refine ⟨1786108990029235781266091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4762957306744628750042909 1786108990029235781266091)
        ·
          refine ⟨2679163485043853671899137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786108990029235781266091 2679163485043853671899137)
          ·
            refine ⟨2009372613782890253924353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679163485043853671899137 2009372613782890253924353)
            ·
              refine ⟨1507029460337167690443265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009372613782890253924353 1507029460337167690443265)
              ·
                refine ⟨1130272095252875767832449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507029460337167690443265 1130272095252875767832449)
                ·
                  refine ⟨847704071439656825874337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130272095252875767832449 847704071439656825874337)
                  ·
                    refine ⟨635778053579742619405753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 847704071439656825874337 635778053579742619405753)
                    ·
                      refine ⟨476833540184806964554315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635778053579742619405753 476833540184806964554315)
                      ·
                        rfl

theorem cell23_928630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_928630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928630 prefixEnd_928630 := by exact prefixLift 928630
  have htrace : WordTrace (prefixWord ++ tailWord_928630) baseStart_928630 baseEnd_928630 := by
    simpa [prefixWord, tailWord_928630, baseEnd_928630] using wordTrace_append hprefix tailTrace_928630
  have hstable : (prefixWord ++ tailWord_928630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928630).length < 2 ^ (prefixWord ++ tailWord_928630).sum := by decide
  have hdescent : baseEnd_928630 < baseStart_928630 := by decide
  rcases family_descends (prefixWord ++ tailWord_928630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928652 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_928652 : Nat := 118140960795 + 928652 * 2 ^ 59
def prefixEnd_928652 : Nat := 4983230072969 + 3 ^ 40 * 928652 * 2
def baseEnd_928652 : Nat := 476844836759205878479213

theorem tailTrace_928652 : CollatzResearch.WordTrace tailWord_928652 prefixEnd_928652 476844836759205878479213 := by
  unfold tailWord_928652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16935360515829939989914105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22580480687773253319885473 16935360515829939989914105)
  ·
    refine ⟨12701520386872454992435579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16935360515829939989914105 12701520386872454992435579)
    ·
      refine ⟨19052280580308682488653369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701520386872454992435579 19052280580308682488653369)
      ·
        refine ⟨14289210435231511866490027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19052280580308682488653369 14289210435231511866490027)
        ·
          refine ⟨21433815652847267799735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289210435231511866490027 21433815652847267799735041)
          ·
            refine ⟨16075361739635450849801281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21433815652847267799735041 16075361739635450849801281)
            ·
              refine ⟨12056521304726588137350961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16075361739635450849801281 12056521304726588137350961)
              ·
                refine ⟨9042390978544941103013221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12056521304726588137350961 9042390978544941103013221)
                ·
                  refine ⟨1695448308477176456814979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9042390978544941103013221 1695448308477176456814979)
                  ·
                    refine ⟨2543172462715764685222469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695448308477176456814979 2543172462715764685222469)
                    ·
                      refine ⟨476844836759205878479213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2543172462715764685222469 476844836759205878479213)
                      ·
                        rfl

theorem cell23_928652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_928652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928652 prefixEnd_928652 := by exact prefixLift 928652
  have htrace : WordTrace (prefixWord ++ tailWord_928652) baseStart_928652 baseEnd_928652 := by
    simpa [prefixWord, tailWord_928652, baseEnd_928652] using wordTrace_append hprefix tailTrace_928652
  have hstable : (prefixWord ++ tailWord_928652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928652).length < 2 ^ (prefixWord ++ tailWord_928652).sum := by decide
  have hdescent : baseEnd_928652 < baseStart_928652 := by decide
  rcases family_descends (prefixWord ++ tailWord_928652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928666 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_928666 : Nat := 118140960795 + 928666 * 2 ^ 59
def prefixEnd_928666 : Nat := 4983230072969 + 3 ^ 40 * 928666 * 2
def baseEnd_928666 : Nat := 158950675162789607901383

theorem tailTrace_928666 : CollatzResearch.WordTrace tailWord_928666 prefixEnd_928666 158950675162789607901383 := by
  unfold tailWord_928666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467807913402290092709463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22580821102406106913891901 8467807913402290092709463)
  ·
    refine ⟨12701711870103435139064195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8467807913402290092709463 12701711870103435139064195)
    ·
      refine ⟨19052567805155152708596293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701711870103435139064195 19052567805155152708596293)
      ·
        refine ⟨3572356463466591132861805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19052567805155152708596293 3572356463466591132861805)
        ·
          refine ⟨1339633673799971674823177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3572356463466591132861805 1339633673799971674823177)
          ·
            refine ⟨1004725255349978756117383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339633673799971674823177 1004725255349978756117383)
            ·
              refine ⟨1507087883024968134176075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004725255349978756117383 1507087883024968134176075)
              ·
                refine ⟨2260631824537452201264113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507087883024968134176075 2260631824537452201264113)
                ·
                  refine ⟨1695473868403089150948085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2260631824537452201264113 1695473868403089150948085)
                  ·
                    refine ⟨158950675162789607901383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1695473868403089150948085 158950675162789607901383)
                    ·
                      rfl

theorem cell23_928666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_928666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928666 prefixEnd_928666 := by exact prefixLift 928666
  have htrace : WordTrace (prefixWord ++ tailWord_928666) baseStart_928666 baseEnd_928666 := by
    simpa [prefixWord, tailWord_928666, baseEnd_928666] using wordTrace_append hprefix tailTrace_928666
  have hstable : (prefixWord ++ tailWord_928666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928666).length < 2 ^ (prefixWord ++ tailWord_928666).sum := by decide
  have hdescent : baseEnd_928666 < baseStart_928666 := by decide
  rcases family_descends (prefixWord ++ tailWord_928666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928669 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_928669 : Nat := 118140960795 + 928669 * 2 ^ 59
def prefixEnd_928669 : Nat := 4983230072969 + 3 ^ 40 * 928669 * 2
def baseEnd_928669 : Nat := 476853565930332311966635

theorem tailTrace_928669 : CollatzResearch.WordTrace tailWord_928669 prefixEnd_928669 476853565930332311966635 := by
  unfold tailWord_928669
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871341072598291883197061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580894048398861255464707 33871341072598291883197061)
  ·
    refine ⟨6350876451112179728099449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33871341072598291883197061 6350876451112179728099449)
    ·
      refine ⟨4763157338334134796074587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6350876451112179728099449 4763157338334134796074587)
      ·
        refine ⟨7144736007501202194111881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763157338334134796074587 7144736007501202194111881)
        ·
          refine ⟨5358552005625901645583911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7144736007501202194111881 5358552005625901645583911)
          ·
            refine ⟨8037828008438852468375867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358552005625901645583911 8037828008438852468375867)
            ·
              refine ⟨12056742012658278702563801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037828008438852468375867 12056742012658278702563801)
              ·
                refine ⟨9042556509493709026922851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12056742012658278702563801 9042556509493709026922851)
                ·
                  refine ⟨13563834764240563540384277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9042556509493709026922851 13563834764240563540384277)
                  ·
                    refine ⟨635804754573776415955513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13563834764240563540384277 635804754573776415955513)
                    ·
                      refine ⟨476853565930332311966635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635804754573776415955513 476853565930332311966635)
                      ·
                        rfl

theorem cell23_928669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_928669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928669 prefixEnd_928669 := by exact prefixLift 928669
  have htrace : WordTrace (prefixWord ++ tailWord_928669) baseStart_928669 baseEnd_928669 := by
    simpa [prefixWord, tailWord_928669, baseEnd_928669] using wordTrace_append hprefix tailTrace_928669
  have hstable : (prefixWord ++ tailWord_928669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928669).length < 2 ^ (prefixWord ++ tailWord_928669).sum := by decide
  have hdescent : baseEnd_928669 < baseStart_928669 := by decide
  rcases family_descends (prefixWord ++ tailWord_928669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928696 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 1, 4]
def baseStart_928696 : Nat := 118140960795 + 928696 * 2 ^ 59
def prefixEnd_928696 : Nat := 4983230072969 + 3 ^ 40 * 928696 * 2
def baseEnd_928696 : Nat := 158955809969334568776337

theorem tailTrace_928696 : CollatzResearch.WordTrace tailWord_928696 prefixEnd_928696 158955809969334568776337 := by
  unfold tailWord_928696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936162921750237747214971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22581550562333650329619961 16936162921750237747214971)
  ·
    refine ⟨25404244382625356620822457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16936162921750237747214971 25404244382625356620822457)
    ·
      refine ⟨19053183286969017465616843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25404244382625356620822457 19053183286969017465616843)
      ·
        refine ⟨28579774930453526198425265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053183286969017465616843 28579774930453526198425265)
        ·
          refine ⟨21434831197840144648818949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28579774930453526198425265 21434831197840144648818949)
          ·
            refine ⟨4019030849595027121653553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21434831197840144648818949 4019030849595027121653553)
            ·
              refine ⟨3014273137196270341240165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019030849595027121653553 3014273137196270341240165)
              ·
                refine ⟨565176213224300688982531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3014273137196270341240165 565176213224300688982531)
                ·
                  refine ⟨847764319836451033473797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565176213224300688982531 847764319836451033473797)
                  ·
                    refine ⟨158955809969334568776337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847764319836451033473797 158955809969334568776337)
                    ·
                      rfl

theorem cell23_928696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_928696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928696 prefixEnd_928696 := by exact prefixLift 928696
  have htrace : WordTrace (prefixWord ++ tailWord_928696) baseStart_928696 baseEnd_928696 := by
    simpa [prefixWord, tailWord_928696, baseEnd_928696] using wordTrace_append hprefix tailTrace_928696
  have hstable : (prefixWord ++ tailWord_928696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928696).length < 2 ^ (prefixWord ++ tailWord_928696).sum := by decide
  have hdescent : baseEnd_928696 < baseStart_928696 := by decide
  rcases family_descends (prefixWord ++ tailWord_928696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928739 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 1, 5]
def baseStart_928739 : Nat := 118140960795 + 928739 * 2 ^ 59
def prefixEnd_928739 : Nat := 4983230072969 + 3 ^ 40 * 928739 * 2
def baseEnd_928739 : Nat := 158963169858715679363771

theorem tailTrace_928739 : CollatzResearch.WordTrace tailWord_928739 prefixEnd_928739 158963169858715679363771 := by
  unfold tailWord_928739
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873894182344693838245271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22582596121563129225496847 33873894182344693838245271)
  ·
    refine ⟨50810841273517040757367907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33873894182344693838245271 50810841273517040757367907)
    ·
      refine ⟨76216261910275561136051861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50810841273517040757367907 76216261910275561136051861)
      ·
        refine ⟨3572637277044166928252431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76216261910275561136051861 3572637277044166928252431)
        ·
          refine ⟨5358955915566250392378647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572637277044166928252431 5358955915566250392378647)
          ·
            refine ⟨8038433873349375588567971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358955915566250392378647 8038433873349375588567971)
            ·
              refine ⟨12057650810024063382851957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038433873349375588567971 12057650810024063382851957)
              ·
                refine ⟨1130404763439755942142371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12057650810024063382851957 1130404763439755942142371)
                ·
                  refine ⟨1695607145159633913213557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130404763439755942142371 1695607145159633913213557)
                  ·
                    refine ⟨158963169858715679363771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1695607145159633913213557 158963169858715679363771)
                    ·
                      rfl

theorem cell23_928739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 5].length) (baseStart_928739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928739 prefixEnd_928739 := by exact prefixLift 928739
  have htrace : WordTrace (prefixWord ++ tailWord_928739) baseStart_928739 baseEnd_928739 := by
    simpa [prefixWord, tailWord_928739, baseEnd_928739] using wordTrace_append hprefix tailTrace_928739
  have hstable : (prefixWord ++ tailWord_928739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928739).length < 2 ^ (prefixWord ++ tailWord_928739).sum := by decide
  have hdescent : baseEnd_928739 < baseStart_928739 := by decide
  rcases family_descends (prefixWord ++ tailWord_928739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928746 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_928746 : Nat := 118140960795 + 928746 * 2 ^ 59
def prefixEnd_928746 : Nat := 4983230072969 + 3 ^ 40 * 928746 * 2
def baseEnd_928746 : Nat := 476893103940728510703781

theorem tailTrace_928746 : CollatzResearch.WordTrace tailWord_928746 prefixEnd_928746 476893103940728510703781 := by
  unfold tailWord_928746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468537373329833508437523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22582766328879556022500061 8468537373329833508437523)
  ·
    refine ⟨12702806059994750262656285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8468537373329833508437523 12702806059994750262656285)
    ·
      refine ⟨4763552272498031348496107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12702806059994750262656285 4763552272498031348496107)
      ·
        refine ⟨7145328408747047022744161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763552272498031348496107 7145328408747047022744161)
        ·
          refine ⟨5358996306560285267058121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7145328408747047022744161 5358996306560285267058121)
          ·
            refine ⟨4019247229920213950293591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358996306560285267058121 4019247229920213950293591)
            ·
              refine ⟨6028870844880320925440387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019247229920213950293591 6028870844880320925440387)
              ·
                refine ⟨9043306267320481388160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028870844880320925440387 9043306267320481388160581)
                ·
                  refine ⟨1695619925122590260280109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9043306267320481388160581 1695619925122590260280109)
                  ·
                    refine ⟨635857471920971347605041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695619925122590260280109 635857471920971347605041)
                    ·
                      refine ⟨476893103940728510703781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635857471920971347605041 476893103940728510703781)
                      ·
                        rfl

theorem cell23_928746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_928746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928746 prefixEnd_928746 := by exact prefixLift 928746
  have htrace : WordTrace (prefixWord ++ tailWord_928746) baseStart_928746 baseEnd_928746 := by
    simpa [prefixWord, tailWord_928746, baseEnd_928746] using wordTrace_append hprefix tailTrace_928746
  have hstable : (prefixWord ++ tailWord_928746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928746).length < 2 ^ (prefixWord ++ tailWord_928746).sum := by decide
  have hdescent : baseEnd_928746 < baseStart_928746 := by decide
  rcases family_descends (prefixWord ++ tailWord_928746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928753 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_928753 : Nat := 118140960795 + 928753 * 2 ^ 59
def prefixEnd_928753 : Nat := 4983230072969 + 3 ^ 40 * 928753 * 2
def baseEnd_928753 : Nat := 476896698305309983316249

theorem tailTrace_928753 : CollatzResearch.WordTrace tailWord_928753 prefixEnd_928753 476896698305309983316249 := by
  unfold tailWord_928753
  simp only [CollatzResearch.WordTrace]
  refine ⟨33874404804293974229254913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22582936536195982819503275 33874404804293974229254913)
  ·
    refine ⟨25405803603220480671941185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33874404804293974229254913 25405803603220480671941185)
    ·
      refine ⟨19054352702415360503955889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25405803603220480671941185 19054352702415360503955889)
      ·
        refine ⟨14290764526811520377966917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19054352702415360503955889 14290764526811520377966917)
        ·
          refine ⟨2679518348777160070868797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14290764526811520377966917 2679518348777160070868797)
          ·
            refine ⟨1004819380791435026575799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2679518348777160070868797 1004819380791435026575799)
            ·
              refine ⟨1507229071187152539863699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004819380791435026575799 1507229071187152539863699)
              ·
                refine ⟨2260843606780728809795549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507229071187152539863699 2260843606780728809795549)
                ·
                  refine ⟨847816352542773303673331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2260843606780728809795549 847816352542773303673331)
                  ·
                    refine ⟨1271724528814159955509997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847816352542773303673331 1271724528814159955509997)
                    ·
                      refine ⟨476896698305309983316249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271724528814159955509997 476896698305309983316249)
                      ·
                        rfl

theorem cell23_928753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_928753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928753 prefixEnd_928753 := by exact prefixLift 928753
  have htrace : WordTrace (prefixWord ++ tailWord_928753) baseStart_928753 baseEnd_928753 := by
    simpa [prefixWord, tailWord_928753, baseEnd_928753] using wordTrace_append hprefix tailTrace_928753
  have hstable : (prefixWord ++ tailWord_928753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928753).length < 2 ^ (prefixWord ++ tailWord_928753).sum := by decide
  have hdescent : baseEnd_928753 < baseStart_928753 := by decide
  rcases family_descends (prefixWord ++ tailWord_928753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928776 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_928776 : Nat := 118140960795 + 928776 * 2 ^ 59
def prefixEnd_928776 : Nat := 4983230072969 + 3 ^ 40 * 928776 * 2
def baseEnd_928776 : Nat := 476908508360363393328643

theorem tailTrace_928776 : CollatzResearch.WordTrace tailWord_928776 prefixEnd_928776 476908508360363393328643 := by
  unfold tailWord_928776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937621841605324578671091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22583495788807099438228121 16937621841605324578671091)
  ·
    refine ⟨25406432762407986868006637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16937621841605324578671091 25406432762407986868006637)
    ·
      refine ⟨9527412285902995075502489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25406432762407986868006637 9527412285902995075502489)
      ·
        refine ⟨7145559214427246306626867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9527412285902995075502489 7145559214427246306626867)
        ·
          refine ⟨10718338821640869459940301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145559214427246306626867 10718338821640869459940301)
          ·
            refine ⟨4019377058115326047477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10718338821640869459940301 4019377058115326047477613)
            ·
              refine ⟨1507266396793247267804105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4019377058115326047477613 1507266396793247267804105)
              ·
                refine ⟨1130449797594935450853079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507266396793247267804105 1130449797594935450853079)
                ·
                  refine ⟨1695674696392403176279619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130449797594935450853079 1695674696392403176279619)
                  ·
                    refine ⟨2543512044588604764419429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695674696392403176279619 2543512044588604764419429)
                    ·
                      refine ⟨476908508360363393328643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2543512044588604764419429 476908508360363393328643)
                      ·
                        rfl

theorem cell23_928776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_928776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928776 prefixEnd_928776 := by exact prefixLift 928776
  have htrace : WordTrace (prefixWord ++ tailWord_928776) baseStart_928776 baseEnd_928776 := by
    simpa [prefixWord, tailWord_928776, baseEnd_928776] using wordTrace_append hprefix tailTrace_928776
  have hstable : (prefixWord ++ tailWord_928776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928776).length < 2 ^ (prefixWord ++ tailWord_928776).sum := by decide
  have hdescent : baseEnd_928776 < baseStart_928776 := by decide
  rcases family_descends (prefixWord ++ tailWord_928776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928789 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_928789 : Nat := 118140960795 + 928789 * 2 ^ 59
def prefixEnd_928789 : Nat := 4983230072969 + 3 ^ 40 * 928789 * 2
def baseEnd_928789 : Nat := 476915183608871842466083

theorem tailTrace_928789 : CollatzResearch.WordTrace tailWord_928789 prefixEnd_928789 476915183608871842466083 := by
  unfold tailWord_928789
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875717832163552377565421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22583811888109034918376947 33875717832163552377565421)
  ·
    refine ⟨12703394187061332141587033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33875717832163552377565421 12703394187061332141587033)
    ·
      refine ⟨9527545640295999106190275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12703394187061332141587033 9527545640295999106190275)
      ·
        refine ⟨14291318460443998659285413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527545640295999106190275 14291318460443998659285413)
        ·
          refine ⟨2679622211333249748616015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14291318460443998659285413 2679622211333249748616015)
          ·
            refine ⟨4019433316999874622924023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679622211333249748616015 4019433316999874622924023)
            ·
              refine ⟨6029149975499811934386035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019433316999874622924023 6029149975499811934386035)
              ·
                refine ⟨9043724963249717901579053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029149975499811934386035 9043724963249717901579053)
                ·
                  refine ⟨3391396861218644213092145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9043724963249717901579053 3391396861218644213092145)
                  ·
                    refine ⟨2543547645913983159819109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391396861218644213092145 2543547645913983159819109)
                    ·
                      refine ⟨476915183608871842466083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2543547645913983159819109 476915183608871842466083)
                      ·
                        rfl

theorem cell23_928789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_928789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928789 prefixEnd_928789 := by exact prefixLift 928789
  have htrace : WordTrace (prefixWord ++ tailWord_928789) baseStart_928789 baseEnd_928789 := by
    simpa [prefixWord, tailWord_928789, baseEnd_928789] using wordTrace_append hprefix tailTrace_928789
  have hstable : (prefixWord ++ tailWord_928789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928789).length < 2 ^ (prefixWord ++ tailWord_928789).sum := by decide
  have hdescent : baseEnd_928789 < baseStart_928789 := by decide
  rcases family_descends (prefixWord ++ tailWord_928789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928812 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_928812 : Nat := 118140960795 + 928812 * 2 ^ 59
def prefixEnd_928812 : Nat := 4983230072969 + 3 ^ 40 * 928812 * 2
def baseEnd_928812 : Nat := 158975664554641750826159

theorem tailTrace_928812 : CollatzResearch.WordTrace tailWord_928812 prefixEnd_928812 158975664554641750826159 := by
  unfold tailWord_928812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938278355540113652826345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22584371140720151537101793 16938278355540113652826345)
  ·
    refine ⟨12703708766655085239619759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16938278355540113652826345 12703708766655085239619759)
    ·
      refine ⟨19055563149982627859429639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703708766655085239619759 19055563149982627859429639)
      ·
        refine ⟨28583344724973941789144459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055563149982627859429639 28583344724973941789144459)
        ·
          refine ⟨42875017087460912683716689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28583344724973941789144459 42875017087460912683716689)
          ·
            refine ⟨32156262815595684512787517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42875017087460912683716689 32156262815595684512787517)
            ·
              refine ⟨12058598555848381692295319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32156262815595684512787517 12058598555848381692295319)
              ·
                refine ⟨18087897833772572538442979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058598555848381692295319 18087897833772572538442979)
                ·
                  refine ⟨27131846750658858807664469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18087897833772572538442979 27131846750658858807664469)
                  ·
                    refine ⟨158975664554641750826159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27131846750658858807664469 158975664554641750826159)
                    ·
                      rfl

theorem cell23_928812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_928812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928812 prefixEnd_928812 := by exact prefixLift 928812
  have htrace : WordTrace (prefixWord ++ tailWord_928812) baseStart_928812 baseEnd_928812 := by
    simpa [prefixWord, tailWord_928812, baseEnd_928812] using wordTrace_append hprefix tailTrace_928812
  have hstable : (prefixWord ++ tailWord_928812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928812).length < 2 ^ (prefixWord ++ tailWord_928812).sum := by decide
  have hdescent : baseEnd_928812 < baseStart_928812 := by decide
  rcases family_descends (prefixWord ++ tailWord_928812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928853 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_928853 : Nat := 118140960795 + 928853 * 2 ^ 59
def prefixEnd_928853 : Nat := 4983230072969 + 3 ^ 40 * 928853 * 2
def baseEnd_928853 : Nat := 476948046370759592065789

theorem tailTrace_928853 : CollatzResearch.WordTrace tailWord_928853 prefixEnd_928853 476948046370759592065789 := by
  unfold tailWord_928853
  simp only [CollatzResearch.WordTrace]
  refine ⟨33878052103931691307895213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22585368069287794205263475 33878052103931691307895213)
  ·
    refine ⟨12704269538974384240460705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33878052103931691307895213 12704269538974384240460705)
    ·
      refine ⟨9528202154230788180345529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12704269538974384240460705 9528202154230788180345529)
      ·
        refine ⟨7146151615673091135259147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9528202154230788180345529 7146151615673091135259147)
        ·
          refine ⟨10719227423509636702888721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146151615673091135259147 10719227423509636702888721)
          ·
            refine ⟨8039420567632227527166541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10719227423509636702888721 8039420567632227527166541)
            ·
              refine ⟨3014782712862085322687453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8039420567632227527166541 3014782712862085322687453)
              ·
                refine ⟨1130543517323281996007795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3014782712862085322687453 1130543517323281996007795)
                ·
                  refine ⟨1695815275984922994011693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130543517323281996007795 1695815275984922994011693)
                  ·
                    refine ⟨635930728494346122754385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695815275984922994011693 635930728494346122754385)
                    ·
                      refine ⟨476948046370759592065789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635930728494346122754385 476948046370759592065789)
                      ·
                        rfl

theorem cell23_928853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_928853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928853 prefixEnd_928853 := by exact prefixLift 928853
  have htrace : WordTrace (prefixWord ++ tailWord_928853) baseStart_928853 baseEnd_928853 := by
    simpa [prefixWord, tailWord_928853, baseEnd_928853] using wordTrace_append hprefix tailTrace_928853
  have hstable : (prefixWord ++ tailWord_928853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928853).length < 2 ^ (prefixWord ++ tailWord_928853).sum := by decide
  have hdescent : baseEnd_928853 < baseStart_928853 := by decide
  rcases family_descends (prefixWord ++ tailWord_928853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928854 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_928854 : Nat := 118140960795 + 928854 * 2 ^ 59
def prefixEnd_928854 : Nat := 4983230072969 + 3 ^ 40 * 928854 * 2
def baseEnd_928854 : Nat := 158982853283804696051095

theorem tailTrace_928854 : CollatzResearch.WordTrace tailWord_928854 prefixEnd_928854 158982853283804696051095 := by
  unfold tailWord_928854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117380536058004279917601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22585392384618712319121077 2117380536058004279917601)
  ·
    refine ⟨1588035402043503209938201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2117380536058004279917601 1588035402043503209938201)
    ·
      refine ⟨1191026551532627407453651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588035402043503209938201 1191026551532627407453651)
      ·
        refine ⟨1786539827298941111180477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191026551532627407453651 1786539827298941111180477)
        ·
          refine ⟨669952435237102916692679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1786539827298941111180477 669952435237102916692679)
          ·
            refine ⟨1004928652855654375039019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669952435237102916692679 1004928652855654375039019)
            ·
              refine ⟨1507392979283481562558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004928652855654375039019 1507392979283481562558529)
              ·
                refine ⟨1130544734462611171918897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507392979283481562558529 1130544734462611171918897)
                ·
                  refine ⟨847908550846958378939173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130544734462611171918897 847908550846958378939173)
                  ·
                    refine ⟨158982853283804696051095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847908550846958378939173 158982853283804696051095)
                    ·
                      rfl

theorem cell23_928854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_928854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928854 prefixEnd_928854 := by exact prefixLift 928854
  have htrace : WordTrace (prefixWord ++ tailWord_928854) baseStart_928854 baseEnd_928854 := by
    simpa [prefixWord, tailWord_928854, baseEnd_928854] using wordTrace_append hprefix tailTrace_928854
  have hstable : (prefixWord ++ tailWord_928854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928854).length < 2 ^ (prefixWord ++ tailWord_928854).sum := by decide
  have hdescent : baseEnd_928854 < baseStart_928854 := by decide
  rcases family_descends (prefixWord ++ tailWord_928854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928879 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_928879 : Nat := 118140960795 + 928879 * 2 ^ 59
def prefixEnd_928879 : Nat := 4983230072969 + 3 ^ 40 * 928879 * 2
def baseEnd_928879 : Nat := 476961396867776490340669

theorem tailTrace_928879 : CollatzResearch.WordTrace tailWord_928879 prefixEnd_928879 476961396867776490340669 := by
  unfold tailWord_928879
  simp only [CollatzResearch.WordTrace]
  refine ⟨33879000401837497748341691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22586000267891665165561127 33879000401837497748341691)
  ·
    refine ⟨50818500602756246622512537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33879000401837497748341691 50818500602756246622512537)
    ·
      refine ⟨38113875452067184966884403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50818500602756246622512537 38113875452067184966884403)
      ·
        refine ⟨57170813178100777450326605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38113875452067184966884403 57170813178100777450326605)
        ·
          refine ⟨21439054941787791543872477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57170813178100777450326605 21439054941787791543872477)
          ·
            refine ⟨8039645603170421828952179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21439054941787791543872477 8039645603170421828952179)
            ·
              refine ⟨12059468404755632743428269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039645603170421828952179 12059468404755632743428269)
              ·
                refine ⟨4522300651783362278785601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12059468404755632743428269 4522300651783362278785601)
                ·
                  refine ⟨3391725488837521709089201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522300651783362278785601 3391725488837521709089201)
                  ·
                    refine ⟨2543794116628141281816901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391725488837521709089201 2543794116628141281816901)
                    ·
                      refine ⟨476961396867776490340669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2543794116628141281816901 476961396867776490340669)
                      ·
                        rfl

theorem cell23_928879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_928879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928879 prefixEnd_928879 := by exact prefixLift 928879
  have htrace : WordTrace (prefixWord ++ tailWord_928879) baseStart_928879 baseEnd_928879 := by
    simpa [prefixWord, tailWord_928879, baseEnd_928879] using wordTrace_append hprefix tailTrace_928879
  have hstable : (prefixWord ++ tailWord_928879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928879).length < 2 ^ (prefixWord ++ tailWord_928879).sum := by decide
  have hdescent : baseEnd_928879 < baseStart_928879 := by decide
  rcases family_descends (prefixWord ++ tailWord_928879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928886 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_928886 : Nat := 118140960795 + 928886 * 2 ^ 59
def prefixEnd_928886 : Nat := 4983230072969 + 3 ^ 40 * 928886 * 2
def baseEnd_928886 : Nat := 476964991232357962953137

theorem tailTrace_928886 : CollatzResearch.WordTrace tailWord_928886 prefixEnd_928886 476964991232357962953137 := by
  unfold tailWord_928886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117453482050758621490407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22586170475208091962564341 2117453482050758621490407)
  ·
    refine ⟨3176180223076137932235611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2117453482050758621490407 3176180223076137932235611)
    ·
      refine ⟨4764270334614206898353417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176180223076137932235611 4764270334614206898353417)
      ·
        refine ⟨3573202750960655173765063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764270334614206898353417 3573202750960655173765063)
        ·
          refine ⟨5359804126440982760647595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573202750960655173765063 5359804126440982760647595)
          ·
            refine ⟨8039706189661474140971393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359804126440982760647595 8039706189661474140971393)
            ·
              refine ⟨6029779642246105605728545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8039706189661474140971393 6029779642246105605728545)
              ·
                refine ⟨4522334731684579204296409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029779642246105605728545 4522334731684579204296409)
                ·
                  refine ⟨3391751048763434403222307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522334731684579204296409 3391751048763434403222307)
                  ·
                    refine ⟨5087626573145151604833461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3391751048763434403222307 5087626573145151604833461)
                    ·
                      refine ⟨476964991232357962953137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5087626573145151604833461 476964991232357962953137)
                      ·
                        rfl

theorem cell23_928886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_928886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928886 prefixEnd_928886 := by exact prefixLift 928886
  have htrace : WordTrace (prefixWord ++ tailWord_928886) baseStart_928886 baseEnd_928886 := by
    simpa [prefixWord, tailWord_928886, baseEnd_928886] using wordTrace_append hprefix tailTrace_928886
  have hstable : (prefixWord ++ tailWord_928886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928886).length < 2 ^ (prefixWord ++ tailWord_928886).sum := by decide
  have hdescent : baseEnd_928886 < baseStart_928886 := by decide
  rcases family_descends (prefixWord ++ tailWord_928886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_928969 : Nat := 118140960795 + 928969 * 2 ^ 59
def prefixEnd_928969 : Nat := 4983230072969 + 3 ^ 40 * 928969 * 2
def baseEnd_928969 : Nat := 477007610126681138215255

theorem tailTrace_928969 : CollatzResearch.WordTrace tailWord_928969 prefixEnd_928969 477007610126681138215255 := by
  unfold tailWord_928969
  simp only [CollatzResearch.WordTrace]
  refine ⟨33882282971511443119117961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22588188647674295412745307 33882282971511443119117961)
  ·
    refine ⟨25411712228633582339338471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33882282971511443119117961 25411712228633582339338471)
    ·
      refine ⟨38117568342950373509007707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25411712228633582339338471 38117568342950373509007707)
      ·
        refine ⟨57176352514425560263511561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38117568342950373509007707 57176352514425560263511561)
        ·
          refine ⟨42882264385819170197633671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57176352514425560263511561 42882264385819170197633671)
          ·
            refine ⟨64323396578728755296450507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42882264385819170197633671 64323396578728755296450507)
            ·
              refine ⟨96485094868093132944675761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64323396578728755296450507 96485094868093132944675761)
              ·
                refine ⟨72363821151069849708506821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96485094868093132944675761 72363821151069849708506821)
                ·
                  refine ⟨13568216465825596820345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72363821151069849708506821 13568216465825596820345029)
                  ·
                    refine ⟨2544040587342299403814693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13568216465825596820345029 2544040587342299403814693)
                    ·
                      refine ⟨477007610126681138215255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2544040587342299403814693 477007610126681138215255)
                      ·
                        rfl

theorem cell23_928969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_928969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928969 prefixEnd_928969 := by exact prefixLift 928969
  have htrace : WordTrace (prefixWord ++ tailWord_928969) baseStart_928969 baseEnd_928969 := by
    simpa [prefixWord, tailWord_928969, baseEnd_928969] using wordTrace_append hprefix tailTrace_928969
  have hstable : (prefixWord ++ tailWord_928969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928969).length < 2 ^ (prefixWord ++ tailWord_928969).sum := by decide
  have hdescent : baseEnd_928969 < baseStart_928969 := by decide
  rcases family_descends (prefixWord ++ tailWord_928969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928996 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 6]
def baseStart_928996 : Nat := 118140960795 + 928996 * 2 ^ 59
def prefixEnd_928996 : Nat := 4983230072969 + 3 ^ 40 * 928996 * 2
def baseEnd_928996 : Nat := 53002386011594725841959

theorem tailTrace_928996 : CollatzResearch.WordTrace tailWord_928996 prefixEnd_928996 53002386011594725841959 := by
  unfold tailWord_928996
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941633871206813365175421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22588845161609084486900561 16941633871206813365175421)
  ·
    refine ⟨6353112701702555011940783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16941633871206813365175421 6353112701702555011940783)
    ·
      refine ⟨9529669052553832517911175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353112701702555011940783 9529669052553832517911175)
      ·
        refine ⟨14294503578830748776866763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9529669052553832517911175 14294503578830748776866763)
        ·
          refine ⟨21441755368246123165300145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14294503578830748776866763 21441755368246123165300145)
          ·
            refine ⟨16081316526184592373975109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21441755368246123165300145 16081316526184592373975109)
            ·
              refine ⟨3015246848659611070120333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16081316526184592373975109 3015246848659611070120333)
              ·
                refine ⟨1130717568247354151295125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3015246848659611070120333 1130717568247354151295125)
                ·
                  refine ⟨53002386011594725841959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1130717568247354151295125 53002386011594725841959)
                  ·
                    rfl

theorem cell23_928996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_928996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928996 prefixEnd_928996 := by exact prefixLift 928996
  have htrace : WordTrace (prefixWord ++ tailWord_928996) baseStart_928996 baseEnd_928996 := by
    simpa [prefixWord, tailWord_928996, baseEnd_928996] using wordTrace_append hprefix tailTrace_928996
  have hstable : (prefixWord ++ tailWord_928996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928996).length < 2 ^ (prefixWord ++ tailWord_928996).sum := by decide
  have hdescent : baseEnd_928996 < baseStart_928996 := by decide
  rcases family_descends (prefixWord ++ tailWord_928996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929033 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 4, 3, 2]
def baseStart_929033 : Nat := 118140960795 + 929033 * 2 ^ 59
def prefixEnd_929033 : Nat := 4983230072969 + 3 ^ 40 * 929033 * 2
def baseEnd_929033 : Nat := 477040472888568887814961

theorem tailTrace_929033 : CollatzResearch.WordTrace tailWord_929033 prefixEnd_929033 477040472888568887814961 := by
  unfold tailWord_929033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33884617243279582049447753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22589744828853054699631835 33884617243279582049447753)
  ·
    refine ⟨25413462932459686537085815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33884617243279582049447753 25413462932459686537085815)
    ·
      refine ⟨38120194398689529805628723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25413462932459686537085815 38120194398689529805628723)
      ·
        refine ⟨57180291598034294708443085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38120194398689529805628723 57180291598034294708443085)
        ·
          refine ⟨21442609349262860515666157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57180291598034294708443085 21442609349262860515666157)
          ·
            refine ⟨8040978505973572693374809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21442609349262860515666157 8040978505973572693374809)
            ·
              refine ⟨6030733879480179520031107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8040978505973572693374809 6030733879480179520031107)
              ·
                refine ⟨9046100819220269280046661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030733879480179520031107 9046100819220269280046661)
                ·
                  refine ⟨1696143903603800490008749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9046100819220269280046661 1696143903603800490008749)
                  ·
                    refine ⟨636053963851425183753281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696143903603800490008749 636053963851425183753281)
                    ·
                      refine ⟨477040472888568887814961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636053963851425183753281 477040472888568887814961)
                      ·
                        rfl

theorem cell23_929033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3, 2].length) (baseStart_929033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929033 prefixEnd_929033 := by exact prefixLift 929033
  have htrace : WordTrace (prefixWord ++ tailWord_929033) baseStart_929033 baseEnd_929033 := by
    simpa [prefixWord, tailWord_929033, baseEnd_929033] using wordTrace_append hprefix tailTrace_929033
  have hstable : (prefixWord ++ tailWord_929033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929033).length < 2 ^ (prefixWord ++ tailWord_929033).sum := by decide
  have hdescent : baseEnd_929033 < baseStart_929033 := by decide
  rcases family_descends (prefixWord ++ tailWord_929033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929039 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 10]
def baseStart_929039 : Nat := 118140960795 + 929039 * 2 ^ 59
def prefixEnd_929039 : Nat := 4983230072969 + 3 ^ 40 * 929039 * 2
def baseEnd_929039 : Nat := 159014517924165288113311

theorem tailTrace_929039 : CollatzResearch.WordTrace tailWord_929039 prefixEnd_929039 159014517924165288113311 := by
  unfold tailWord_929039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33884836081257845074166171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22589890720838563382777447 33884836081257845074166171)
  ·
    refine ⟨50827254121886767611249257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33884836081257845074166171 50827254121886767611249257)
    ·
      refine ⟨38120440591415075708436943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50827254121886767611249257 38120440591415075708436943)
      ·
        refine ⟨57180660887122613562655415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38120440591415075708436943 57180660887122613562655415)
        ·
          refine ⟨85770991330683920343983123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57180660887122613562655415 85770991330683920343983123)
          ·
            refine ⟨128656486996025880515974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85770991330683920343983123 128656486996025880515974685)
            ·
              refine ⟨48246182623509705193490507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128656486996025880515974685 48246182623509705193490507)
              ·
                refine ⟨72369273935264557790235761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48246182623509705193490507 72369273935264557790235761)
                ·
                  refine ⟨54276955451448418342676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72369273935264557790235761 54276955451448418342676821)
                  ·
                    refine ⟨159014517924165288113311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 54276955451448418342676821 159014517924165288113311)
                    ·
                      rfl

theorem cell23_929039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_929039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929039 prefixEnd_929039 := by exact prefixLift 929039
  have htrace : WordTrace (prefixWord ++ tailWord_929039) baseStart_929039 baseEnd_929039 := by
    simpa [prefixWord, tailWord_929039, baseEnd_929039] using wordTrace_append hprefix tailTrace_929039
  have hstable : (prefixWord ++ tailWord_929039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929039).length < 2 ^ (prefixWord ++ tailWord_929039).sum := by decide
  have hdescent : baseEnd_929039 < baseStart_929039 := by decide
  rcases family_descends (prefixWord ++ tailWord_929039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929073 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_929073 : Nat := 118140960795 + 929073 * 2 ^ 59
def prefixEnd_929073 : Nat := 4983230072969 + 3 ^ 40 * 929073 * 2
def baseEnd_929073 : Nat := 159020337371582910438259

theorem tailTrace_929073 : CollatzResearch.WordTrace tailWord_929073 prefixEnd_929073 159020337371582910438259 := by
  unfold tailWord_929073
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886076163134668880903873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22590717442089779253935915 33886076163134668880903873)
  ·
    refine ⟨25414557122351001660677905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33886076163134668880903873 25414557122351001660677905)
    ·
      refine ⟨19060917841763251245508429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25414557122351001660677905 19060917841763251245508429)
      ·
        refine ⟨7147844190661219217065661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19060917841763251245508429 7147844190661219217065661)
        ·
          refine ⟨2680441571497957206399623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7147844190661219217065661 2680441571497957206399623)
          ·
            refine ⟨4020662357246935809599435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680441571497957206399623 4020662357246935809599435)
            ·
              refine ⟨6030993535870403714399153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020662357246935809599435 6030993535870403714399153)
              ·
                refine ⟨4523245151902802785799365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030993535870403714399153 4523245151902802785799365)
                ·
                  refine ⟨848108465981775522337381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4523245151902802785799365 848108465981775522337381)
                  ·
                    refine ⟨159020337371582910438259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848108465981775522337381 159020337371582910438259)
                    ·
                      rfl

theorem cell23_929073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_929073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929073 prefixEnd_929073 := by exact prefixLift 929073
  have htrace : WordTrace (prefixWord ++ tailWord_929073) baseStart_929073 baseEnd_929073 := by
    simpa [prefixWord, tailWord_929073, baseEnd_929073] using wordTrace_append hprefix tailTrace_929073
  have hstable : (prefixWord ++ tailWord_929073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929073).length < 2 ^ (prefixWord ++ tailWord_929073).sum := by decide
  have hdescent : baseEnd_929073 < baseStart_929073 := by decide
  rcases family_descends (prefixWord ++ tailWord_929073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929074 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_929074 : Nat := 118140960795 + 929074 * 2 ^ 59
def prefixEnd_929074 : Nat := 4983230072969 + 3 ^ 40 * 929074 * 2
def baseEnd_929074 : Nat := 477061525595403227402273

theorem tailTrace_929074 : CollatzResearch.WordTrace tailWord_929074 prefixEnd_929074 477061525595403227402273 := by
  unfold tailWord_929074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471528159032761512922569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22590741757420697367793517 8471528159032761512922569)
  ·
    refine ⟨6353646119274571134691927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8471528159032761512922569 6353646119274571134691927)
    ·
      refine ⟨9530469178911856702037891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353646119274571134691927 9530469178911856702037891)
      ·
        refine ⟨14295703768367785053056837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530469178911856702037891 14295703768367785053056837)
        ·
          refine ⟨2680444456568959697448157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14295703768367785053056837 2680444456568959697448157)
          ·
            refine ⟨1005166671213359886543059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2680444456568959697448157 1005166671213359886543059)
            ·
              refine ⟨1507750006820039829814589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005166671213359886543059 1507750006820039829814589)
              ·
                refine ⟨565406252557514936180471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507750006820039829814589 565406252557514936180471)
                ·
                  refine ⟨848109378836272404270707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565406252557514936180471 848109378836272404270707)
                  ·
                    refine ⟨1272164068254408606406061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 848109378836272404270707 1272164068254408606406061)
                    ·
                      refine ⟨477061525595403227402273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1272164068254408606406061 477061525595403227402273)
                      ·
                        rfl

theorem cell23_929074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_929074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929074 prefixEnd_929074 := by exact prefixLift 929074
  have htrace : WordTrace (prefixWord ++ tailWord_929074) baseStart_929074 baseEnd_929074 := by
    simpa [prefixWord, tailWord_929074, baseEnd_929074] using wordTrace_append hprefix tailTrace_929074
  have hstable : (prefixWord ++ tailWord_929074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929074).length < 2 ^ (prefixWord ++ tailWord_929074).sum := by decide
  have hdescent : baseEnd_929074 < baseStart_929074 := by decide
  rcases family_descends (prefixWord ++ tailWord_929074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929097 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 1, 2, 2]
def baseStart_929097 : Nat := 118140960795 + 929097 * 2 ^ 59
def prefixEnd_929097 : Nat := 4983230072969 + 3 ^ 40 * 929097 * 2
def baseEnd_929097 : Nat := 477073335650456637414667

theorem tailTrace_929097 : CollatzResearch.WordTrace tailWord_929097 prefixEnd_929097 477073335650456637414667 := by
  unfold tailWord_929097
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886951515047720979777545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22591301010031813986518363 33886951515047720979777545)
  ·
    refine ⟨25415213636285790734833159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33886951515047720979777545 25415213636285790734833159)
    ·
      refine ⟨38122820454428686102249739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25415213636285790734833159 38122820454428686102249739)
      ·
        refine ⟨57184230681643029153374609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38122820454428686102249739 57184230681643029153374609)
        ·
          refine ⟨42888173011232271865030957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57184230681643029153374609 42888173011232271865030957)
          ·
            refine ⟨16083064879212101949386609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42888173011232271865030957 16083064879212101949386609)
            ·
              refine ⟨12062298659409076462039957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16083064879212101949386609 12062298659409076462039957)
              ·
                refine ⟨565420249659800459158123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12062298659409076462039957 565420249659800459158123)
                ·
                  refine ⟨848130374489700688737185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565420249659800459158123 848130374489700688737185)
                  ·
                    refine ⟨636097780867275516552889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848130374489700688737185 636097780867275516552889)
                    ·
                      refine ⟨477073335650456637414667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636097780867275516552889 477073335650456637414667)
                      ·
                        rfl

theorem cell23_929097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 2, 2].length) (baseStart_929097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929097 prefixEnd_929097 := by exact prefixLift 929097
  have htrace : WordTrace (prefixWord ++ tailWord_929097) baseStart_929097 baseEnd_929097 := by
    simpa [prefixWord, tailWord_929097, baseEnd_929097] using wordTrace_append hprefix tailTrace_929097
  have hstable : (prefixWord ++ tailWord_929097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929097).length < 2 ^ (prefixWord ++ tailWord_929097).sum := by decide
  have hdescent : baseEnd_929097 < baseStart_929097 := by decide
  rcases family_descends (prefixWord ++ tailWord_929097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929106 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_929106 : Nat := 118140960795 + 929106 * 2 ^ 59
def prefixEnd_929106 : Nat := 4983230072969 + 3 ^ 40 * 929106 * 2
def baseEnd_929106 : Nat := 477077956976347102202125

theorem tailTrace_929106 : CollatzResearch.WordTrace tailWord_929106 prefixEnd_929106 477077956976347102202125 := by
  unfold tailWord_929106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471819943003778879213793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22591519848010077011236781 8471819943003778879213793)
  ·
    refine ⟨6353864957252834159410345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8471819943003778879213793 6353864957252834159410345)
    ·
      refine ⟨4765398717939625619557759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6353864957252834159410345 4765398717939625619557759)
      ·
        refine ⟨7148098076909438429336639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765398717939625619557759 7148098076909438429336639)
        ·
          refine ⟨10722147115364157644004959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148098076909438429336639 10722147115364157644004959)
          ·
            refine ⟨16083220673046236466007439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722147115364157644004959 16083220673046236466007439)
            ·
              refine ⟨24124831009569354699011159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083220673046236466007439 24124831009569354699011159)
              ·
                refine ⟨36187246514354032048516739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24124831009569354699011159 36187246514354032048516739)
                ·
                  refine ⟨54280869771531048072775109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36187246514354032048516739 54280869771531048072775109)
                  ·
                    refine ⟨10177663082162071513645333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54280869771531048072775109 10177663082162071513645333)
                    ·
                      refine ⟨477077956976347102202125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10177663082162071513645333 477077956976347102202125)
                      ·
                        rfl

theorem cell23_929106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_929106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929106 prefixEnd_929106 := by exact prefixLift 929106
  have htrace : WordTrace (prefixWord ++ tailWord_929106) baseStart_929106 baseEnd_929106 := by
    simpa [prefixWord, tailWord_929106, baseEnd_929106] using wordTrace_append hprefix tailTrace_929106
  have hstable : (prefixWord ++ tailWord_929106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929106).length < 2 ^ (prefixWord ++ tailWord_929106).sum := by decide
  have hdescent : baseEnd_929106 < baseStart_929106 := by decide
  rcases family_descends (prefixWord ++ tailWord_929106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929134 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_929134 : Nat := 118140960795 + 929134 * 2 ^ 59
def prefixEnd_929134 : Nat := 4983230072969 + 3 ^ 40 * 929134 * 2
def baseEnd_929134 : Nat := 477092334434672992651997

theorem tailTrace_929134 : CollatzResearch.WordTrace tailWord_929134 prefixEnd_929134 477092334434672992651997 := by
  unfold tailWord_929134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236037626989209537359307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22592200677275784199249637 4236037626989209537359307)
  ·
    refine ⟨6354056440483814306038961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236037626989209537359307 6354056440483814306038961)
    ·
      refine ⟨4765542330362860729529221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6354056440483814306038961 4765542330362860729529221)
      ·
        refine ⟨893539186943036386786729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4765542330362860729529221 893539186943036386786729)
        ·
          refine ⟨670154390207277290090047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893539186943036386786729 670154390207277290090047)
          ·
            refine ⟨1005231585310915935135071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670154390207277290090047 1005231585310915935135071)
            ·
              refine ⟨1507847377966373902702607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005231585310915935135071 1507847377966373902702607)
              ·
                refine ⟨2261771066949560854053911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507847377966373902702607 2261771066949560854053911)
                ·
                  refine ⟨3392656600424341281080867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261771066949560854053911 3392656600424341281080867)
                  ·
                    refine ⟨5088984900636511921621301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392656600424341281080867 5088984900636511921621301)
                    ·
                      refine ⟨477092334434672992651997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5088984900636511921621301 477092334434672992651997)
                      ·
                        rfl

theorem cell23_929134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_929134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929134 prefixEnd_929134 := by exact prefixLift 929134
  have htrace : WordTrace (prefixWord ++ tailWord_929134) baseStart_929134 baseEnd_929134 := by
    simpa [prefixWord, tailWord_929134, baseEnd_929134] using wordTrace_append hprefix tailTrace_929134
  have hstable : (prefixWord ++ tailWord_929134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929134).length < 2 ^ (prefixWord ++ tailWord_929134).sum := by decide
  have hdescent : baseEnd_929134 < baseStart_929134 := by decide
  rcases family_descends (prefixWord ++ tailWord_929134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929146 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_929146 : Nat := 118140960795 + 929146 * 2 ^ 59
def prefixEnd_929146 : Nat := 4983230072969 + 3 ^ 40 * 929146 * 2
def baseEnd_929146 : Nat := 159032832067508981900647

theorem tailTrace_929146 : CollatzResearch.WordTrace tailWord_929146 prefixEnd_929146 159032832067508981900647 := by
  unfold tailWord_929146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472184672967550587077823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22592492461246801565540861 8472184672967550587077823)
  ·
    refine ⟨12708277009451325880616735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472184672967550587077823 12708277009451325880616735)
    ·
      refine ⟨19062415514176988820925103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708277009451325880616735 19062415514176988820925103)
      ·
        refine ⟨28593623271265483231387655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19062415514176988820925103 28593623271265483231387655)
        ·
          refine ⟨42890434906898224847081483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28593623271265483231387655 42890434906898224847081483)
          ·
            refine ⟨64335652360347337270622225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42890434906898224847081483 64335652360347337270622225)
            ·
              refine ⟨48251739270260502952966669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64335652360347337270622225 48251739270260502952966669)
              ·
                refine ⟨18094402226347688607362501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48251739270260502952966669 18094402226347688607362501)
                ·
                  refine ⟨3392700417440191613880469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18094402226347688607362501 3392700417440191613880469)
                  ·
                    refine ⟨159032832067508981900647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3392700417440191613880469 159032832067508981900647)
                    ·
                      rfl

theorem cell23_929146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_929146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929146 prefixEnd_929146 := by exact prefixLift 929146
  have htrace : WordTrace (prefixWord ++ tailWord_929146) baseStart_929146 baseEnd_929146 := by
    simpa [prefixWord, tailWord_929146, baseEnd_929146] using wordTrace_append hprefix tailTrace_929146
  have hstable : (prefixWord ++ tailWord_929146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929146).length < 2 ^ (prefixWord ++ tailWord_929146).sum := by decide
  have hdescent : baseEnd_929146 < baseStart_929146 := by decide
  rcases family_descends (prefixWord ++ tailWord_929146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929230 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_929230 : Nat := 118140960795 + 929230 * 2 ^ 59
def prefixEnd_929230 : Nat := 4983230072969 + 3 ^ 40 * 929230 * 2
def baseEnd_929230 : Nat := 477141628577504617051555

theorem tailTrace_929230 : CollatzResearch.WordTrace tailWord_929230 prefixEnd_929230 477141628577504617051555 := by
  unfold tailWord_929230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236475302945735586796143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22594534949043923129579429 4236475302945735586796143)
  ·
    refine ⟨6354712954418603380194215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236475302945735586796143 6354712954418603380194215)
    ·
      refine ⟨9532069431627905070291323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354712954418603380194215 9532069431627905070291323)
      ·
        refine ⟨14298104147441857605436985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532069431627905070291323 14298104147441857605436985)
        ·
          refine ⟨10723578110581393204077739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14298104147441857605436985 10723578110581393204077739)
          ·
            refine ⟨16085367165872089806116609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723578110581393204077739 16085367165872089806116609)
            ·
              refine ⟨12064025374404067354587457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085367165872089806116609 12064025374404067354587457)
              ·
                refine ⟨9048019030803050515940593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064025374404067354587457 9048019030803050515940593)
                ·
                  refine ⟨6786014273102287886955445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048019030803050515940593 6786014273102287886955445)
                  ·
                    refine ⟨636188838103339489402073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6786014273102287886955445 636188838103339489402073)
                    ·
                      refine ⟨477141628577504617051555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636188838103339489402073 477141628577504617051555)
                      ·
                        rfl

theorem cell23_929230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_929230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929230 prefixEnd_929230 := by exact prefixLift 929230
  have htrace : WordTrace (prefixWord ++ tailWord_929230) baseStart_929230 baseEnd_929230 := by
    simpa [prefixWord, tailWord_929230, baseEnd_929230] using wordTrace_append hprefix tailTrace_929230
  have hstable : (prefixWord ++ tailWord_929230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929230).length < 2 ^ (prefixWord ++ tailWord_929230).sum := by decide
  have hdescent : baseEnd_929230 < baseStart_929230 := by decide
  rcases family_descends (prefixWord ++ tailWord_929230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929260 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_929260 : Nat := 118140960795 + 929260 * 2 ^ 59
def prefixEnd_929260 : Nat := 4983230072969 + 3 ^ 40 * 929260 * 2
def baseEnd_929260 : Nat := 477157032997139499676417

theorem tailTrace_929260 : CollatzResearch.WordTrace tailWord_929260 prefixEnd_929260 477157032997139499676417 := by
  unfold tailWord_929260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946448306728599908980617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22595264408971466545307489 16946448306728599908980617)
  ·
    refine ⟨12709836230046449931735463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16946448306728599908980617 12709836230046449931735463)
    ·
      refine ⟨19064754345069674897603195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709836230046449931735463 19064754345069674897603195)
      ·
        refine ⟨28597131517604512346404793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064754345069674897603195 28597131517604512346404793)
        ·
          refine ⟨21447848638203384259803595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28597131517604512346404793 21447848638203384259803595)
          ·
            refine ⟨32171772957305076389705393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21447848638203384259803595 32171772957305076389705393)
            ·
              refine ⟨24128829717978807292279045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32171772957305076389705393 24128829717978807292279045)
              ·
                refine ⟨4524155572121026367302321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24128829717978807292279045 4524155572121026367302321)
                ·
                  refine ⟨3393116679090769775476741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524155572121026367302321 3393116679090769775476741)
                  ·
                    refine ⟨636209377329519332901889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393116679090769775476741 636209377329519332901889)
                    ·
                      refine ⟨477157032997139499676417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636209377329519332901889 477157032997139499676417)
                      ·
                        rfl

theorem cell23_929260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_929260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929260 prefixEnd_929260 := by exact prefixLift 929260
  have htrace : WordTrace (prefixWord ++ tailWord_929260) baseStart_929260 baseEnd_929260 := by
    simpa [prefixWord, tailWord_929260, baseEnd_929260] using wordTrace_append hprefix tailTrace_929260
  have hstable : (prefixWord ++ tailWord_929260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929260).length < 2 ^ (prefixWord ++ tailWord_929260).sum := by decide
  have hdescent : baseEnd_929260 < baseStart_929260 := by decide
  rcases family_descends (prefixWord ++ tailWord_929260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929360 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_929360 : Nat := 118140960795 + 929360 * 2 ^ 59
def prefixEnd_929360 : Nat := 4983230072969 + 3 ^ 40 * 929360 * 2
def baseEnd_929360 : Nat := 159069460354196369475319

theorem tailTrace_929360 : CollatzResearch.WordTrace tailWord_929360 prefixEnd_929360 159069460354196369475319 := by
  unfold tailWord_929360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948271956547458448300767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22597695942063277931067689 16948271956547458448300767)
  ·
    refine ⟨25422407934821187672451151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16948271956547458448300767 25422407934821187672451151)
    ·
      refine ⟨38133611902231781508676727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25422407934821187672451151 38133611902231781508676727)
      ·
        refine ⟨57200417853347672263015091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38133611902231781508676727 57200417853347672263015091)
        ·
          refine ⟨85800626780021508394522637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57200417853347672263015091 85800626780021508394522637)
          ·
            refine ⟨32175235042508065647945989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85800626780021508394522637 32175235042508065647945989)
            ·
              refine ⟨6032856570470262308989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32175235042508065647945989 6032856570470262308989873)
              ·
                refine ⟨4524642427852696731742405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032856570470262308989873 4524642427852696731742405)
                ·
                  refine ⟨848370455222380637201701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4524642427852696731742405 848370455222380637201701)
                  ·
                    refine ⟨159069460354196369475319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848370455222380637201701 159069460354196369475319)
                    ·
                      rfl

theorem cell23_929360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_929360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929360 prefixEnd_929360 := by exact prefixLift 929360
  have htrace : WordTrace (prefixWord ++ tailWord_929360) baseStart_929360 baseEnd_929360 := by
    simpa [prefixWord, tailWord_929360, baseEnd_929360] using wordTrace_append hprefix tailTrace_929360
  have hstable : (prefixWord ++ tailWord_929360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929360).length < 2 ^ (prefixWord ++ tailWord_929360).sum := by decide
  have hdescent : baseEnd_929360 < baseStart_929360 := by decide
  rcases family_descends (prefixWord ++ tailWord_929360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929367 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_929367 : Nat := 118140960795 + 929367 * 2 ^ 59
def prefixEnd_929367 : Nat := 4983230072969 + 3 ^ 40 * 929367 * 2
def baseEnd_929367 : Nat := 477211975427170581038425

theorem tailTrace_929367 : CollatzResearch.WordTrace tailWord_929367 prefixEnd_929367 477211975427170581038425 := by
  unfold tailWord_929367
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896799224069557092106355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22597866149379704728070903 33896799224069557092106355)
  ·
    refine ⟨50845198836104335638159533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33896799224069557092106355 50845198836104335638159533)
    ·
      refine ⟨19066949563539125864309825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50845198836104335638159533 19066949563539125864309825)
      ·
        refine ⟨14300212172654344398232369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19066949563539125864309825 14300212172654344398232369)
        ·
          refine ⟨10725159129490758298674277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14300212172654344398232369 10725159129490758298674277)
          ·
            refine ⟨2010967336779517181001427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10725159129490758298674277 2010967336779517181001427)
            ·
              refine ⟨3016451005169275771502141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010967336779517181001427 3016451005169275771502141)
              ·
                refine ⟨1131169126938478414313303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016451005169275771502141 1131169126938478414313303)
                ·
                  refine ⟨1696753690407717621469955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131169126938478414313303 1696753690407717621469955)
                  ·
                    refine ⟨2545130535611576432204933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1696753690407717621469955 2545130535611576432204933)
                    ·
                      refine ⟨477211975427170581038425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2545130535611576432204933 477211975427170581038425)
                      ·
                        rfl

theorem cell23_929367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_929367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929367 prefixEnd_929367 := by exact prefixLift 929367
  have htrace : WordTrace (prefixWord ++ tailWord_929367) baseStart_929367 baseEnd_929367 := by
    simpa [prefixWord, tailWord_929367, baseEnd_929367] using wordTrace_append hprefix tailTrace_929367
  have hstable : (prefixWord ++ tailWord_929367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929367).length < 2 ^ (prefixWord ++ tailWord_929367).sum := by decide
  have hdescent : baseEnd_929367 < baseStart_929367 := by decide
  rcases family_descends (prefixWord ++ tailWord_929367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929397 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_929397 : Nat := 118140960795 + 929397 * 2 ^ 59
def prefixEnd_929397 : Nat := 4983230072969 + 3 ^ 40 * 929397 * 2
def baseEnd_929397 : Nat := 477227379846805463663287

theorem tailTrace_929397 : CollatzResearch.WordTrace tailWord_929397 prefixEnd_929397 477227379846805463663287 := by
  unfold tailWord_929397
  simp only [CollatzResearch.WordTrace]
  refine ⟨33897893413960872215698445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22598595609307248143798963 33897893413960872215698445)
  ·
    refine ⟨12711710030235327080886917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33897893413960872215698445 12711710030235327080886917)
    ·
      refine ⟨2383445630669123827666297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12711710030235327080886917 2383445630669123827666297)
      ·
        refine ⟨1787584223001842870749723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383445630669123827666297 1787584223001842870749723)
        ·
          refine ⟨2681376334502764306124585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787584223001842870749723 2681376334502764306124585)
          ·
            refine ⟨2011032250877073229593439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681376334502764306124585 2011032250877073229593439)
            ·
              refine ⟨3016548376315609844390159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011032250877073229593439 3016548376315609844390159)
              ·
                refine ⟨4524822564473414766585239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016548376315609844390159 4524822564473414766585239)
                ·
                  refine ⟨6787233846710122149877859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524822564473414766585239 6787233846710122149877859)
                  ·
                    refine ⟨10180850770065183224816789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6787233846710122149877859 10180850770065183224816789)
                    ·
                      refine ⟨477227379846805463663287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10180850770065183224816789 477227379846805463663287)
                      ·
                        rfl

theorem cell23_929397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_929397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929397 prefixEnd_929397 := by exact prefixLift 929397
  have htrace : WordTrace (prefixWord ++ tailWord_929397) baseStart_929397 baseEnd_929397 := by
    simpa [prefixWord, tailWord_929397, baseEnd_929397] using wordTrace_append hprefix tailTrace_929397
  have hstable : (prefixWord ++ tailWord_929397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929397).length < 2 ^ (prefixWord ++ tailWord_929397).sum := by decide
  have hdescent : baseEnd_929397 < baseStart_929397 := by decide
  rcases family_descends (prefixWord ++ tailWord_929397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929417 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_929417 : Nat := 118140960795 + 929417 * 2 ^ 59
def prefixEnd_929417 : Nat := 4983230072969 + 3 ^ 40 * 929417 * 2
def baseEnd_929417 : Nat := 477237649459895385413195

theorem tailTrace_929417 : CollatzResearch.WordTrace tailWord_929417 prefixEnd_929417 477237649459895385413195 := by
  unfold tailWord_929417
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898622873888415631426505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22599081915925610420951003 33898622873888415631426505)
  ·
    refine ⟨25423967155416311723569879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33898622873888415631426505 25423967155416311723569879)
    ·
      refine ⟨38135950733124467585354819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423967155416311723569879 38135950733124467585354819)
      ·
        refine ⟨57203926099686701378032229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38135950733124467585354819 57203926099686701378032229)
        ·
          refine ⟨10725736143691256508381043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57203926099686701378032229 10725736143691256508381043)
          ·
            refine ⟨16088604215536884762571565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725736143691256508381043 16088604215536884762571565)
            ·
              refine ⟨6033226580826331785964337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16088604215536884762571565 6033226580826331785964337)
              ·
                refine ⟨4524919935619748839473253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033226580826331785964337 4524919935619748839473253)
                ·
                  refine ⟨848422487928702907401235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4524919935619748839473253 848422487928702907401235)
                  ·
                    refine ⟨1272633731893054361101853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 848422487928702907401235 1272633731893054361101853)
                    ·
                      refine ⟨477237649459895385413195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1272633731893054361101853 477237649459895385413195)
                      ·
                        rfl

theorem cell23_929417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_929417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929417 prefixEnd_929417 := by exact prefixLift 929417
  have htrace : WordTrace (prefixWord ++ tailWord_929417) baseStart_929417 baseEnd_929417 := by
    simpa [prefixWord, tailWord_929417, baseEnd_929417] using wordTrace_append hprefix tailTrace_929417
  have hstable : (prefixWord ++ tailWord_929417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929417).length < 2 ^ (prefixWord ++ tailWord_929417).sum := by decide
  have hdescent : baseEnd_929417 < baseStart_929417 := by decide
  rcases family_descends (prefixWord ++ tailWord_929417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929418 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_929418 : Nat := 118140960795 + 929418 * 2 ^ 59
def prefixEnd_929418 : Nat := 4983230072969 + 3 ^ 40 * 929418 * 2
def baseEnd_929418 : Nat := 477238162940549881500691

theorem tailTrace_929418 : CollatzResearch.WordTrace tailWord_929418 prefixEnd_929418 477238162940549881500691 := by
  unfold tailWord_929418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474664836721198200553227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22599106231256528534808605 8474664836721198200553227)
  ·
    refine ⟨12711997255081797300829841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8474664836721198200553227 12711997255081797300829841)
    ·
      refine ⟨9533997941311347975622381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12711997255081797300829841 9533997941311347975622381)
      ·
        refine ⟨3575249227991755490858393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9533997941311347975622381 3575249227991755490858393)
        ·
          refine ⟨2681436920993816618143795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575249227991755490858393 2681436920993816618143795)
          ·
            refine ⟨4022155381490724927215693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681436920993816618143795 4022155381490724927215693)
            ·
              refine ⟨1508308268059021847705885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4022155381490724927215693 1508308268059021847705885)
              ·
                refine ⟨565615600522133192889707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1508308268059021847705885 565615600522133192889707)
                ·
                  refine ⟨848423400783199789334561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565615600522133192889707 848423400783199789334561)
                  ·
                    refine ⟨636317550587399842000921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848423400783199789334561 636317550587399842000921)
                    ·
                      refine ⟨477238162940549881500691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636317550587399842000921 477238162940549881500691)
                      ·
                        rfl

theorem cell23_929418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_929418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929418 prefixEnd_929418 := by exact prefixLift 929418
  have htrace : WordTrace (prefixWord ++ tailWord_929418) baseStart_929418 baseEnd_929418 := by
    simpa [prefixWord, tailWord_929418, baseEnd_929418] using wordTrace_append hprefix tailTrace_929418
  have hstable : (prefixWord ++ tailWord_929418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929418).length < 2 ^ (prefixWord ++ tailWord_929418).sum := by decide
  have hdescent : baseEnd_929418 < baseStart_929418 := by decide
  rcases family_descends (prefixWord ++ tailWord_929418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929461 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_929461 : Nat := 118140960795 + 929461 * 2 ^ 59
def prefixEnd_929461 : Nat := 4983230072969 + 3 ^ 40 * 929461 * 2
def baseEnd_929461 : Nat := 477260242608693213262993

theorem tailTrace_929461 : CollatzResearch.WordTrace tailWord_929461 prefixEnd_929461 477260242608693213262993 := by
  unfold tailWord_929461
  simp only [CollatzResearch.WordTrace]
  refine ⟨33900227685729011146028237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22600151790486007430685491 33900227685729011146028237)
  ·
    refine ⟨12712585382148379179760589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33900227685729011146028237 12712585382148379179760589)
    ·
      refine ⟨4767219518305642192410221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12712585382148379179760589 4767219518305642192410221)
      ·
        refine ⟨1787707319364615822153833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4767219518305642192410221 1787707319364615822153833)
        ·
          refine ⟨1340780489523461866615375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787707319364615822153833 1340780489523461866615375)
          ·
            refine ⟨2011170734285192799923063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340780489523461866615375 2011170734285192799923063)
            ·
              refine ⟨3016756101427789199884595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011170734285192799923063 3016756101427789199884595)
              ·
                refine ⟨4525134152141683799826893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016756101427789199884595 4525134152141683799826893)
                ·
                  refine ⟨1696925307053131424935085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4525134152141683799826893 1696925307053131424935085)
                  ·
                    refine ⟨636346990144924284350657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696925307053131424935085 636346990144924284350657)
                    ·
                      refine ⟨477260242608693213262993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636346990144924284350657 477260242608693213262993)
                      ·
                        rfl

theorem cell23_929461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_929461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929461 prefixEnd_929461 := by exact prefixLift 929461
  have htrace : WordTrace (prefixWord ++ tailWord_929461) baseStart_929461 baseEnd_929461 := by
    simpa [prefixWord, tailWord_929461, baseEnd_929461] using wordTrace_append hprefix tailTrace_929461
  have hstable : (prefixWord ++ tailWord_929461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929461).length < 2 ^ (prefixWord ++ tailWord_929461).sum := by decide
  have hdescent : baseEnd_929461 < baseStart_929461 := by decide
  rcases family_descends (prefixWord ++ tailWord_929461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929520 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_929520 : Nat := 118140960795 + 929520 * 2 ^ 59
def prefixEnd_929520 : Nat := 4983230072969 + 3 ^ 40 * 929520 * 2
def baseEnd_929520 : Nat := 477290537967308482425221

theorem tailTrace_929520 : CollatzResearch.WordTrace tailWord_929520 prefixEnd_929520 477290537967308482425221 := by
  unfold tailWord_929520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951189796257632111213007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22601586395010176148284009 16951189796257632111213007)
  ·
    refine ⟨25426784694386448166819511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16951189796257632111213007 25426784694386448166819511)
    ·
      refine ⟨38140177041579672250229267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25426784694386448166819511 38140177041579672250229267)
      ·
        refine ⟨57210265562369508375343901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38140177041579672250229267 57210265562369508375343901)
        ·
          refine ⟨21453849585888565640753963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57210265562369508375343901 21453849585888565640753963)
          ·
            refine ⟨32180774378832848461130945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453849585888565640753963 32180774378832848461130945)
            ·
              refine ⟨24135580784124636345848209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180774378832848461130945 24135580784124636345848209)
              ·
                refine ⟨18101685588093477259386157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24135580784124636345848209 18101685588093477259386157)
                ·
                  refine ⟨6788132095535053972269809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18101685588093477259386157 6788132095535053972269809)
                  ·
                    refine ⟨5091099071651290479202357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788132095535053972269809 5091099071651290479202357)
                    ·
                      refine ⟨477290537967308482425221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5091099071651290479202357 477290537967308482425221)
                      ·
                        rfl

theorem cell23_929520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_929520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929520 prefixEnd_929520 := by exact prefixLift 929520
  have htrace : WordTrace (prefixWord ++ tailWord_929520) baseStart_929520 baseEnd_929520 := by
    simpa [prefixWord, tailWord_929520, baseEnd_929520] using wordTrace_append hprefix tailTrace_929520
  have hstable : (prefixWord ++ tailWord_929520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929520).length < 2 ^ (prefixWord ++ tailWord_929520).sum := by decide
  have hdescent : baseEnd_929520 < baseStart_929520 := by decide
  rcases family_descends (prefixWord ++ tailWord_929520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929527 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 2, 5]
def baseStart_929527 : Nat := 118140960795 + 929527 * 2 ^ 59
def prefixEnd_929527 : Nat := 4983230072969 + 3 ^ 40 * 929527 * 2
def baseEnd_929527 : Nat := 159098044110629985012563

theorem tailTrace_929527 : CollatzResearch.WordTrace tailWord_929527 prefixEnd_929527 159098044110629985012563 := by
  unfold tailWord_929527
  simp only [CollatzResearch.WordTrace]
  refine ⟨33902634903489904417930835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22601756602326602945287223 33902634903489904417930835)
  ·
    refine ⟨50853952355234856626896253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33902634903489904417930835 50853952355234856626896253)
    ·
      refine ⟨19070232133213071235086095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50853952355234856626896253 19070232133213071235086095)
      ·
        refine ⟨28605348199819606852629143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070232133213071235086095 28605348199819606852629143)
        ·
          refine ⟨42908022299729410278943715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605348199819606852629143 42908022299729410278943715)
          ·
            refine ⟨64362033449594115418415573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42908022299729410278943715 64362033449594115418415573)
            ·
              refine ⟨1508485158974862080119115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64362033449594115418415573 1508485158974862080119115)
              ·
                refine ⟨2262727738462293120178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508485158974862080119115 2262727738462293120178673)
                ·
                  refine ⟨1697045803846719840134005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262727738462293120178673 1697045803846719840134005)
                  ·
                    refine ⟨159098044110629985012563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1697045803846719840134005 159098044110629985012563)
                    ·
                      rfl

theorem cell23_929527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_929527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929527 prefixEnd_929527 := by exact prefixLift 929527
  have htrace : WordTrace (prefixWord ++ tailWord_929527) baseStart_929527 baseEnd_929527 := by
    simpa [prefixWord, tailWord_929527, baseEnd_929527] using wordTrace_append hprefix tailTrace_929527
  have hstable : (prefixWord ++ tailWord_929527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929527).length < 2 ^ (prefixWord ++ tailWord_929527).sum := by decide
  have hdescent : baseEnd_929527 < baseStart_929527 := by decide
  rcases family_descends (prefixWord ++ tailWord_929527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929547 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4]
def baseStart_929547 : Nat := 118140960795 + 929547 * 2 ^ 59
def prefixEnd_929547 : Nat := 4983230072969 + 3 ^ 40 * 929547 * 2
def baseEnd_929547 : Nat := 477304401944979876787597

theorem tailTrace_929547 : CollatzResearch.WordTrace tailWord_929547 prefixEnd_929547 477304401944979876787597 := by
  unfold tailWord_929547
  simp only [CollatzResearch.WordTrace]
  refine ⟨33903364363417447833658895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22602242908944965222439263 33903364363417447833658895)
  ·
    refine ⟨50855046545126171750488343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33903364363417447833658895 50855046545126171750488343)
    ·
      refine ⟨76282569817689257625732515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50855046545126171750488343 76282569817689257625732515)
      ·
        refine ⟨114423854726533886438598773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76282569817689257625732515 114423854726533886438598773)
        ·
          refine ⟨10727236380612551853618635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114423854726533886438598773 10727236380612551853618635)
          ·
            refine ⟨16090854570918827780427953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10727236380612551853618635 16090854570918827780427953)
            ·
              refine ⟨12068140928189120835320965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16090854570918827780427953 12068140928189120835320965)
              ·
                refine ⟨2262776424035460156622681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12068140928189120835320965 2262776424035460156622681)
                ·
                  refine ⟨1697082318026595117467011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262776424035460156622681 1697082318026595117467011)
                  ·
                    refine ⟨2545623477039892676200517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1697082318026595117467011 2545623477039892676200517)
                    ·
                      refine ⟨477304401944979876787597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2545623477039892676200517 477304401944979876787597)
                      ·
                        rfl

theorem cell23_929547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_929547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929547 prefixEnd_929547 := by exact prefixLift 929547
  have htrace : WordTrace (prefixWord ++ tailWord_929547) baseStart_929547 baseEnd_929547 := by
    simpa [prefixWord, tailWord_929547, baseEnd_929547] using wordTrace_append hprefix tailTrace_929547
  have hstable : (prefixWord ++ tailWord_929547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929547).length < 2 ^ (prefixWord ++ tailWord_929547).sum := by decide
  have hdescent : baseEnd_929547 < baseStart_929547 := by decide
  rcases family_descends (prefixWord ++ tailWord_929547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929564 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_929564 : Nat := 118140960795 + 929564 * 2 ^ 59
def prefixEnd_929564 : Nat := 4983230072969 + 3 ^ 40 * 929564 * 2
def baseEnd_929564 : Nat := 477313131116106310275019

theorem tailTrace_929564 : CollatzResearch.WordTrace tailWord_929564 prefixEnd_929564 477313131116106310275019 := by
  unfold tailWord_929564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951992202177929868513873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22602656269570573158018497 16951992202177929868513873)
  ·
    refine ⟨12713994151633447401385405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16951992202177929868513873 12713994151633447401385405)
    ·
      refine ⟨4767747806862542775519527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12713994151633447401385405 4767747806862542775519527)
      ·
        refine ⟨7151621710293814163279291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767747806862542775519527 7151621710293814163279291)
        ·
          refine ⟨10727432565440721244918937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7151621710293814163279291 10727432565440721244918937)
          ·
            refine ⟨8045574424080540933689203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10727432565440721244918937 8045574424080540933689203)
            ·
              refine ⟨12068361636120811400533805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045574424080540933689203 12068361636120811400533805)
              ·
                refine ⟨4525635613545304275200177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12068361636120811400533805 4525635613545304275200177)
                ·
                  refine ⟨3394226710158978206400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525635613545304275200177 3394226710158978206400133)
                  ·
                    refine ⟨636417508154808413700025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394226710158978206400133 636417508154808413700025)
                    ·
                      refine ⟨477313131116106310275019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636417508154808413700025 477313131116106310275019)
                      ·
                        rfl

theorem cell23_929564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_929564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929564 prefixEnd_929564 := by exact prefixLift 929564
  have htrace : WordTrace (prefixWord ++ tailWord_929564) baseStart_929564 baseEnd_929564 := by
    simpa [prefixWord, tailWord_929564, baseEnd_929564] using wordTrace_append hprefix tailTrace_929564
  have hstable : (prefixWord ++ tailWord_929564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929564).length < 2 ^ (prefixWord ++ tailWord_929564).sum := by decide
  have hdescent : baseEnd_929564 < baseStart_929564 := by decide
  rcases family_descends (prefixWord ++ tailWord_929564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929567 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_929567 : Nat := 118140960795 + 929567 * 2 ^ 59
def prefixEnd_929567 : Nat := 4983230072969 + 3 ^ 40 * 929567 * 2
def baseEnd_929567 : Nat := 477314671558069798537505

theorem tailTrace_929567 : CollatzResearch.WordTrace tailWord_929567 prefixEnd_929567 477314671558069798537505 := by
  unfold tailWord_929567
  simp only [CollatzResearch.WordTrace]
  refine ⟨33904093823344991249386955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22602729215563327499591303 33904093823344991249386955)
  ·
    refine ⟨50856140735017486874080433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33904093823344991249386955 50856140735017486874080433)
    ·
      refine ⟨38142105551263115155560325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50856140735017486874080433 38142105551263115155560325)
      ·
        refine ⟨7151644790861834091667561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38142105551263115155560325 7151644790861834091667561)
        ·
          refine ⟨5363733593146375568750671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151644790861834091667561 5363733593146375568750671)
          ·
            refine ⟨8045600389719563353126007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363733593146375568750671 8045600389719563353126007)
            ·
              refine ⟨12068400584579345029689011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045600389719563353126007 12068400584579345029689011)
              ·
                refine ⟨18102600876869017544533517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068400584579345029689011 18102600876869017544533517)
                ·
                  refine ⟨6788475328825881579200069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18102600876869017544533517 6788475328825881579200069)
                  ·
                    refine ⟨1272839124154852796100013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788475328825881579200069 1272839124154852796100013)
                    ·
                      refine ⟨477314671558069798537505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1272839124154852796100013 477314671558069798537505)
                      ·
                        rfl

theorem cell23_929567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_929567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929567 prefixEnd_929567 := by exact prefixLift 929567
  have htrace : WordTrace (prefixWord ++ tailWord_929567) baseStart_929567 baseEnd_929567 := by
    simpa [prefixWord, tailWord_929567, baseEnd_929567] using wordTrace_append hprefix tailTrace_929567
  have hstable : (prefixWord ++ tailWord_929567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929567).length < 2 ^ (prefixWord ++ tailWord_929567).sum := by decide
  have hdescent : baseEnd_929567 < baseStart_929567 := by decide
  rcases family_descends (prefixWord ++ tailWord_929567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929608 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 1, 4]
def baseStart_929608 : Nat := 118140960795 + 929608 * 2 ^ 59
def prefixEnd_929608 : Nat := 4983230072969 + 3 ^ 40 * 929608 * 2
def baseEnd_929608 : Nat := 159111908088301379374939

theorem tailTrace_929608 : CollatzResearch.WordTrace tailWord_929608 prefixEnd_929608 159111908088301379374939 := by
  unfold tailWord_929608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952794608098227625814739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22603726144130970167752985 16952794608098227625814739)
  ·
    refine ⟨25429191912147341438722109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16952794608098227625814739 25429191912147341438722109)
    ·
      refine ⟨9535946967055253039520791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25429191912147341438722109 9535946967055253039520791)
      ·
        refine ⟨14303920450582879559281187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535946967055253039520791 14303920450582879559281187)
        ·
          refine ⟨21455880675874319338921781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303920450582879559281187 21455880675874319338921781)
          ·
            refine ⟨2011488813363217438023917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21455880675874319338921781 2011488813363217438023917)
            ·
              refine ⟨754308305011206539258969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2011488813363217438023917 754308305011206539258969)
              ·
                refine ⟨565731228758404904444227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754308305011206539258969 565731228758404904444227)
                ·
                  refine ⟨848596843137607356666341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565731228758404904444227 848596843137607356666341)
                  ·
                    refine ⟨159111908088301379374939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848596843137607356666341 159111908088301379374939)
                    ·
                      rfl

theorem cell23_929608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_929608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929608 prefixEnd_929608 := by exact prefixLift 929608
  have htrace : WordTrace (prefixWord ++ tailWord_929608) baseStart_929608 baseEnd_929608 := by
    simpa [prefixWord, tailWord_929608, baseEnd_929608] using wordTrace_append hprefix tailTrace_929608
  have hstable : (prefixWord ++ tailWord_929608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929608).length < 2 ^ (prefixWord ++ tailWord_929608).sum := by decide
  have hdescent : baseEnd_929608 < baseStart_929608 := by decide
  rcases family_descends (prefixWord ++ tailWord_929608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929621 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 6]
def baseStart_929621 : Nat := 118140960795 + 929621 * 2 ^ 59
def prefixEnd_929621 : Nat := 4983230072969 + 3 ^ 40 * 929621 * 2
def baseEnd_929621 : Nat := 53038044390379176362473

theorem tailTrace_929621 : CollatzResearch.WordTrace tailWord_929621 prefixEnd_929621 53038044390379176362473 := by
  unfold tailWord_929621
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906063365149358471852717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22604042243432905647901811 33906063365149358471852717)
  ·
    refine ⟨12714773761931009426944769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33906063365149358471852717 12714773761931009426944769)
    ·
      refine ⟨9536080321448257070208577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12714773761931009426944769 9536080321448257070208577)
      ·
        refine ⟨7152060241086192802656433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9536080321448257070208577 7152060241086192802656433)
        ·
          refine ⟨5364045180814644601992325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152060241086192802656433 5364045180814644601992325)
          ·
            refine ⟨1005758471402745862873561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5364045180814644601992325 1005758471402745862873561)
            ·
              refine ⟨754318853552059397155171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005758471402745862873561 754318853552059397155171)
              ·
                refine ⟨1131478280328089095732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754318853552059397155171 1131478280328089095732757)
                ·
                  refine ⟨53038044390379176362473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1131478280328089095732757 53038044390379176362473)
                  ·
                    rfl

theorem cell23_929621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_929621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929621 prefixEnd_929621 := by exact prefixLift 929621
  have htrace : WordTrace (prefixWord ++ tailWord_929621) baseStart_929621 baseEnd_929621 := by
    simpa [prefixWord, tailWord_929621, baseEnd_929621] using wordTrace_append hprefix tailTrace_929621
  have hstable : (prefixWord ++ tailWord_929621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929621).length < 2 ^ (prefixWord ++ tailWord_929621).sum := by decide
  have hdescent : baseEnd_929621 < baseStart_929621 := by decide
  rcases family_descends (prefixWord ++ tailWord_929621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929721 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_929721 : Nat := 118140960795 + 929721 * 2 ^ 59
def prefixEnd_929721 : Nat := 4983230072969 + 3 ^ 40 * 929721 * 2
def baseEnd_929721 : Nat := 477393747578862196011797

theorem tailTrace_929721 : CollatzResearch.WordTrace tailWord_929721 prefixEnd_929721 477393747578862196011797 := by
  unfold tailWord_929721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909710664787075550493017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22606473776524717033662011 33909710664787075550493017)
  ·
    refine ⟨25432282998590306662869763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33909710664787075550493017 25432282998590306662869763)
    ·
      refine ⟨38148424497885459994304645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25432282998590306662869763 38148424497885459994304645)
      ·
        refine ⟨7152829593353523748932121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38148424497885459994304645 7152829593353523748932121)
        ·
          refine ⟨5364622195015142811699091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152829593353523748932121 5364622195015142811699091)
          ·
            refine ⟨8046933292522714217548637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364622195015142811699091 8046933292522714217548637)
            ·
              refine ⟨3017599984696017831580739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8046933292522714217548637 3017599984696017831580739)
              ·
                refine ⟨4526399977044026747371109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017599984696017831580739 4526399977044026747371109)
                ·
                  refine ⟨848699995695755015132083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4526399977044026747371109 848699995695755015132083)
                  ·
                    refine ⟨1273049993543632522698125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 848699995695755015132083 1273049993543632522698125)
                    ·
                      refine ⟨477393747578862196011797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1273049993543632522698125 477393747578862196011797)
                      ·
                        rfl

theorem cell23_929721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_929721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929721 prefixEnd_929721 := by exact prefixLift 929721
  have htrace : WordTrace (prefixWord ++ tailWord_929721) baseStart_929721 baseEnd_929721 := by
    simpa [prefixWord, tailWord_929721, baseEnd_929721] using wordTrace_append hprefix tailTrace_929721
  have hstable : (prefixWord ++ tailWord_929721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929721).length < 2 ^ (prefixWord ++ tailWord_929721).sum := by decide
  have hdescent : baseEnd_929721 < baseStart_929721 := by decide
  rcases family_descends (prefixWord ++ tailWord_929721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929761 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_929761 : Nat := 118140960795 + 929761 * 2 ^ 59
def prefixEnd_929761 : Nat := 4983230072969 + 3 ^ 40 * 929761 * 2
def baseEnd_929761 : Nat := 477414286805042039511613

theorem tailTrace_929761 : CollatzResearch.WordTrace tailWord_929761 prefixEnd_929761 477414286805042039511613 := by
  unfold tailWord_929761
  simp only [CollatzResearch.WordTrace]
  refine ⟨33911169584642162381949137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22607446389761441587966091 33911169584642162381949137)
  ·
    refine ⟨25433377188481621786461853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33911169584642162381949137 25433377188481621786461853)
    ·
      refine ⟨9537516445680608169923195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25433377188481621786461853 9537516445680608169923195)
      ·
        refine ⟨14306274668520912254884793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9537516445680608169923195 14306274668520912254884793)
        ·
          refine ⟨10729706001390684191163595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14306274668520912254884793 10729706001390684191163595)
          ·
            refine ⟨16094559002086026286745393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729706001390684191163595 16094559002086026286745393)
            ·
              refine ⟨12070919251564519715059045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16094559002086026286745393 12070919251564519715059045)
              ·
                refine ⟨2263297359668347446573571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12070919251564519715059045 2263297359668347446573571)
                ·
                  refine ⟨3394946039502521169860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263297359668347446573571 3394946039502521169860357)
                  ·
                    refine ⟨636552382406722719348817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394946039502521169860357 636552382406722719348817)
                    ·
                      refine ⟨477414286805042039511613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636552382406722719348817 477414286805042039511613)
                      ·
                        rfl

theorem cell23_929761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_929761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929761 prefixEnd_929761 := by exact prefixLift 929761
  have htrace : WordTrace (prefixWord ++ tailWord_929761) baseStart_929761 baseEnd_929761 := by
    simpa [prefixWord, tailWord_929761, baseEnd_929761] using wordTrace_append hprefix tailTrace_929761
  have hstable : (prefixWord ++ tailWord_929761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929761).length < 2 ^ (prefixWord ++ tailWord_929761).sum := by decide
  have hdescent : baseEnd_929761 < baseStart_929761 := by decide
  rcases family_descends (prefixWord ++ tailWord_929761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929764 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_929764 : Nat := 118140960795 + 929764 * 2 ^ 59
def prefixEnd_929764 : Nat := 4983230072969 + 3 ^ 40 * 929764 * 2
def baseEnd_929764 : Nat := 477415827247005527774099

theorem tailTrace_929764 : CollatzResearch.WordTrace tailWord_929764 prefixEnd_929764 477415827247005527774099 := by
  unfold tailWord_929764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16955639501815646947154173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22607519335754195929538897 16955639501815646947154173)
  ·
    refine ⟨6358364813180867605182815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16955639501815646947154173 6358364813180867605182815)
    ·
      refine ⟨9537547219771301407774223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358364813180867605182815 9537547219771301407774223)
      ·
        refine ⟨14306320829656952111661335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9537547219771301407774223 14306320829656952111661335)
        ·
          refine ⟨21459481244485428167492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14306320829656952111661335 21459481244485428167492003)
          ·
            refine ⟨32189221866728142251238005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21459481244485428167492003 32189221866728142251238005)
            ·
              refine ⟨3017739550005763336053563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32189221866728142251238005 3017739550005763336053563)
              ·
                refine ⟨4526609325008645004080345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017739550005763336053563 4526609325008645004080345)
                ·
                  refine ⟨3394956993756483753060259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526609325008645004080345 3394956993756483753060259)
                  ·
                    refine ⟨5092435490634725629590389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394956993756483753060259 5092435490634725629590389)
                    ·
                      refine ⟨477415827247005527774099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5092435490634725629590389 477415827247005527774099)
                      ·
                        rfl

theorem cell23_929764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_929764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929764 prefixEnd_929764 := by exact prefixLift 929764
  have htrace : WordTrace (prefixWord ++ tailWord_929764) baseStart_929764 baseEnd_929764 := by
    simpa [prefixWord, tailWord_929764, baseEnd_929764] using wordTrace_append hprefix tailTrace_929764
  have hstable : (prefixWord ++ tailWord_929764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929764).length < 2 ^ (prefixWord ++ tailWord_929764).sum := by decide
  have hdescent : baseEnd_929764 < baseStart_929764 := by decide
  rcases family_descends (prefixWord ++ tailWord_929764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929784 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 7]
def baseStart_929784 : Nat := 118140960795 + 929784 * 2 ^ 59
def prefixEnd_929784 : Nat := 4983230072969 + 3 ^ 40 * 929784 * 2
def baseEnd_929784 : Nat := 53047344095566161058223

theorem tailTrace_929784 : CollatzResearch.WordTrace tailWord_929784 prefixEnd_929784 53047344095566161058223 := by
  unfold tailWord_929784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956004231779418655018203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22608005642372558206690937 16956004231779418655018203)
  ·
    refine ⟨25434006347669127982527305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16956004231779418655018203 25434006347669127982527305)
    ·
      refine ⟨19075504760751845986895479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25434006347669127982527305 19075504760751845986895479)
      ·
        refine ⟨28613257141127768980343219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19075504760751845986895479 28613257141127768980343219)
        ·
          refine ⟨42919885711691653470514829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28613257141127768980343219 42919885711691653470514829)
          ·
            refine ⟨16094957141884370051443061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42919885711691653470514829 16094957141884370051443061)
            ·
              refine ⟨1508902232051659692322787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16094957141884370051443061 1508902232051659692322787)
              ·
                refine ⟨2263353348077489538484181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508902232051659692322787 2263353348077489538484181)
                ·
                  refine ⟨53047344095566161058223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2263353348077489538484181 53047344095566161058223)
                  ·
                    rfl

theorem cell23_929784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_929784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929784 prefixEnd_929784 := by exact prefixLift 929784
  have htrace : WordTrace (prefixWord ++ tailWord_929784) baseStart_929784 baseEnd_929784 := by
    simpa [prefixWord, tailWord_929784, baseEnd_929784] using wordTrace_append hprefix tailTrace_929784
  have hstable : (prefixWord ++ tailWord_929784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929784).length < 2 ^ (prefixWord ++ tailWord_929784).sum := by decide
  have hdescent : baseEnd_929784 < baseStart_929784 := by decide
  rcases family_descends (prefixWord ++ tailWord_929784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929812 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_929812 : Nat := 118140960795 + 929812 * 2 ^ 59
def prefixEnd_929812 : Nat := 4983230072969 + 3 ^ 40 * 929812 * 2
def baseEnd_929812 : Nat := 477440474318421339973879

theorem tailTrace_929812 : CollatzResearch.WordTrace tailWord_929812 prefixEnd_929812 477440474318421339973879 := by
  unfold tailWord_929812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956514853728699046027845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22608686471638265394703793 16956514853728699046027845)
  ·
    refine ⟨3179346535074131071130221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16956514853728699046027845 3179346535074131071130221)
    ·
      refine ⟨1192254950652799151673833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3179346535074131071130221 1192254950652799151673833)
      ·
        refine ⟨894191212989599363755375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192254950652799151673833 894191212989599363755375)
        ·
          refine ⟨1341286819484399045633063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894191212989599363755375 1341286819484399045633063)
          ·
            refine ⟨2011930229226598568449595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341286819484399045633063 2011930229226598568449595)
            ·
              refine ⟨3017895343839897852674393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011930229226598568449595 3017895343839897852674393)
              ·
                refine ⟨2263421507879923389505795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017895343839897852674393 2263421507879923389505795)
                ·
                  refine ⟨3395132261819885084258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263421507879923389505795 3395132261819885084258693)
                  ·
                    refine ⟨636587299091228453298505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395132261819885084258693 636587299091228453298505)
                    ·
                      refine ⟨477440474318421339973879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636587299091228453298505 477440474318421339973879)
                      ·
                        rfl

theorem cell23_929812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_929812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929812 prefixEnd_929812 := by exact prefixLift 929812
  have htrace : WordTrace (prefixWord ++ tailWord_929812) baseStart_929812 baseEnd_929812 := by
    simpa [prefixWord, tailWord_929812, baseEnd_929812] using wordTrace_append hprefix tailTrace_929812
  have hstable : (prefixWord ++ tailWord_929812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929812).length < 2 ^ (prefixWord ++ tailWord_929812).sum := by decide
  have hdescent : baseEnd_929812 < baseStart_929812 := by decide
  rcases family_descends (prefixWord ++ tailWord_929812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929838 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_929838 : Nat := 118140960795 + 929838 * 2 ^ 59
def prefixEnd_929838 : Nat := 4983230072969 + 3 ^ 40 * 929838 * 2
def baseEnd_929838 : Nat := 477453824815438238248759

theorem tailTrace_929838 : CollatzResearch.WordTrace tailWord_929838 prefixEnd_929838 477453824815438238248759 := by
  unfold tailWord_929838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239247250670400566562771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22609318670242136355001445 4239247250670400566562771)
  ·
    refine ⟨6358870876005600849844157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239247250670400566562771 6358870876005600849844157)
    ·
      refine ⟨2384576578502100318691559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6358870876005600849844157 2384576578502100318691559)
      ·
        refine ⟨3576864867753150478037339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384576578502100318691559 3576864867753150478037339)
        ·
          refine ⟨5365297301629725717056009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576864867753150478037339 5365297301629725717056009)
          ·
            refine ⟨4023972976222294287792007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5365297301629725717056009 4023972976222294287792007)
            ·
              refine ⟨6035959464333441431688011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023972976222294287792007 6035959464333441431688011)
              ·
                refine ⟨9053939196500162147532017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035959464333441431688011 9053939196500162147532017)
                ·
                  refine ⟨6790454397375121610649013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053939196500162147532017 6790454397375121610649013)
                  ·
                    refine ⟨636605099753917650998345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6790454397375121610649013 636605099753917650998345)
                    ·
                      refine ⟨477453824815438238248759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636605099753917650998345 477453824815438238248759)
                      ·
                        rfl

theorem cell23_929838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_929838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929838 prefixEnd_929838 := by exact prefixLift 929838
  have htrace : WordTrace (prefixWord ++ tailWord_929838) baseStart_929838 baseEnd_929838 := by
    simpa [prefixWord, tailWord_929838, baseEnd_929838] using wordTrace_append hprefix tailTrace_929838
  have hstable : (prefixWord ++ tailWord_929838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929838).length < 2 ^ (prefixWord ++ tailWord_929838).sum := by decide
  have hdescent : baseEnd_929838 < baseStart_929838 := by decide
  rcases family_descends (prefixWord ++ tailWord_929838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929851 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 4, 2]
def baseStart_929851 : Nat := 118140960795 + 929851 * 2 ^ 59
def prefixEnd_929851 : Nat := 4983230072969 + 3 ^ 40 * 929851 * 2
def baseEnd_929851 : Nat := 477460500063946687386199

theorem tailTrace_929851 : CollatzResearch.WordTrace tailWord_929851 prefixEnd_929851 477460500063946687386199 := by
  unfold tailWord_929851
  simp only [CollatzResearch.WordTrace]
  refine ⟨33914452154316107752725407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22609634769544071835150271 33914452154316107752725407)
  ·
    refine ⟨50871678231474161629088111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33914452154316107752725407 50871678231474161629088111)
    ·
      refine ⟨76307517347211242443632167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50871678231474161629088111 76307517347211242443632167)
      ·
        refine ⟨114461276020816863665448251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76307517347211242443632167 114461276020816863665448251)
        ·
          refine ⟨171691914031225295498172377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114461276020816863665448251 171691914031225295498172377)
          ·
            refine ⟨128768935523418971623629283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171691914031225295498172377 128768935523418971623629283)
            ·
              refine ⟨193153403285128457435443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128768935523418971623629283 193153403285128457435443925)
              ·
                refine ⟨4527032889495198221143217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193153403285128457435443925 4527032889495198221143217)
                ·
                  refine ⟨3395274667121398665857413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527032889495198221143217 3395274667121398665857413)
                  ·
                    refine ⟨636614000085262249848265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395274667121398665857413 636614000085262249848265)
                    ·
                      refine ⟨477460500063946687386199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636614000085262249848265 477460500063946687386199)
                      ·
                        rfl

theorem cell23_929851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4, 2].length) (baseStart_929851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929851 prefixEnd_929851 := by exact prefixLift 929851
  have htrace : WordTrace (prefixWord ++ tailWord_929851) baseStart_929851 baseEnd_929851 := by
    simpa [prefixWord, tailWord_929851, baseEnd_929851] using wordTrace_append hprefix tailTrace_929851
  have hstable : (prefixWord ++ tailWord_929851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929851).length < 2 ^ (prefixWord ++ tailWord_929851).sum := by decide
  have hdescent : baseEnd_929851 < baseStart_929851 := by decide
  rcases family_descends (prefixWord ++ tailWord_929851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929864 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_929864 : Nat := 118140960795 + 929864 * 2 ^ 59
def prefixEnd_929864 : Nat := 4983230072969 + 3 ^ 40 * 929864 * 2
def baseEnd_929864 : Nat := 477467175312455136523639

theorem tailTrace_929864 : CollatzResearch.WordTrace tailWord_929864 prefixEnd_929864 477467175312455136523639 := by
  unfold tailWord_929864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16957463151634505486474323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22609950868846007315299097 16957463151634505486474323)
  ·
    refine ⟨25436194727451758229711485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16957463151634505486474323 25436194727451758229711485)
    ·
      refine ⟨9538573022794409336141807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25436194727451758229711485 9538573022794409336141807)
      ·
        refine ⟨14307859534191614004212711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538573022794409336141807 14307859534191614004212711)
        ·
          refine ⟨21461789301287421006319067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307859534191614004212711 21461789301287421006319067)
          ·
            refine ⟨32192683951931131509478601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21461789301287421006319067 32192683951931131509478601)
            ·
              refine ⟨24144512963948348632108951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32192683951931131509478601 24144512963948348632108951)
              ·
                refine ⟨36216769445922522948163427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24144512963948348632108951 36216769445922522948163427)
                ·
                  refine ⟨54325154168883784422245141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36216769445922522948163427 54325154168883784422245141)
                  ·
                    refine ⟨2546491601666427394792741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54325154168883784422245141 2546491601666427394792741)
                    ·
                      refine ⟨477467175312455136523639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2546491601666427394792741 477467175312455136523639)
                      ·
                        rfl

theorem cell23_929864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_929864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929864 prefixEnd_929864 := by exact prefixLift 929864
  have htrace : WordTrace (prefixWord ++ tailWord_929864) baseStart_929864 baseEnd_929864 := by
    simpa [prefixWord, tailWord_929864, baseEnd_929864] using wordTrace_append hprefix tailTrace_929864
  have hstable : (prefixWord ++ tailWord_929864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929864).length < 2 ^ (prefixWord ++ tailWord_929864).sum := by decide
  have hdescent : baseEnd_929864 < baseStart_929864 := by decide
  rcases family_descends (prefixWord ++ tailWord_929864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929885 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_929885 : Nat := 118140960795 + 929885 * 2 ^ 59
def prefixEnd_929885 : Nat := 4983230072969 + 3 ^ 40 * 929885 * 2
def baseEnd_929885 : Nat := 477477958406199554361043

theorem tailTrace_929885 : CollatzResearch.WordTrace tailWord_929885 prefixEnd_929885 477477958406199554361043 := by
  unfold tailWord_929885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915692236192931559463109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22610461490795287706308739 33915692236192931559463109)
  ·
    refine ⟨6359192294286174667399333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33915692236192931559463109 6359192294286174667399333)
    ·
      refine ⟨1192348555178657750137375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6359192294286174667399333 1192348555178657750137375)
      ·
        refine ⟨1788522832767986625206063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192348555178657750137375 1788522832767986625206063)
        ·
          refine ⟨2682784249151979937809095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788522832767986625206063 2682784249151979937809095)
          ·
            refine ⟨4024176373727969906713643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682784249151979937809095 4024176373727969906713643)
            ·
              refine ⟨6036264560591954860070465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024176373727969906713643 6036264560591954860070465)
              ·
                refine ⟨4527198420443966145052849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036264560591954860070465 4527198420443966145052849)
                ·
                  refine ⟨3395398815332974608789637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527198420443966145052849 3395398815332974608789637)
                  ·
                    refine ⟨636637277874932739148057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395398815332974608789637 636637277874932739148057)
                    ·
                      refine ⟨477477958406199554361043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636637277874932739148057 477477958406199554361043)
                      ·
                        rfl

theorem cell23_929885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_929885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929885 prefixEnd_929885 := by exact prefixLift 929885
  have htrace : WordTrace (prefixWord ++ tailWord_929885) baseStart_929885 baseEnd_929885 := by
    simpa [prefixWord, tailWord_929885, baseEnd_929885] using wordTrace_append hprefix tailTrace_929885
  have hstable : (prefixWord ++ tailWord_929885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929885).length < 2 ^ (prefixWord ++ tailWord_929885).sum := by decide
  have hdescent : baseEnd_929885 < baseStart_929885 := by decide
  rcases family_descends (prefixWord ++ tailWord_929885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929891 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 6]
def baseStart_929891 : Nat := 118140960795 + 929891 * 2 ^ 59
def prefixEnd_929891 : Nat := 4983230072969 + 3 ^ 40 * 929891 * 2
def baseEnd_929891 : Nat := 53053448810014058987335

theorem tailTrace_929891 : CollatzResearch.WordTrace tailWord_929891 prefixEnd_929891 53053448810014058987335 := by
  unfold tailWord_929891
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915911074171194584181527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22610607382780796389454351 33915911074171194584181527)
  ·
    refine ⟨50873866611256791876272291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33915911074171194584181527 50873866611256791876272291)
    ·
      refine ⟨76310799916885187814408437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50873866611256791876272291 76310799916885187814408437)
      ·
        refine ⟨7154137492207986357600791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76310799916885187814408437 7154137492207986357600791)
        ·
          refine ⟨10731206238311979536401187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154137492207986357600791 10731206238311979536401187)
          ·
            refine ⟨16096809357467969304601781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731206238311979536401187 16096809357467969304601781)
            ·
              refine ⟨1509075877262622122306417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16096809357467969304601781 1509075877262622122306417)
              ·
                refine ⟨1131806907946966591729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509075877262622122306417 1131806907946966591729813)
                ·
                  refine ⟨53053448810014058987335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1131806907946966591729813 53053448810014058987335)
                  ·
                    rfl

theorem cell23_929891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 6].length) (baseStart_929891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929891 prefixEnd_929891 := by exact prefixLift 929891
  have htrace : WordTrace (prefixWord ++ tailWord_929891) baseStart_929891 baseEnd_929891 := by
    simpa [prefixWord, tailWord_929891, baseEnd_929891] using wordTrace_append hprefix tailTrace_929891
  have hstable : (prefixWord ++ tailWord_929891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929891).length < 2 ^ (prefixWord ++ tailWord_929891).sum := by decide
  have hdescent : baseEnd_929891 < baseStart_929891 := by decide
  rcases family_descends (prefixWord ++ tailWord_929891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929938 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_929938 : Nat := 118140960795 + 929938 * 2 ^ 59
def prefixEnd_929938 : Nat := 4983230072969 + 3 ^ 40 * 929938 * 2
def baseEnd_929938 : Nat := 159168390960295948999433

theorem tailTrace_929938 : CollatzResearch.WordTrace tailWord_929938 prefixEnd_929938 159168390960295948999433 := by
  unfold tailWord_929938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479406326250230402785617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22611750203333947740761645 8479406326250230402785617)
  ·
    refine ⟨6359554744687672802089213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8479406326250230402785617 6359554744687672802089213)
    ·
      refine ⟨2384833029257877300783455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6359554744687672802089213 2384833029257877300783455)
      ·
        refine ⟨3577249543886815951175183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384833029257877300783455 3577249543886815951175183)
        ·
          refine ⟨5365874315830223926762775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577249543886815951175183 5365874315830223926762775)
          ·
            refine ⟨8048811473745335890144163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365874315830223926762775 8048811473745335890144163)
            ·
              refine ⟨12073217210618003835216245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048811473745335890144163 12073217210618003835216245)
              ·
                refine ⟨1131864113495437859551523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12073217210618003835216245 1131864113495437859551523)
                ·
                  refine ⟨1697796170243156789327285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131864113495437859551523 1697796170243156789327285)
                  ·
                    refine ⟨159168390960295948999433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1697796170243156789327285 159168390960295948999433)
                    ·
                      rfl

theorem cell23_929938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_929938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929938 prefixEnd_929938 := by exact prefixLift 929938
  have htrace : WordTrace (prefixWord ++ tailWord_929938) baseStart_929938 baseEnd_929938 := by
    simpa [prefixWord, tailWord_929938, baseEnd_929938] using wordTrace_append hprefix tailTrace_929938
  have hstable : (prefixWord ++ tailWord_929938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929938).length < 2 ^ (prefixWord ++ tailWord_929938).sum := by decide
  have hdescent : baseEnd_929938 < baseStart_929938 := by decide
  rcases family_descends (prefixWord ++ tailWord_929938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929971 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_929971 : Nat := 118140960795 + 929971 * 2 ^ 59
def prefixEnd_929971 : Nat := 4983230072969 + 3 ^ 40 * 929971 * 2
def baseEnd_929971 : Nat := 477522117742486217885647

theorem tailTrace_929971 : CollatzResearch.WordTrace tailWord_929971 prefixEnd_929971 477522117742486217885647 := by
  unfold tailWord_929971
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918828913881368247093767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22612552609254245498062511 33918828913881368247093767)
  ·
    refine ⟨50878243370822052370640651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33918828913881368247093767 50878243370822052370640651)
    ·
      refine ⟨76317365056233078555960977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50878243370822052370640651 76317365056233078555960977)
      ·
        refine ⟨57238023792174808916970733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76317365056233078555960977 57238023792174808916970733)
        ·
          refine ⟨21464258922065553343864025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57238023792174808916970733 21464258922065553343864025)
          ·
            refine ⟨16098194191549165007898019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21464258922065553343864025 16098194191549165007898019)
            ·
              refine ⟨24147291287323747511847029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16098194191549165007898019 24147291287323747511847029)
              ·
                refine ⟨2263808558186601329235659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24147291287323747511847029 2263808558186601329235659)
                ·
                  refine ⟨3395712837279901993853489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263808558186601329235659 3395712837279901993853489)
                  ·
                    refine ⟨2546784627959926495390117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395712837279901993853489 2546784627959926495390117)
                    ·
                      refine ⟨477522117742486217885647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2546784627959926495390117 477522117742486217885647)
                      ·
                        rfl

theorem cell23_929971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_929971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929971 prefixEnd_929971 := by exact prefixLift 929971
  have htrace : WordTrace (prefixWord ++ tailWord_929971) baseStart_929971 baseEnd_929971 := by
    simpa [prefixWord, tailWord_929971, baseEnd_929971] using wordTrace_append hprefix tailTrace_929971
  have hstable : (prefixWord ++ tailWord_929971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929971).length < 2 ^ (prefixWord ++ tailWord_929971).sum := by decide
  have hdescent : baseEnd_929971 < baseStart_929971 := by decide
  rcases family_descends (prefixWord ++ tailWord_929971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929975 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_929975 : Nat := 118140960795 + 929975 * 2 ^ 59
def prefixEnd_929975 : Nat := 4983230072969 + 3 ^ 40 * 929975 * 2
def baseEnd_929975 : Nat := 477524171665104202235629

theorem tailTrace_929975 : CollatzResearch.WordTrace tailWord_929975 prefixEnd_929975 477524171665104202235629 := by
  unfold tailWord_929975
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918974805866876930239379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22612649870577917953492919 33918974805866876930239379)
  ·
    refine ⟨50878462208800315395359069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33918974805866876930239379 50878462208800315395359069)
    ·
      refine ⟨19079423328300118273259651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50878462208800315395359069 19079423328300118273259651)
      ·
        refine ⟨28619134992450177409889477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079423328300118273259651 28619134992450177409889477)
        ·
          refine ⟨5366087811084408264354277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28619134992450177409889477 5366087811084408264354277)
          ·
            refine ⟨1006141464578326549566427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5366087811084408264354277 1006141464578326549566427)
            ·
              refine ⟨1509212196867489824349641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006141464578326549566427 1509212196867489824349641)
              ·
                refine ⟨1131909147650617368262231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509212196867489824349641 1131909147650617368262231)
                ·
                  refine ⟨1697863721475926052393347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131909147650617368262231 1697863721475926052393347)
                  ·
                    refine ⟨2546795582213889078590021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1697863721475926052393347 2546795582213889078590021)
                    ·
                      refine ⟨477524171665104202235629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2546795582213889078590021 477524171665104202235629)
                      ·
                        rfl

theorem cell23_929975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_929975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929975 prefixEnd_929975 := by exact prefixLift 929975
  have htrace : WordTrace (prefixWord ++ tailWord_929975) baseStart_929975 baseEnd_929975 := by
    simpa [prefixWord, tailWord_929975, baseEnd_929975] using wordTrace_append hprefix tailTrace_929975
  have hstable : (prefixWord ++ tailWord_929975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929975).length < 2 ^ (prefixWord ++ tailWord_929975).sum := by decide
  have hdescent : baseEnd_929975 < baseStart_929975 := by decide
  rcases family_descends (prefixWord ++ tailWord_929975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929985 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_929985 : Nat := 118140960795 + 929985 * 2 ^ 59
def prefixEnd_929985 : Nat := 4983230072969 + 3 ^ 40 * 929985 * 2
def baseEnd_929985 : Nat := 159176435490549721036861

theorem tailTrace_929985 : CollatzResearch.WordTrace tailWord_929985 prefixEnd_929985 159176435490549721036861 := by
  unfold tailWord_929985
  simp only [CollatzResearch.WordTrace]
  refine ⟨33919339535830648638103409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22612893023887099092068939 33919339535830648638103409)
  ·
    refine ⟨25439504651872986478577557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33919339535830648638103409 25439504651872986478577557)
    ·
      refine ⟨1192476780556546241183323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25439504651872986478577557 1192476780556546241183323)
      ·
        refine ⟨1788715170834819361774985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192476780556546241183323 1788715170834819361774985)
        ·
          refine ⟨1341536378126114521331239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788715170834819361774985 1341536378126114521331239)
          ·
            refine ⟨2012304567189171781996859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341536378126114521331239 2012304567189171781996859)
            ·
              refine ⟨3018456850783757672995289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012304567189171781996859 3018456850783757672995289)
              ·
                refine ⟨2263842638087818254746467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018456850783757672995289 2263842638087818254746467)
                ·
                  refine ⟨3395763957131727382119701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263842638087818254746467 3395763957131727382119701)
                  ·
                    refine ⟨159176435490549721036861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3395763957131727382119701 159176435490549721036861)
                    ·
                      rfl

theorem cell23_929985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_929985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929985 prefixEnd_929985 := by exact prefixLift 929985
  have htrace : WordTrace (prefixWord ++ tailWord_929985) baseStart_929985 baseEnd_929985 := by
    simpa [prefixWord, tailWord_929985, baseEnd_929985] using wordTrace_append hprefix tailTrace_929985
  have hstable : (prefixWord ++ tailWord_929985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929985).length < 2 ^ (prefixWord ++ tailWord_929985).sum := by decide
  have hdescent : baseEnd_929985 < baseStart_929985 := by decide
  rcases family_descends (prefixWord ++ tailWord_929985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929988 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_929988 : Nat := 118140960795 + 929988 * 2 ^ 59
def prefixEnd_929988 : Nat := 4983230072969 + 3 ^ 40 * 929988 * 2
def baseEnd_929988 : Nat := 477530846913612651373069

theorem tailTrace_929988 : CollatzResearch.WordTrace tailWord_929988 prefixEnd_929988 477530846913612651373069 := by
  unfold tailWord_929988
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959724477409890075231309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22612965969879853433641745 16959724477409890075231309)
  ·
    refine ⟨6359896679028708778211741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16959724477409890075231309 6359896679028708778211741)
    ·
      refine ⟨2384961254635765791829403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6359896679028708778211741 2384961254635765791829403)
      ·
        refine ⟨3577441881953648687744105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384961254635765791829403 3577441881953648687744105)
        ·
          refine ⟨2683081411465236515808079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577441881953648687744105 2683081411465236515808079)
          ·
            refine ⟨4024622117197854773712119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683081411465236515808079 4024622117197854773712119)
            ·
              refine ⟨6036933175796782160568179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024622117197854773712119 6036933175796782160568179)
              ·
                refine ⟨9055399763695173240852269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036933175796782160568179 9055399763695173240852269)
                ·
                  refine ⟨3395774911385689965319601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9055399763695173240852269 3395774911385689965319601)
                  ·
                    refine ⟨2546831183539267473989701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395774911385689965319601 2546831183539267473989701)
                    ·
                      refine ⟨477530846913612651373069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2546831183539267473989701 477530846913612651373069)
                      ·
                        rfl

theorem cell23_929988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_929988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929988 prefixEnd_929988 := by exact prefixLift 929988
  have htrace : WordTrace (prefixWord ++ tailWord_929988) baseStart_929988 baseEnd_929988 := by
    simpa [prefixWord, tailWord_929988, baseEnd_929988] using wordTrace_append hprefix tailTrace_929988
  have hstable : (prefixWord ++ tailWord_929988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929988).length < 2 ^ (prefixWord ++ tailWord_929988).sum := by decide
  have hdescent : baseEnd_929988 < baseStart_929988 := by decide
  rcases family_descends (prefixWord ++ tailWord_929988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929992 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_929992 : Nat := 118140960795 + 929992 * 2 ^ 59
def prefixEnd_929992 : Nat := 4983230072969 + 3 ^ 40 * 929992 * 2
def baseEnd_929992 : Nat := 477532900836230635723051

theorem tailTrace_929992 : CollatzResearch.WordTrace tailWord_929992 prefixEnd_929992 477532900836230635723051 := by
  unfold tailWord_929992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959797423402644416804115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22613063231203525889072153 16959797423402644416804115)
  ·
    refine ⟨25439696135103966625206173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16959797423402644416804115 25439696135103966625206173)
    ·
      refine ⟨9539886050663987484452315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25439696135103966625206173 9539886050663987484452315)
      ·
        refine ⟨14309829075995981226678473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9539886050663987484452315 14309829075995981226678473)
        ·
          refine ⟨10732371806996985920008855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14309829075995981226678473 10732371806996985920008855)
          ·
            refine ⟨16098557710495478880013283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732371806996985920008855 16098557710495478880013283)
            ·
              refine ⟨24147836565743218320019925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16098557710495478880013283 24147836565743218320019925)
              ·
                refine ⟨565964919509606679375467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24147836565743218320019925 565964919509606679375467)
                ·
                  refine ⟨848947379264410019063201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565964919509606679375467 848947379264410019063201)
                  ·
                    refine ⟨636710534448307514297401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848947379264410019063201 636710534448307514297401)
                    ·
                      refine ⟨477532900836230635723051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636710534448307514297401 477532900836230635723051)
                      ·
                        rfl

theorem cell23_929992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_929992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929992 prefixEnd_929992 := by exact prefixLift 929992
  have htrace : WordTrace (prefixWord ++ tailWord_929992) baseStart_929992 baseEnd_929992 := by
    simpa [prefixWord, tailWord_929992, baseEnd_929992] using wordTrace_append hprefix tailTrace_929992
  have hstable : (prefixWord ++ tailWord_929992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929992).length < 2 ^ (prefixWord ++ tailWord_929992).sum := by decide
  have hdescent : baseEnd_929992 < baseStart_929992 := by decide
  rcases family_descends (prefixWord ++ tailWord_929992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929995 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 1, 2, 3]
def baseStart_929995 : Nat := 118140960795 + 929995 * 2 ^ 59
def prefixEnd_929995 : Nat := 4983230072969 + 3 ^ 40 * 929995 * 2
def baseEnd_929995 : Nat := 477534441278194123985537

theorem tailTrace_929995 : CollatzResearch.WordTrace tailWord_929995 prefixEnd_929995 477534441278194123985537 := by
  unfold tailWord_929995
  simp only [CollatzResearch.WordTrace]
  refine ⟨33919704265794420345967439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613136177196280230644959 33919704265794420345967439)
  ·
    refine ⟨50879556398691630518951159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33919704265794420345967439 50879556398691630518951159)
    ·
      refine ⟨76319334598037445778426739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50879556398691630518951159 76319334598037445778426739)
      ·
        refine ⟨114479001897056168667640109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76319334598037445778426739 114479001897056168667640109)
        ·
          refine ⟨42929625711396063250365041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114479001897056168667640109 42929625711396063250365041)
          ·
            refine ⟨32197219283547047437773781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42929625711396063250365041 32197219283547047437773781)
            ·
              refine ⟨754622326958133924322823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32197219283547047437773781 754622326958133924322823)
              ·
                refine ⟨1131933490437200886484235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754622326958133924322823 1131933490437200886484235)
                ·
                  refine ⟨1697900235655801329726353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131933490437200886484235 1697900235655801329726353)
                  ·
                    refine ⟨1273425176741850997294765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1697900235655801329726353 1273425176741850997294765)
                    ·
                      refine ⟨477534441278194123985537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1273425176741850997294765 477534441278194123985537)
                      ·
                        rfl

theorem cell23_929995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 2, 3].length) (baseStart_929995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_929995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_929995 prefixEnd_929995 := by exact prefixLift 929995
  have htrace : WordTrace (prefixWord ++ tailWord_929995) baseStart_929995 baseEnd_929995 := by
    simpa [prefixWord, tailWord_929995, baseEnd_929995] using wordTrace_append hprefix tailTrace_929995
  have hstable : (prefixWord ++ tailWord_929995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929995).length < 2 ^ (prefixWord ++ tailWord_929995).sum := by decide
  have hdescent : baseEnd_929995 < baseStart_929995 := by decide
  rcases family_descends (prefixWord ++ tailWord_929995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930009 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 1, 2, 2]
def baseStart_930009 : Nat := 118140960795 + 930009 * 2 ^ 59
def prefixEnd_930009 : Nat := 4983230072969 + 3 ^ 40 * 930009 * 2
def baseEnd_930009 : Nat := 477541630007357069210473

theorem tailTrace_930009 : CollatzResearch.WordTrace tailWord_930009 prefixEnd_930009 477541630007357069210473 := by
  unfold tailWord_930009
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920214887743700736977081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613476591829133824651387 33920214887743700736977081)
  ·
    refine ⟨25440161165807775552732811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33920214887743700736977081 25440161165807775552732811)
    ·
      refine ⟨38160241748711663329099217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25440161165807775552732811 38160241748711663329099217)
      ·
        refine ⟨28620181311533747496824413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38160241748711663329099217 28620181311533747496824413)
        ·
          refine ⟨10732567991825155311309155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28620181311533747496824413 10732567991825155311309155)
          ·
            refine ⟨16098851987737732966963733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732567991825155311309155 16098851987737732966963733)
            ·
              refine ⟨754633686925206232826425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16098851987737732966963733 754633686925206232826425)
              ·
                refine ⟨565975265193904674619819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754633686925206232826425 565975265193904674619819)
                ·
                  refine ⟨848962897790857011929729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565975265193904674619819 848962897790857011929729)
                  ·
                    refine ⟨636722173343142758947297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848962897790857011929729 636722173343142758947297)
                    ·
                      refine ⟨477541630007357069210473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636722173343142758947297 477541630007357069210473)
                      ·
                        rfl

theorem cell23_930009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_930009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930009 prefixEnd_930009 := by exact prefixLift 930009
  have htrace : WordTrace (prefixWord ++ tailWord_930009) baseStart_930009 baseEnd_930009 := by
    simpa [prefixWord, tailWord_930009, baseEnd_930009] using wordTrace_append hprefix tailTrace_930009
  have hstable : (prefixWord ++ tailWord_930009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930009).length < 2 ^ (prefixWord ++ tailWord_930009).sum := by decide
  have hdescent : baseEnd_930009 < baseStart_930009 := by decide
  rcases family_descends (prefixWord ++ tailWord_930009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930035 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 1, 3, 2]
def baseStart_930035 : Nat := 118140960795 + 930035 * 2 ^ 59
def prefixEnd_930035 : Nat := 4983230072969 + 3 ^ 40 * 930035 * 2
def baseEnd_930035 : Nat := 477554980504373967485353

theorem tailTrace_930035 : CollatzResearch.WordTrace tailWord_930035 prefixEnd_930035 477554980504373967485353 := by
  unfold tailWord_930035
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921163185649507177423559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614108790433004784949039 33921163185649507177423559)
  ·
    refine ⟨50881744778474260766135339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33921163185649507177423559 50881744778474260766135339)
    ·
      refine ⟨76322617167711391149203009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50881744778474260766135339 76322617167711391149203009)
      ·
        refine ⟨57241962875783543361902257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76322617167711391149203009 57241962875783543361902257)
        ·
          refine ⟨42931472156837657521426693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57241962875783543361902257 42931472156837657521426693)
          ·
            refine ⟨8049651029407060785267505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42931472156837657521426693 8049651029407060785267505)
            ·
              refine ⟨6037238272055295588950629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049651029407060785267505 6037238272055295588950629)
              ·
                refine ⟨1131982176010367922928243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6037238272055295588950629 1131982176010367922928243)
                ·
                  refine ⟨1697973264015551884392365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131982176010367922928243 1697973264015551884392365)
                  ·
                    refine ⟨636739974005831956647137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697973264015551884392365 636739974005831956647137)
                    ·
                      refine ⟨477554980504373967485353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636739974005831956647137 477554980504373967485353)
                      ·
                        rfl

theorem cell23_930035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3, 2].length) (baseStart_930035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930035 prefixEnd_930035 := by exact prefixLift 930035
  have htrace : WordTrace (prefixWord ++ tailWord_930035) baseStart_930035 baseEnd_930035 := by
    simpa [prefixWord, tailWord_930035, baseEnd_930035] using wordTrace_append hprefix tailTrace_930035
  have hstable : (prefixWord ++ tailWord_930035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930035).length < 2 ^ (prefixWord ++ tailWord_930035).sum := by decide
  have hdescent : baseEnd_930035 < baseStart_930035 := by decide
  rcases family_descends (prefixWord ++ tailWord_930035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930051 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_930051 : Nat := 118140960795 + 930051 * 2 ^ 59
def prefixEnd_930051 : Nat := 4983230072969 + 3 ^ 40 * 930051 * 2
def baseEnd_930051 : Nat := 477563196194845904885279

theorem tailTrace_930051 : CollatzResearch.WordTrace tailWord_930051 prefixEnd_930051 477563196194845904885279 := by
  unfold tailWord_930051
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921746753591541910006007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614497835727694606670671 33921746753591541910006007)
  ·
    refine ⟨50882620130387312865009011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33921746753591541910006007 50882620130387312865009011)
    ·
      refine ⟨76323930195580969297513517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50882620130387312865009011 76323930195580969297513517)
      ·
        refine ⟨28621473823342863486567569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76323930195580969297513517 28621473823342863486567569)
        ·
          refine ⟨21466105367507147614925677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28621473823342863486567569 21466105367507147614925677)
          ·
            refine ⟨8049789512815180355597129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21466105367507147614925677 8049789512815180355597129)
            ·
              refine ⟨6037342134611385266697847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049789512815180355597129 6037342134611385266697847)
              ·
                refine ⟨9056013201917077900046771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037342134611385266697847 9056013201917077900046771)
                ·
                  refine ⟨13584019802875616850070157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056013201917077900046771 13584019802875616850070157)
                  ·
                    refine ⟨5094007426078356318776309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13584019802875616850070157 5094007426078356318776309)
                    ·
                      refine ⟨477563196194845904885279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5094007426078356318776309 477563196194845904885279)
                      ·
                        rfl

theorem cell23_930051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_930051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930051 prefixEnd_930051 := by exact prefixLift 930051
  have htrace : WordTrace (prefixWord ++ tailWord_930051) baseStart_930051 baseEnd_930051 := by
    simpa [prefixWord, tailWord_930051, baseEnd_930051] using wordTrace_append hprefix tailTrace_930051
  have hstable : (prefixWord ++ tailWord_930051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930051).length < 2 ^ (prefixWord ++ tailWord_930051).sum := by decide
  have hdescent : baseEnd_930051 < baseStart_930051 := by decide
  rcases family_descends (prefixWord ++ tailWord_930051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930082 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_930082 : Nat := 118140960795 + 930082 * 2 ^ 59
def prefixEnd_930082 : Nat := 4983230072969 + 3 ^ 40 * 930082 * 2
def baseEnd_930082 : Nat := 477579114095135283597637

theorem tailTrace_930082 : CollatzResearch.WordTrace tailWord_930082 prefixEnd_930082 477579114095135283597637 := by
  unfold tailWord_930082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480719354119808551096125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22615251610986156136256333 8480719354119808551096125)
  ·
    refine ⟨3180269757794928206661047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8480719354119808551096125 3180269757794928206661047)
    ·
      refine ⟨4770404636692392309991571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180269757794928206661047 4770404636692392309991571)
      ·
        refine ⟨7155606955038588464987357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770404636692392309991571 7155606955038588464987357)
        ·
          refine ⟨2683352608139470674370259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7155606955038588464987357 2683352608139470674370259)
          ·
            refine ⟨4025028912209206011555389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683352608139470674370259 4025028912209206011555389)
            ·
              refine ⟨1509385842078452254333271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025028912209206011555389 1509385842078452254333271)
              ·
                refine ⟨2264078763117678381499907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509385842078452254333271 2264078763117678381499907)
                ·
                  refine ⟨3396118144676517572249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264078763117678381499907 3396118144676517572249861)
                  ·
                    refine ⟨636772152126847044796849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396118144676517572249861 636772152126847044796849)
                    ·
                      refine ⟨477579114095135283597637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636772152126847044796849 477579114095135283597637)
                      ·
                        rfl

theorem cell23_930082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_930082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930082 prefixEnd_930082 := by exact prefixLift 930082
  have htrace : WordTrace (prefixWord ++ tailWord_930082) baseStart_930082 baseEnd_930082 := by
    simpa [prefixWord, tailWord_930082, baseEnd_930082] using wordTrace_append hprefix tailTrace_930082
  have hstable : (prefixWord ++ tailWord_930082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930082).length < 2 ^ (prefixWord ++ tailWord_930082).sum := by decide
  have hdescent : baseEnd_930082 < baseStart_930082 := by decide
  rcases family_descends (prefixWord ++ tailWord_930082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930128 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_930128 : Nat := 118140960795 + 930128 * 2 ^ 59
def prefixEnd_930128 : Nat := 4983230072969 + 3 ^ 40 * 930128 * 2
def baseEnd_930128 : Nat := 477602734205242103622425

theorem tailTrace_930128 : CollatzResearch.WordTrace tailWord_930128 prefixEnd_930128 477602734205242103622425 := by
  unfold tailWord_930128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962277587156292030279519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22616370116208389373706025 16962277587156292030279519)
  ·
    refine ⟨25443416380734438045419279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962277587156292030279519 25443416380734438045419279)
    ·
      refine ⟨38165124571101657068128919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25443416380734438045419279 38165124571101657068128919)
      ·
        refine ⟨57247686856652485602193379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38165124571101657068128919 57247686856652485602193379)
        ·
          refine ⟨85871530284978728403290069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57247686856652485602193379 85871530284978728403290069)
          ·
            refine ⟨2012613991054188946952111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85871530284978728403290069 2012613991054188946952111)
            ·
              refine ⟨3018920986581283420428167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012613991054188946952111 3018920986581283420428167)
              ·
                refine ⟨4528381479871925130642251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018920986581283420428167 4528381479871925130642251)
                ·
                  refine ⟨6792572219807887695963377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528381479871925130642251 6792572219807887695963377)
                  ·
                    refine ⟨5094429164855915771972533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792572219807887695963377 5094429164855915771972533)
                    ·
                      refine ⟨477602734205242103622425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5094429164855915771972533 477602734205242103622425)
                      ·
                        rfl

theorem cell23_930128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_930128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930128 prefixEnd_930128 := by exact prefixLift 930128
  have htrace : WordTrace (prefixWord ++ tailWord_930128) baseStart_930128 baseEnd_930128 := by
    simpa [prefixWord, tailWord_930128, baseEnd_930128] using wordTrace_append hprefix tailTrace_930128
  have hstable : (prefixWord ++ tailWord_930128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930128).length < 2 ^ (prefixWord ++ tailWord_930128).sum := by decide
  have hdescent : baseEnd_930128 < baseStart_930128 := by decide
  rcases family_descends (prefixWord ++ tailWord_930128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930131 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 8]
def baseStart_930131 : Nat := 118140960795 + 930131 * 2 ^ 59
def prefixEnd_930131 : Nat := 4983230072969 + 3 ^ 40 * 930131 * 2
def baseEnd_930131 : Nat := 159201424882401863961637

theorem tailTrace_930131 : CollatzResearch.WordTrace tailWord_930131 prefixEnd_930131 159201424882401863961637 := by
  unfold tailWord_930131
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924664593301715572918247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22616443062201143715278831 33924664593301715572918247)
  ·
    refine ⟨50886996889952573359377371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33924664593301715572918247 50886996889952573359377371)
    ·
      refine ⟨76330495334928860039066057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50886996889952573359377371 76330495334928860039066057)
      ·
        refine ⟨57247871501196645029299543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76330495334928860039066057 57247871501196645029299543)
        ·
          refine ⟨85871807251794967543949315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57247871501196645029299543 85871807251794967543949315)
          ·
            refine ⟨128807710877692451315923973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85871807251794967543949315 128807710877692451315923973)
            ·
              refine ⟨24151445789567334621735745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128807710877692451315923973 24151445789567334621735745)
              ·
                refine ⟨18113584342175500966301809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24151445789567334621735745 18113584342175500966301809)
                ·
                  refine ⟨13585188256631625724726357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18113584342175500966301809 13585188256631625724726357)
                  ·
                    refine ⟨159201424882401863961637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13585188256631625724726357 159201424882401863961637)
                    ·
                      rfl

theorem cell23_930131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_930131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930131 prefixEnd_930131 := by exact prefixLift 930131
  have htrace : WordTrace (prefixWord ++ tailWord_930131) baseStart_930131 baseEnd_930131 := by
    simpa [prefixWord, tailWord_930131, baseEnd_930131] using wordTrace_append hprefix tailTrace_930131
  have hstable : (prefixWord ++ tailWord_930131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930131).length < 2 ^ (prefixWord ++ tailWord_930131).sum := by decide
  have hdescent : baseEnd_930131 < baseStart_930131 := by decide
  rcases family_descends (prefixWord ++ tailWord_930131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930133 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_930133 : Nat := 118140960795 + 930133 * 2 ^ 59
def prefixEnd_930133 : Nat := 4983230072969 + 3 ^ 40 * 930133 * 2
def baseEnd_930133 : Nat := 477605301608514584059903

theorem tailTrace_930133 : CollatzResearch.WordTrace tailWord_930133 prefixEnd_930133 477605301608514584059903 := by
  unfold tailWord_930133
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924737539294469914491053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22616491692862979942994035 33924737539294469914491053)
  ·
    refine ⟨12721776577235426217934145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33924737539294469914491053 12721776577235426217934145)
    ·
      refine ⟨9541332432926569663450609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12721776577235426217934145 9541332432926569663450609)
      ·
        refine ⟨7155999324694927247587957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9541332432926569663450609 7155999324694927247587957)
        ·
          refine ⟨670874936690149429461371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7155999324694927247587957 670874936690149429461371)
          ·
            refine ⟨1006312405035224144192057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670874936690149429461371 1006312405035224144192057)
            ·
              refine ⟨754734303776418108144043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006312405035224144192057 754734303776418108144043)
              ·
                refine ⟨1132101455664627162216065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754734303776418108144043 1132101455664627162216065)
                ·
                  refine ⟨849076091748470371662049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132101455664627162216065 849076091748470371662049)
                  ·
                    refine ⟨636807068811352778746537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849076091748470371662049 636807068811352778746537)
                    ·
                      refine ⟨477605301608514584059903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636807068811352778746537 477605301608514584059903)
                      ·
                        rfl

theorem cell23_930133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_930133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930133 prefixEnd_930133 := by exact prefixLift 930133
  have htrace : WordTrace (prefixWord ++ tailWord_930133) baseStart_930133 baseEnd_930133 := by
    simpa [prefixWord, tailWord_930133, baseEnd_930133] using wordTrace_append hprefix tailTrace_930133
  have hstable : (prefixWord ++ tailWord_930133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930133).length < 2 ^ (prefixWord ++ tailWord_930133).sum := by decide
  have hdescent : baseEnd_930133 < baseStart_930133 := by decide
  rcases family_descends (prefixWord ++ tailWord_930133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930138 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_930138 : Nat := 118140960795 + 930138 * 2 ^ 59
def prefixEnd_930138 : Nat := 4983230072969 + 3 ^ 40 * 930138 * 2
def baseEnd_930138 : Nat := 477607869011787064497379

theorem tailTrace_930138 : CollatzResearch.WordTrace tailWord_930138 prefixEnd_930138 477607869011787064497379 := by
  unfold tailWord_930138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481229976069088942105767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22616613269517570512282045 8481229976069088942105767)
  ·
    refine ⟨12721844964103633413158651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481229976069088942105767 12721844964103633413158651)
    ·
      refine ⟨19082767446155450119737977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12721844964103633413158651 19082767446155450119737977)
      ·
        refine ⟨14312075584616587589803483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19082767446155450119737977 14312075584616587589803483)
        ·
          refine ⟨21468113376924881384705225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312075584616587589803483 21468113376924881384705225)
          ·
            refine ⟨16101085032693661038528919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468113376924881384705225 16101085032693661038528919)
            ·
              refine ⟨24151627549040491557793379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101085032693661038528919 24151627549040491557793379)
              ·
                refine ⟨36227441323560737336690069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24151627549040491557793379 36227441323560737336690069)
                ·
                  refine ⟨1698161312041909562657347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36227441323560737336690069 1698161312041909562657347)
                  ·
                    refine ⟨2547241968062864343986021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1698161312041909562657347 2547241968062864343986021)
                    ·
                      refine ⟨477607869011787064497379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2547241968062864343986021 477607869011787064497379)
                      ·
                        rfl

theorem cell23_930138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_930138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930138 prefixEnd_930138 := by exact prefixLift 930138
  have htrace : WordTrace (prefixWord ++ tailWord_930138) baseStart_930138 baseEnd_930138 := by
    simpa [prefixWord, tailWord_930138, baseEnd_930138] using wordTrace_append hprefix tailTrace_930138
  have hstable : (prefixWord ++ tailWord_930138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930138).length < 2 ^ (prefixWord ++ tailWord_930138).sum := by decide
  have hdescent : baseEnd_930138 < baseStart_930138 := by decide
  rcases family_descends (prefixWord ++ tailWord_930138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930216 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 1, 4]
def baseStart_930216 : Nat := 118140960795 + 930216 * 2 ^ 59
def prefixEnd_930216 : Nat := 4983230072969 + 3 ^ 40 * 930216 * 2
def baseEnd_930216 : Nat := 159215973500945919774007

theorem tailTrace_930216 : CollatzResearch.WordTrace tailWord_930216 prefixEnd_930216 159215973500945919774007 := by
  unfold tailWord_930216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963882398996887544881251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22618509865329183393175001 16963882398996887544881251)
  ·
    refine ⟨25445823598495331317321877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16963882398996887544881251 25445823598495331317321877)
    ·
      refine ⟨1192772981179468655499463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25445823598495331317321877 1192772981179468655499463)
      ·
        refine ⟨1789159471769202983249195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192772981179468655499463 1789159471769202983249195)
        ·
          refine ⟨2683739207653804474873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789159471769202983249195 2683739207653804474873793)
          ·
            refine ⟨2012804405740353356155345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683739207653804474873793 2012804405740353356155345)
            ·
              refine ⟨1509603304305265017116509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012804405740353356155345 1509603304305265017116509)
              ·
                refine ⟨566101239114474381418691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509603304305265017116509 566101239114474381418691)
                ·
                  refine ⟨849151858671711572128037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566101239114474381418691 849151858671711572128037)
                  ·
                    refine ⟨159215973500945919774007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849151858671711572128037 159215973500945919774007)
                    ·
                      rfl

theorem cell23_930216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_930216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930216 prefixEnd_930216 := by exact prefixLift 930216
  have htrace : WordTrace (prefixWord ++ tailWord_930216) baseStart_930216 baseEnd_930216 := by
    simpa [prefixWord, tailWord_930216, baseEnd_930216] using wordTrace_append hprefix tailTrace_930216
  have hstable : (prefixWord ++ tailWord_930216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930216).length < 2 ^ (prefixWord ++ tailWord_930216).sum := by decide
  have hdescent : baseEnd_930216 < baseStart_930216 := by decide
  rcases family_descends (prefixWord ++ tailWord_930216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930229 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 6]
def baseStart_930229 : Nat := 118140960795 + 930229 * 2 ^ 59
def prefixEnd_930229 : Nat := 4983230072969 + 3 ^ 40 * 930229 * 2
def baseEnd_930229 : Nat := 53072732861260689828829

theorem tailTrace_930229 : CollatzResearch.WordTrace tailWord_930229 prefixEnd_930229 53072732861260689828829 := by
  unfold tailWord_930229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33928238946946678309985741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22618825964631118873323827 33928238946946678309985741)
  ·
    refine ⟨12723089605105004366244653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33928238946946678309985741 12723089605105004366244653)
    ·
      refine ⟨4771158601914376637341745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12723089605105004366244653 4771158601914376637341745)
      ·
        refine ⟨3578368951435782478006309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4771158601914376637341745 3578368951435782478006309)
        ·
          refine ⟨670944178394209214626183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3578368951435782478006309 670944178394209214626183)
          ·
            refine ⟨1006416267591313821939275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670944178394209214626183 1006416267591313821939275)
            ·
              refine ⟨1509624401386970732908913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006416267591313821939275 1509624401386970732908913)
              ·
                refine ⟨1132218301040228049681685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509624401386970732908913 1132218301040228049681685)
                ·
                  refine ⟨53072732861260689828829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1132218301040228049681685 53072732861260689828829)
                  ·
                    rfl

theorem cell23_930229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_930229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930229 prefixEnd_930229 := by exact prefixLift 930229
  have htrace : WordTrace (prefixWord ++ tailWord_930229) baseStart_930229 baseEnd_930229 := by
    simpa [prefixWord, tailWord_930229, baseEnd_930229] using wordTrace_append hprefix tailTrace_930229
  have hstable : (prefixWord ++ tailWord_930229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930229).length < 2 ^ (prefixWord ++ tailWord_930229).sum := by decide
  have hdescent : baseEnd_930229 < baseStart_930229 := by decide
  rcases family_descends (prefixWord ++ tailWord_930229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930282 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_930282 : Nat := 118140960795 + 930282 * 2 ^ 59
def prefixEnd_930282 : Nat := 4983230072969 + 3 ^ 40 * 930282 * 2
def baseEnd_930282 : Nat := 477681810226034501096717

theorem tailTrace_930282 : CollatzResearch.WordTrace tailWord_930282 prefixEnd_930282 477681810226034501096717 := by
  unfold tailWord_930282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482543003938667090416275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22620114677169778907776733 8482543003938667090416275)
  ·
    refine ⟨12723814505908000635624413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8482543003938667090416275 12723814505908000635624413)
    ·
      refine ⟨4771430439715500238359155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12723814505908000635624413 4771430439715500238359155)
      ·
        refine ⟨7157145659573250357538733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771430439715500238359155 7157145659573250357538733)
        ·
          refine ⟨2683929622339968884077025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7157145659573250357538733 2683929622339968884077025)
          ·
            refine ⟨2012947216754976663057769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683929622339968884077025 2012947216754976663057769)
            ·
              refine ⟨1509710412566232497293327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012947216754976663057769 1509710412566232497293327)
              ·
                refine ⟨2264565618849348745939991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509710412566232497293327 2264565618849348745939991)
                ·
                  refine ⟨3396848428274023118909987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264565618849348745939991 3396848428274023118909987)
                  ·
                    refine ⟨5095272642411034678364981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396848428274023118909987 5095272642411034678364981)
                    ·
                      refine ⟨477681810226034501096717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5095272642411034678364981 477681810226034501096717)
                      ·
                        rfl

theorem cell23_930282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_930282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930282 prefixEnd_930282 := by exact prefixLift 930282
  have htrace : WordTrace (prefixWord ++ tailWord_930282) baseStart_930282 baseEnd_930282 := by
    simpa [prefixWord, tailWord_930282, baseEnd_930282] using wordTrace_append hprefix tailTrace_930282
  have hstable : (prefixWord ++ tailWord_930282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930282).length < 2 ^ (prefixWord ++ tailWord_930282).sum := by decide
  have hdescent : baseEnd_930282 < baseStart_930282 := by decide
  rcases family_descends (prefixWord ++ tailWord_930282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930285 : List Nat := [1, 5, 1, 3, 1, 1, 11]
def baseStart_930285 : Nat := 118140960795 + 930285 * 2 ^ 59
def prefixEnd_930285 : Nat := 4983230072969 + 3 ^ 40 * 930285 * 2
def baseEnd_930285 : Nat := 5897325316888864066163

theorem tailTrace_930285 : CollatzResearch.WordTrace tailWord_930285 prefixEnd_930285 5897325316888864066163 := by
  unfold tailWord_930285
  simp only [CollatzResearch.WordTrace]
  refine ⟨33930281434743799874024309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22620187623162533249349539 33930281434743799874024309)
  ·
    refine ⟨3180963884507231238189779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33930281434743799874024309 3180963884507231238189779)
    ·
      refine ⟨4771445826760846857284669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180963884507231238189779 4771445826760846857284669)
      ·
        refine ⟨1789292185035317571481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4771445826760846857284669 1789292185035317571481751)
        ·
          refine ⟨2683938277552976357222627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789292185035317571481751 2683938277552976357222627)
          ·
            refine ⟨4025907416329464535833941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683938277552976357222627 4025907416329464535833941)
            ·
              refine ⟨5897325316888864066163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4025907416329464535833941 5897325316888864066163)
              ·
                rfl

theorem cell23_930285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 11].length) (baseStart_930285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930285 prefixEnd_930285 := by exact prefixLift 930285
  have htrace : WordTrace (prefixWord ++ tailWord_930285) baseStart_930285 baseEnd_930285 := by
    simpa [prefixWord, tailWord_930285, baseEnd_930285] using wordTrace_append hprefix tailTrace_930285
  have hstable : (prefixWord ++ tailWord_930285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930285).length < 2 ^ (prefixWord ++ tailWord_930285).sum := by decide
  have hdescent : baseEnd_930285 < baseStart_930285 := by decide
  rcases family_descends (prefixWord ++ tailWord_930285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930306 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_930306 : Nat := 118140960795 + 930306 * 2 ^ 59
def prefixEnd_930306 : Nat := 4983230072969 + 3 ^ 40 * 930306 * 2
def baseEnd_930306 : Nat := 159231377920580802398869

theorem tailTrace_930306 : CollatzResearch.WordTrace tailWord_930306 prefixEnd_930306 159231377920580802398869 := by
  unfold tailWord_930306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482761841916930115134693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22620698245111813640359181 8482761841916930115134693)
  ·
    refine ⟨1590517845359424396587755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8482761841916930115134693 1590517845359424396587755)
    ·
      refine ⟨2385776768039136594881633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590517845359424396587755 2385776768039136594881633)
      ·
        refine ⟨1789332576029352446161225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385776768039136594881633 1789332576029352446161225)
        ·
          refine ⟨1341999432022014334620919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789332576029352446161225 1341999432022014334620919)
          ·
            refine ⟨2012999148033021501931379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341999432022014334620919 2012999148033021501931379)
            ·
              refine ⟨3019498722049532252897069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012999148033021501931379 3019498722049532252897069)
              ·
                refine ⟨1132312020768574594836401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3019498722049532252897069 1132312020768574594836401)
                ·
                  refine ⟨849234015576430946127301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132312020768574594836401 849234015576430946127301)
                  ·
                    refine ⟨159231377920580802398869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849234015576430946127301 159231377920580802398869)
                    ·
                      rfl

theorem cell23_930306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_930306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930306 prefixEnd_930306 := by exact prefixLift 930306
  have htrace : WordTrace (prefixWord ++ tailWord_930306) baseStart_930306 baseEnd_930306 := by
    simpa [prefixWord, tailWord_930306, baseEnd_930306] using wordTrace_append hprefix tailTrace_930306
  have hstable : (prefixWord ++ tailWord_930306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930306).length < 2 ^ (prefixWord ++ tailWord_930306).sum := by decide
  have hdescent : baseEnd_930306 < baseStart_930306 := by decide
  rcases family_descends (prefixWord ++ tailWord_930306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930346 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_930346 : Nat := 118140960795 + 930346 * 2 ^ 59
def prefixEnd_930346 : Nat := 4983230072969 + 3 ^ 40 * 930346 * 2
def baseEnd_930346 : Nat := 477714672987922250696423

theorem tailTrace_930346 : CollatzResearch.WordTrace tailWord_930346 prefixEnd_930346 477714672987922250696423 := by
  unfold tailWord_930346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483126571880701822998723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22621670858348538194663261 8483126571880701822998723)
  ·
    refine ⟨12724689857821052734498085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8483126571880701822998723 12724689857821052734498085)
    ·
      refine ⟨2385879348341447387718391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12724689857821052734498085 2385879348341447387718391)
      ·
        refine ⟨3578819022512171081577587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385879348341447387718391 3578819022512171081577587)
        ·
          refine ⟨5368228533768256622366381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578819022512171081577587 5368228533768256622366381)
          ·
            refine ⟨2013085700163096233387393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5368228533768256622366381 2013085700163096233387393)
            ·
              refine ⟨1509814275122322175040545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013085700163096233387393 1509814275122322175040545)
              ·
                refine ⟨1132360706341741631280409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509814275122322175040545 1132360706341741631280409)
                ·
                  refine ⟨849270529756306223460307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132360706341741631280409 849270529756306223460307)
                  ·
                    refine ⟨1273905794634459335190461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849270529756306223460307 1273905794634459335190461)
                    ·
                      refine ⟨477714672987922250696423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1273905794634459335190461 477714672987922250696423)
                      ·
                        rfl

theorem cell23_930346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_930346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930346 prefixEnd_930346 := by exact prefixLift 930346
  have htrace : WordTrace (prefixWord ++ tailWord_930346) baseStart_930346 baseEnd_930346 := by
    simpa [prefixWord, tailWord_930346, baseEnd_930346] using wordTrace_append hprefix tailTrace_930346
  have hstable : (prefixWord ++ tailWord_930346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930346).length < 2 ^ (prefixWord ++ tailWord_930346).sum := by decide
  have hdescent : baseEnd_930346 < baseStart_930346 := by decide
  rcases family_descends (prefixWord ++ tailWord_930346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930355 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3]
def baseStart_930355 : Nat := 118140960795 + 930355 * 2 ^ 59
def prefixEnd_930355 : Nat := 4983230072969 + 3 ^ 40 * 930355 * 2
def baseEnd_930355 : Nat := 477719294313812715483881

theorem tailTrace_930355 : CollatzResearch.WordTrace tailWord_930355 prefixEnd_930355 477719294313812715483881 := by
  unfold tailWord_930355
  simp only [CollatzResearch.WordTrace]
  refine ⟨33932834544490201829072519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22621889696326801219381679 33932834544490201829072519)
  ·
    refine ⟨50899251816735302743608779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33932834544490201829072519 50899251816735302743608779)
    ·
      refine ⟨76348877725102954115413169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50899251816735302743608779 76348877725102954115413169)
      ·
        refine ⟨57261658293827215586559877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76348877725102954115413169 57261658293827215586559877)
        ·
          refine ⟨10736560930092602922479977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57261658293827215586559877 10736560930092602922479977)
          ·
            refine ⟨8052420697569452191859983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10736560930092602922479977 8052420697569452191859983)
            ·
              refine ⟨12078631046354178287789975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052420697569452191859983 12078631046354178287789975)
              ·
                refine ⟨18117946569531267431684963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12078631046354178287789975 18117946569531267431684963)
                ·
                  refine ⟨27176919854296901147527445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18117946569531267431684963 27176919854296901147527445)
                  ·
                    refine ⟨1273918118170167241290349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27176919854296901147527445 1273918118170167241290349)
                    ·
                      refine ⟨477719294313812715483881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1273918118170167241290349 477719294313812715483881)
                      ·
                        rfl

theorem cell23_930355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_930355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930355 prefixEnd_930355 := by exact prefixLift 930355
  have htrace : WordTrace (prefixWord ++ tailWord_930355) baseStart_930355 baseEnd_930355 := by
    simpa [prefixWord, tailWord_930355, baseEnd_930355] using wordTrace_append hprefix tailTrace_930355
  have hstable : (prefixWord ++ tailWord_930355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930355).length < 2 ^ (prefixWord ++ tailWord_930355).sum := by decide
  have hdescent : baseEnd_930355 < baseStart_930355 := by decide
  rcases family_descends (prefixWord ++ tailWord_930355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930369 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_930369 : Nat := 118140960795 + 930369 * 2 ^ 59
def prefixEnd_930369 : Nat := 4983230072969 + 3 ^ 40 * 930369 * 2
def baseEnd_930369 : Nat := 477726483042975660708817

theorem tailTrace_930369 : CollatzResearch.WordTrace tailWord_930369 prefixEnd_930369 477726483042975660708817 := by
  unfold tailWord_930369
  simp only [CollatzResearch.WordTrace]
  refine ⟨33933345166439482220082161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22622230110959654813388107 33933345166439482220082161)
  ·
    refine ⟨25450008874829611665061621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33933345166439482220082161 25450008874829611665061621)
    ·
      refine ⟨2385938332015276093599527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25450008874829611665061621 2385938332015276093599527)
      ·
        refine ⟨3578907498022914140399291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385938332015276093599527 3578907498022914140399291)
        ·
          refine ⟨5368361247034371210598937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578907498022914140399291 5368361247034371210598937)
          ·
            refine ⟨4026270935275778407949203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368361247034371210598937 4026270935275778407949203)
            ·
              refine ⟨6039406402913667611923805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026270935275778407949203 6039406402913667611923805)
              ·
                refine ⟨2264777401092625354471427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6039406402913667611923805 2264777401092625354471427)
                ·
                  refine ⟨3397166101638938031707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264777401092625354471427 3397166101638938031707141)
                  ·
                    refine ⟨636968644057300880945089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3397166101638938031707141 636968644057300880945089)
                    ·
                      refine ⟨477726483042975660708817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636968644057300880945089 477726483042975660708817)
                      ·
                        rfl

theorem cell23_930369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_930369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930369 prefixEnd_930369 := by exact prefixLift 930369
  have htrace : WordTrace (prefixWord ++ tailWord_930369) baseStart_930369 baseEnd_930369 := by
    simpa [prefixWord, tailWord_930369, baseEnd_930369] using wordTrace_append hprefix tailTrace_930369
  have hstable : (prefixWord ++ tailWord_930369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930369).length < 2 ^ (prefixWord ++ tailWord_930369).sum := by decide
  have hdescent : baseEnd_930369 < baseStart_930369 := by decide
  rcases family_descends (prefixWord ++ tailWord_930369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930375 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 9]
def baseStart_930375 : Nat := 118140960795 + 930375 * 2 ^ 59
def prefixEnd_930375 : Nat := 4983230072969 + 3 ^ 40 * 930375 * 2
def baseEnd_930375 : Nat := 53081062658544737470421

theorem tailTrace_930375 : CollatzResearch.WordTrace tailWord_930375 prefixEnd_930375 53081062658544737470421 := by
  unfold tailWord_930375
  simp only [CollatzResearch.WordTrace]
  refine ⟨33933564004417745244800579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22622376002945163496533719 33933564004417745244800579)
  ·
    refine ⟨50900346006626617867200869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33933564004417745244800579 50900346006626617867200869)
    ·
      refine ⟨9543814876242490850100163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50900346006626617867200869 9543814876242490850100163)
      ·
        refine ⟨14315722314363736275150245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543814876242490850100163 14315722314363736275150245)
        ·
          refine ⟨2684197933943200551590671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14315722314363736275150245 2684197933943200551590671)
          ·
            refine ⟨4026296900914800827386007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684197933943200551590671 4026296900914800827386007)
            ·
              refine ⟨6039445351372201241079011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026296900914800827386007 6039445351372201241079011)
              ·
                refine ⟨9059168027058301861618517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039445351372201241079011 9059168027058301861618517)
                ·
                  refine ⟨53081062658544737470421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9059168027058301861618517 53081062658544737470421)
                  ·
                    rfl

theorem cell23_930375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 9].length) (baseStart_930375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930375 prefixEnd_930375 := by exact prefixLift 930375
  have htrace : WordTrace (prefixWord ++ tailWord_930375) baseStart_930375 baseEnd_930375 := by
    simpa [prefixWord, tailWord_930375, baseEnd_930375] using wordTrace_append hprefix tailTrace_930375
  have hstable : (prefixWord ++ tailWord_930375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930375).length < 2 ^ (prefixWord ++ tailWord_930375).sum := by decide
  have hdescent : baseEnd_930375 < baseStart_930375 := by decide
  rcases family_descends (prefixWord ++ tailWord_930375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930392 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 5]
def baseStart_930392 : Nat := 118140960795 + 930392 * 2 ^ 59
def prefixEnd_930392 : Nat := 4983230072969 + 3 ^ 40 * 930392 * 2
def baseEnd_930392 : Nat := 53082032566447674524579

theorem tailTrace_930392 : CollatzResearch.WordTrace tailWord_930392 prefixEnd_930392 53082032566447674524579 := by
  unfold tailWord_930392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967092022678078574084715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22622789363570771432112953 16967092022678078574084715)
  ·
    refine ⟨25450638034017117861127073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16967092022678078574084715 25450638034017117861127073)
    ·
      refine ⟨19087978525512838395845305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25450638034017117861127073 19087978525512838395845305)
      ·
        refine ⟨14315983894134628796883979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19087978525512838395845305 14315983894134628796883979)
        ·
          refine ⟨21473975841201943195325969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315983894134628796883979 21473975841201943195325969)
          ·
            refine ⟨16105481880901457396494477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473975841201943195325969 16105481880901457396494477)
            ·
              refine ⟨6039555705338046523685429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16105481880901457396494477 6039555705338046523685429)
              ·
                refine ⟨566208347375441861595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6039555705338046523685429 566208347375441861595509)
                ·
                  refine ⟨53082032566447674524579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 566208347375441861595509 53082032566447674524579)
                  ·
                    rfl

theorem cell23_930392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 5].length) (baseStart_930392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930392 prefixEnd_930392 := by exact prefixLift 930392
  have htrace : WordTrace (prefixWord ++ tailWord_930392) baseStart_930392 baseEnd_930392 := by
    simpa [prefixWord, tailWord_930392, baseEnd_930392] using wordTrace_append hprefix tailTrace_930392
  have hstable : (prefixWord ++ tailWord_930392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930392).length < 2 ^ (prefixWord ++ tailWord_930392).sum := by decide
  have hdescent : baseEnd_930392 < baseStart_930392 := by decide
  rcases family_descends (prefixWord ++ tailWord_930392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930412 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_930412 : Nat := 118140960795 + 930412 * 2 ^ 59
def prefixEnd_930412 : Nat := 4983230072969 + 3 ^ 40 * 930412 * 2
def baseEnd_930412 : Nat := 477748562711118992471119

theorem tailTrace_930412 : CollatzResearch.WordTrace tailWord_930412 prefixEnd_930412 477748562711118992471119 := by
  unfold tailWord_930412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967456752641850281948745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22623275670189133709264993 16967456752641850281948745)
  ·
    refine ⟨12725592564481387711461559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16967456752641850281948745 12725592564481387711461559)
    ·
      refine ⟨19088388846722081567192339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725592564481387711461559 19088388846722081567192339)
      ·
        refine ⟨28632583270083122350788509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19088388846722081567192339 28632583270083122350788509)
        ·
          refine ⟨10737218726281170881545691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28632583270083122350788509 10737218726281170881545691)
          ·
            refine ⟨16105828089421756322318537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737218726281170881545691 16105828089421756322318537)
            ·
              refine ⟨12079371067066317241738903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16105828089421756322318537 12079371067066317241738903)
              ·
                refine ⟨18119056600599475862608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12079371067066317241738903 18119056600599475862608355)
                ·
                  refine ⟨27178584900899213793912533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119056600599475862608355 27178584900899213793912533)
                  ·
                    refine ⟨636998083614825323294825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27178584900899213793912533 636998083614825323294825)
                    ·
                      refine ⟨477748562711118992471119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 636998083614825323294825 477748562711118992471119)
                      ·
                        rfl

theorem cell23_930412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_930412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930412 prefixEnd_930412 := by exact prefixLift 930412
  have htrace : WordTrace (prefixWord ++ tailWord_930412) baseStart_930412 baseEnd_930412 := by
    simpa [prefixWord, tailWord_930412, baseEnd_930412] using wordTrace_append hprefix tailTrace_930412
  have hstable : (prefixWord ++ tailWord_930412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930412).length < 2 ^ (prefixWord ++ tailWord_930412).sum := by decide
  have hdescent : baseEnd_930412 < baseStart_930412 := by decide
  rcases family_descends (prefixWord ++ tailWord_930412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930415 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_930415 : Nat := 118140960795 + 930415 * 2 ^ 59
def prefixEnd_930415 : Nat := 4983230072969 + 3 ^ 40 * 930415 * 2
def baseEnd_930415 : Nat := 477750103153082480733605

theorem tailTrace_930415 : CollatzResearch.WordTrace tailWord_930415 prefixEnd_930415 477750103153082480733605 := by
  unfold tailWord_930415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935022924272832076256699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22623348616181888050837799 33935022924272832076256699)
  ·
    refine ⟨50902534386409248114385049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33935022924272832076256699 50902534386409248114385049)
    ·
      refine ⟨38176900789806936085788787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50902534386409248114385049 38176900789806936085788787)
      ·
        refine ⟨57265351184710404128683181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38176900789806936085788787 57265351184710404128683181)
        ·
          refine ⟨21474506694266401548256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57265351184710404128683181 21474506694266401548256193)
          ·
            refine ⟨16105880020699801161192145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21474506694266401548256193 16105880020699801161192145)
            ·
              refine ⟨12079410015524850870894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16105880020699801161192145 12079410015524850870894109)
              ·
                refine ⟨4529778755821819076585291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12079410015524850870894109 4529778755821819076585291)
                ·
                  refine ⟨6794668133732728614877937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529778755821819076585291 6794668133732728614877937)
                  ·
                    refine ⟨5096001100299546461158453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794668133732728614877937 5096001100299546461158453)
                    ·
                      refine ⟨477750103153082480733605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5096001100299546461158453 477750103153082480733605)
                      ·
                        rfl

theorem cell23_930415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_930415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930415 prefixEnd_930415 := by exact prefixLift 930415
  have htrace : WordTrace (prefixWord ++ tailWord_930415) baseStart_930415 baseEnd_930415 := by
    simpa [prefixWord, tailWord_930415, baseEnd_930415] using wordTrace_append hprefix tailTrace_930415
  have hstable : (prefixWord ++ tailWord_930415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930415).length < 2 ^ (prefixWord ++ tailWord_930415).sum := by decide
  have hdescent : baseEnd_930415 < baseStart_930415 := by decide
  rcases family_descends (prefixWord ++ tailWord_930415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930505 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_930505 : Nat := 118140960795 + 930505 * 2 ^ 59
def prefixEnd_930505 : Nat := 4983230072969 + 3 ^ 40 * 930505 * 2
def baseEnd_930505 : Nat := 477796316411987128608191

theorem tailTrace_930505 : CollatzResearch.WordTrace tailWord_930505 prefixEnd_930505 477796316411987128608191 := by
  unfold tailWord_930505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938305493946777447032969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22625536995964518298021979 33938305493946777447032969)
  ·
    refine ⟨25453729120460083085274727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33938305493946777447032969 25453729120460083085274727)
    ·
      refine ⟨38180593680690124627912091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453729120460083085274727 38180593680690124627912091)
      ·
        refine ⟨57270890521035186941868137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38180593680690124627912091 57270890521035186941868137)
        ·
          refine ⟨42953167890776390206401103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57270890521035186941868137 42953167890776390206401103)
          ·
            refine ⟨64429751836164585309601655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42953167890776390206401103 64429751836164585309601655)
            ·
              refine ⟨96644627754246877964402483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64429751836164585309601655 96644627754246877964402483)
              ·
                refine ⟨144966941631370316946603725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96644627754246877964402483 144966941631370316946603725)
                ·
                  refine ⟨54362603111763868854976397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144966941631370316946603725 54362603111763868854976397)
                  ·
                    refine ⟨20385976166911450820616149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54362603111763868854976397 20385976166911450820616149)
                    ·
                      refine ⟨477796316411987128608191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20385976166911450820616149 477796316411987128608191)
                      ·
                        rfl

theorem cell23_930505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_930505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930505 prefixEnd_930505 := by exact prefixLift 930505
  have htrace : WordTrace (prefixWord ++ tailWord_930505) baseStart_930505 baseEnd_930505 := by
    simpa [prefixWord, tailWord_930505, baseEnd_930505] using wordTrace_append hprefix tailTrace_930505
  have hstable : (prefixWord ++ tailWord_930505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930505).length < 2 ^ (prefixWord ++ tailWord_930505).sum := by decide
  have hdescent : baseEnd_930505 < baseStart_930505 := by decide
  rcases family_descends (prefixWord ++ tailWord_930505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930516 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 6]
def baseStart_930516 : Nat := 118140960795 + 930516 * 2 ^ 59
def prefixEnd_930516 : Nat := 4983230072969 + 3 ^ 40 * 930516 * 2
def baseEnd_930516 : Nat := 53089107188798509507849

theorem tailTrace_930516 : CollatzResearch.WordTrace tailWord_930516 prefixEnd_930516 53089107188798509507849 := by
  unfold tailWord_930516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969353348453463162841701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22625804464604617550455601 16969353348453463162841701)
  ·
    refine ⟨3181753752835024343032819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16969353348453463162841701 3181753752835024343032819)
    ·
      refine ⟨4772630629252536514549229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181753752835024343032819 4772630629252536514549229)
      ·
        refine ⟨1789736485969701192955961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4772630629252536514549229 1789736485969701192955961)
        ·
          refine ⟨1342302364477275894716971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789736485969701192955961 1342302364477275894716971)
          ·
            refine ⟨2013453546715913842075457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342302364477275894716971 2013453546715913842075457)
            ·
              refine ⟨1510090160036935381556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013453546715913842075457 1510090160036935381556593)
              ·
                refine ⟨1132567620027701536167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510090160036935381556593 1132567620027701536167445)
                ·
                  refine ⟨53089107188798509507849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1132567620027701536167445 53089107188798509507849)
                  ·
                    rfl

theorem cell23_930516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_930516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930516 prefixEnd_930516 := by exact prefixLift 930516
  have htrace : WordTrace (prefixWord ++ tailWord_930516) baseStart_930516 baseEnd_930516 := by
    simpa [prefixWord, tailWord_930516, baseEnd_930516] using wordTrace_append hprefix tailTrace_930516
  have hstable : (prefixWord ++ tailWord_930516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930516).length < 2 ^ (prefixWord ++ tailWord_930516).sum := by decide
  have hdescent : baseEnd_930516 < baseStart_930516 := by decide
  rcases family_descends (prefixWord ++ tailWord_930516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930606 : List Nat := [4, 1, 3, 2, 1, 1, 4, 7]
def baseStart_930606 : Nat := 118140960795 + 930606 * 2 ^ 59
def prefixEnd_930606 : Nat := 4983230072969 + 3 ^ 40 * 930606 * 2
def baseEnd_930606 : Nat := 17698080665114490127601

theorem tailTrace_930606 : CollatzResearch.WordTrace tailWord_930606 prefixEnd_930606 17698080665114490127601 := by
  unfold tailWord_930606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242748658322608962057459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22627992844387247797639781 4242748658322608962057459)
  ·
    refine ⟨6364122987483913443086189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242748658322608962057459 6364122987483913443086189)
    ·
      refine ⟨2386546120306467541157321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6364122987483913443086189 2386546120306467541157321)
      ·
        refine ⟨1789909590229850655867991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2386546120306467541157321 1789909590229850655867991)
        ·
          refine ⟨2684864385344775983801987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789909590229850655867991 2684864385344775983801987)
          ·
            refine ⟨4027296578017163975702981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684864385344775983801987 4027296578017163975702981)
            ·
              refine ⟨755118108378218245444309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4027296578017163975702981 755118108378218245444309)
              ·
                refine ⟨17698080665114490127601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 755118108378218245444309 17698080665114490127601)
                ·
                  rfl

theorem cell23_930606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_930606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930606 prefixEnd_930606 := by exact prefixLift 930606
  have htrace : WordTrace (prefixWord ++ tailWord_930606) baseStart_930606 baseEnd_930606 := by
    simpa [prefixWord, tailWord_930606, baseEnd_930606] using wordTrace_append hprefix tailTrace_930606
  have hstable : (prefixWord ++ tailWord_930606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930606).length < 2 ^ (prefixWord ++ tailWord_930606).sum := by decide
  have hdescent : baseEnd_930606 < baseStart_930606 := by decide
  rcases family_descends (prefixWord ++ tailWord_930606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930650 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_930650 : Nat := 118140960795 + 930650 * 2 ^ 59
def prefixEnd_930650 : Nat := 4983230072969 + 3 ^ 40 * 930650 * 2
def baseEnd_930650 : Nat := 477870771106889061295025

theorem tailTrace_930650 : CollatzResearch.WordTrace tailWord_930650 prefixEnd_930650 477870771106889061295025 := by
  unfold tailWord_930650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8485898519605366802765351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22629062718947644807374269 8485898519605366802765351)
  ·
    refine ⟨12728847779408050204148027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8485898519605366802765351 12728847779408050204148027)
    ·
      refine ⟨19093271669112075306222041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12728847779408050204148027 19093271669112075306222041)
      ·
        refine ⟨14319953751834056479666531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19093271669112075306222041 14319953751834056479666531)
        ·
          refine ⟨21479930627751084719499797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319953751834056479666531 21479930627751084719499797)
          ·
            refine ⟨1006871748175832096226553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21479930627751084719499797 1006871748175832096226553)
            ·
              refine ⟨755153811131874072169915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006871748175832096226553 755153811131874072169915)
              ·
                refine ⟨1132730716697811108254873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755153811131874072169915 1132730716697811108254873)
                ·
                  refine ⟨849548037523358331191155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132730716697811108254873 849548037523358331191155)
                  ·
                    refine ⟨1274322056285037496786733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849548037523358331191155 1274322056285037496786733)
                    ·
                      refine ⟨477870771106889061295025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274322056285037496786733 477870771106889061295025)
                      ·
                        rfl

theorem cell23_930650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_930650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930650 prefixEnd_930650 := by exact prefixLift 930650
  have htrace : WordTrace (prefixWord ++ tailWord_930650) baseStart_930650 baseEnd_930650 := by
    simpa [prefixWord, tailWord_930650, baseEnd_930650] using wordTrace_append hprefix tailTrace_930650
  have hstable : (prefixWord ++ tailWord_930650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930650).length < 2 ^ (prefixWord ++ tailWord_930650).sum := by decide
  have hdescent : baseEnd_930650 < baseStart_930650 := by decide
  rcases family_descends (prefixWord ++ tailWord_930650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930656 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2]
def baseStart_930656 : Nat := 118140960795 + 930656 * 2 ^ 59
def prefixEnd_930656 : Nat := 4983230072969 + 3 ^ 40 * 930656 * 2
def baseEnd_930656 : Nat := 477873851990816037819997

theorem tailTrace_930656 : CollatzResearch.WordTrace tailWord_930656 prefixEnd_930656 477873851990816037819997 := by
  unfold tailWord_930656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971906458199865117889911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22629208610933153490519881 16971906458199865117889911)
  ·
    refine ⟨25457859687299797676834867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971906458199865117889911 25457859687299797676834867)
    ·
      refine ⟨38186789530949696515252301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457859687299797676834867 38186789530949696515252301)
      ·
        refine ⟨14320046074106136193219613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38186789530949696515252301 14320046074106136193219613)
        ·
          refine ⟨5370017277789801072457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14320046074106136193219613 5370017277789801072457355)
          ·
            refine ⟨8055025916684701608686033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370017277789801072457355 8055025916684701608686033)
            ·
              refine ⟨6041269437513526206514525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055025916684701608686033 6041269437513526206514525)
              ·
                refine ⟨2265476039067572327442947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6041269437513526206514525 2265476039067572327442947)
                ·
                  refine ⟨3398214058601358491164421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265476039067572327442947 3398214058601358491164421)
                  ·
                    refine ⟨637165135987754717093329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398214058601358491164421 637165135987754717093329)
                    ·
                      refine ⟨477873851990816037819997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637165135987754717093329 477873851990816037819997)
                      ·
                        rfl

theorem cell23_930656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_930656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930656 prefixEnd_930656 := by exact prefixLift 930656
  have htrace : WordTrace (prefixWord ++ tailWord_930656) baseStart_930656 baseEnd_930656 := by
    simpa [prefixWord, tailWord_930656, baseEnd_930656] using wordTrace_append hprefix tailTrace_930656
  have hstable : (prefixWord ++ tailWord_930656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930656).length < 2 ^ (prefixWord ++ tailWord_930656).sum := by decide
  have hdescent : baseEnd_930656 < baseStart_930656 := by decide
  rcases family_descends (prefixWord ++ tailWord_930656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930659 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_930659 : Nat := 118140960795 + 930659 * 2 ^ 59
def prefixEnd_930659 : Nat := 4983230072969 + 3 ^ 40 * 930659 * 2
def baseEnd_930659 : Nat := 477875392432779526082483

theorem tailTrace_930659 : CollatzResearch.WordTrace tailWord_930659 prefixEnd_930659 477875392432779526082483 := by
  unfold tailWord_930659
  simp only [CollatzResearch.WordTrace]
  refine ⟨33943922335388861748139031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22629281556925907832092687 33943922335388861748139031)
  ·
    refine ⟨50915883503083292622208547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33943922335388861748139031 50915883503083292622208547)
    ·
      refine ⟨76373825254624938933312821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50915883503083292622208547 76373825254624938933312821)
      ·
        refine ⟨7160046117621088024998077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76373825254624938933312821 7160046117621088024998077)
        ·
          refine ⟨2685017294107908009374279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7160046117621088024998077 2685017294107908009374279)
          ·
            refine ⟨4027525941161862014061419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685017294107908009374279 4027525941161862014061419)
            ·
              refine ⟨6041288911742793021092129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027525941161862014061419 6041288911742793021092129)
              ·
                refine ⟨4530966683807094765819097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041288911742793021092129 4530966683807094765819097)
                ·
                  refine ⟨3398225012855321074364323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530966683807094765819097 3398225012855321074364323)
                  ·
                    refine ⟨5097337519282981611546485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3398225012855321074364323 5097337519282981611546485)
                    ·
                      refine ⟨477875392432779526082483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5097337519282981611546485 477875392432779526082483)
                      ·
                        rfl

theorem cell23_930659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_930659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930659 prefixEnd_930659 := by exact prefixLift 930659
  have htrace : WordTrace (prefixWord ++ tailWord_930659) baseStart_930659 baseEnd_930659 := by
    simpa [prefixWord, tailWord_930659, baseEnd_930659] using wordTrace_append hprefix tailTrace_930659
  have hstable : (prefixWord ++ tailWord_930659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930659).length < 2 ^ (prefixWord ++ tailWord_930659).sum := by decide
  have hdescent : baseEnd_930659 < baseStart_930659 := by decide
  rcases family_descends (prefixWord ++ tailWord_930659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930660 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_930660 : Nat := 118140960795 + 930660 * 2 ^ 59
def prefixEnd_930660 : Nat := 4983230072969 + 3 ^ 40 * 930660 * 2
def baseEnd_930660 : Nat := 477875905913434022169979

theorem tailTrace_930660 : CollatzResearch.WordTrace tailWord_930660 prefixEnd_930660 477875905913434022169979 := by
  unfold tailWord_930660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971979404192619459462717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22629305872256825945950289 16971979404192619459462717)
  ·
    refine ⟨6364492276572232297298519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16971979404192619459462717 6364492276572232297298519)
    ·
      refine ⟨9546738414858348445947779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6364492276572232297298519 9546738414858348445947779)
      ·
        refine ⟨14320107622287522668921669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546738414858348445947779 14320107622287522668921669)
        ·
          refine ⟨2685020179178910500422813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14320107622287522668921669 2685020179178910500422813)
          ·
            refine ⟨1006882567192091437658555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2685020179178910500422813 1006882567192091437658555)
            ·
              refine ⟨1510323850788137156487833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006882567192091437658555 1510323850788137156487833)
              ·
                refine ⟨1132742888091102867365875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510323850788137156487833 1132742888091102867365875)
                ·
                  refine ⟨1699114332136654301048813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132742888091102867365875 1699114332136654301048813)
                  ·
                    refine ⟨637167874551245362893305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699114332136654301048813 637167874551245362893305)
                    ·
                      refine ⟨477875905913434022169979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637167874551245362893305 477875905913434022169979)
                      ·
                        rfl

theorem cell23_930660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_930660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930660 prefixEnd_930660 := by exact prefixLift 930660
  have htrace : WordTrace (prefixWord ++ tailWord_930660) baseStart_930660 baseEnd_930660 := by
    simpa [prefixWord, tailWord_930660, baseEnd_930660] using wordTrace_append hprefix tailTrace_930660
  have hstable : (prefixWord ++ tailWord_930660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930660).length < 2 ^ (prefixWord ++ tailWord_930660).sum := by decide
  have hdescent : baseEnd_930660 < baseStart_930660 := by decide
  rcases family_descends (prefixWord ++ tailWord_930660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930669 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_930669 : Nat := 118140960795 + 930669 * 2 ^ 59
def prefixEnd_930669 : Nat := 4983230072969 + 3 ^ 40 * 930669 * 2
def baseEnd_930669 : Nat := 477880527239324486957437

theorem tailTrace_930669 : CollatzResearch.WordTrace tailWord_930669 prefixEnd_930669 477880527239324486957437 := by
  unfold tailWord_930669
  simp only [CollatzResearch.WordTrace]
  refine ⟨33944287065352633456003061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22629524710235088970668707 33944287065352633456003061)
  ·
    refine ⟨3182276912376809386500287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33944287065352633456003061 3182276912376809386500287)
    ·
      refine ⟨4773415368565214079750431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182276912376809386500287 4773415368565214079750431)
      ·
        refine ⟨7160123052847821119625647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773415368565214079750431 7160123052847821119625647)
        ·
          refine ⟨10740184579271731679438471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160123052847821119625647 10740184579271731679438471)
          ·
            refine ⟨16110276868907597519157707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10740184579271731679438471 16110276868907597519157707)
            ·
              refine ⟨24165415303361396278736561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16110276868907597519157707 24165415303361396278736561)
              ·
                refine ⟨18124061477521047209052421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24165415303361396278736561 18124061477521047209052421)
                ·
                  refine ⟨3398261527035196351697329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18124061477521047209052421 3398261527035196351697329)
                  ·
                    refine ⟨2548696145276397263772997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398261527035196351697329 2548696145276397263772997)
                    ·
                      refine ⟨477880527239324486957437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2548696145276397263772997 477880527239324486957437)
                      ·
                        rfl

theorem cell23_930669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_930669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930669 prefixEnd_930669 := by exact prefixLift 930669
  have htrace : WordTrace (prefixWord ++ tailWord_930669) baseStart_930669 baseEnd_930669 := by
    simpa [prefixWord, tailWord_930669, baseEnd_930669] using wordTrace_append hprefix tailTrace_930669
  have hstable : (prefixWord ++ tailWord_930669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930669).length < 2 ^ (prefixWord ++ tailWord_930669).sum := by decide
  have hdescent : baseEnd_930669 < baseStart_930669 := by decide
  rcases family_descends (prefixWord ++ tailWord_930669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930729 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_930729 : Nat := 118140960795 + 930729 * 2 ^ 59
def prefixEnd_930729 : Nat := 4983230072969 + 3 ^ 40 * 930729 * 2
def baseEnd_930729 : Nat := 477911336078594252207161

theorem tailTrace_930729 : CollatzResearch.WordTrace tailWord_930729 prefixEnd_930729 477911336078594252207161 := by
  unfold tailWord_930729
  simp only [CollatzResearch.WordTrace]
  refine ⟨33946475445135263703187241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22630983630090175802124827 33946475445135263703187241)
  ·
    refine ⟨25459856583851447777390431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33946475445135263703187241 25459856583851447777390431)
    ·
      refine ⟨38189784875777171666085647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25459856583851447777390431 38189784875777171666085647)
      ·
        refine ⟨57284677313665757499128471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38189784875777171666085647 57284677313665757499128471)
        ·
          refine ⟨85927015970498636248692707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57284677313665757499128471 85927015970498636248692707)
          ·
            refine ⟨128890523955747954373039061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85927015970498636248692707 128890523955747954373039061)
            ·
              refine ⟨3020871655212842680618103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128890523955747954373039061 3020871655212842680618103)
              ·
                refine ⟨4531307482819264020927155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020871655212842680618103 4531307482819264020927155)
                ·
                  refine ⟨6796961224228896031390733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531307482819264020927155 6796961224228896031390733)
                  ·
                    refine ⟨2548860459085836011771525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6796961224228896031390733 2548860459085836011771525)
                    ·
                      refine ⟨477911336078594252207161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2548860459085836011771525 477911336078594252207161)
                      ·
                        rfl

theorem cell23_930729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_930729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930729 prefixEnd_930729 := by exact prefixLift 930729
  have htrace : WordTrace (prefixWord ++ tailWord_930729) baseStart_930729 baseEnd_930729 := by
    simpa [prefixWord, tailWord_930729, baseEnd_930729] using wordTrace_append hprefix tailTrace_930729
  have hstable : (prefixWord ++ tailWord_930729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930729).length < 2 ^ (prefixWord ++ tailWord_930729).sum := by decide
  have hdescent : baseEnd_930729 < baseStart_930729 := by decide
  rcases family_descends (prefixWord ++ tailWord_930729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930746 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_930746 : Nat := 118140960795 + 930746 * 2 ^ 59
def prefixEnd_930746 : Nat := 4983230072969 + 3 ^ 40 * 930746 * 2
def baseEnd_930746 : Nat := 477920065249720685694583

theorem tailTrace_930746 : CollatzResearch.WordTrace tailWord_930746 prefixEnd_930746 477920065249720685694583 := by
  unfold tailWord_930746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486773871518418901639023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22631396990715783737704061 8486773871518418901639023)
  ·
    refine ⟨12730160807277628352458535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8486773871518418901639023 12730160807277628352458535)
    ·
      refine ⟨19095241210916442528687803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12730160807277628352458535 19095241210916442528687803)
      ·
        refine ⟨28642861816374663793031705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19095241210916442528687803 28642861816374663793031705)
        ·
          refine ⟨21482146362280997844773779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28642861816374663793031705 21482146362280997844773779)
          ·
            refine ⟨32223219543421496767160669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482146362280997844773779 32223219543421496767160669)
            ·
              refine ⟨12083707328783061287685251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32223219543421496767160669 12083707328783061287685251)
              ·
                refine ⟨18125560993174591931527877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12083707328783061287685251 18125560993174591931527877)
                ·
                  refine ⟨3398542686220235987161477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18125560993174591931527877 3398542686220235987161477)
                  ·
                    refine ⟨637226753666294247592777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398542686220235987161477 637226753666294247592777)
                    ·
                      refine ⟨477920065249720685694583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637226753666294247592777 477920065249720685694583)
                      ·
                        rfl

theorem cell23_930746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_930746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930746 prefixEnd_930746 := by exact prefixLift 930746
  have htrace : WordTrace (prefixWord ++ tailWord_930746) baseStart_930746 baseEnd_930746 := by
    simpa [prefixWord, tailWord_930746, baseEnd_930746] using wordTrace_append hprefix tailTrace_930746
  have hstable : (prefixWord ++ tailWord_930746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930746).length < 2 ^ (prefixWord ++ tailWord_930746).sum := by decide
  have hdescent : baseEnd_930746 < baseStart_930746 := by decide
  rcases family_descends (prefixWord ++ tailWord_930746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930758 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_930758 : Nat := 118140960795 + 930758 * 2 ^ 59
def prefixEnd_930758 : Nat := 4983230072969 + 3 ^ 40 * 930758 * 2
def baseEnd_930758 : Nat := 477926227017574638744529

theorem tailTrace_930758 : CollatzResearch.WordTrace tailWord_930758 prefixEnd_930758 477926227017574638744529 := by
  unfold tailWord_930758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060860411313443801749779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22631688774686801103995285 1060860411313443801749779)
  ·
    refine ⟨1591290616970165702624669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1060860411313443801749779 1591290616970165702624669)
    ·
      refine ⟨596733981363812138484251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1591290616970165702624669 596733981363812138484251)
      ·
        refine ⟨895100972045718207726377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596733981363812138484251 895100972045718207726377)
        ·
          refine ⟨671325729034288655794783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895100972045718207726377 671325729034288655794783)
          ·
            refine ⟨1006988593551432983692175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671325729034288655794783 1006988593551432983692175)
            ·
              refine ⟨1510482890327149475538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006988593551432983692175 1510482890327149475538263)
              ·
                refine ⟨2265724335490724213307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510482890327149475538263 2265724335490724213307395)
                ·
                  refine ⟨3398586503236086319961093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265724335490724213307395 3398586503236086319961093)
                  ·
                    refine ⟨637234969356766184992705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398586503236086319961093 637234969356766184992705)
                    ·
                      refine ⟨477926227017574638744529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637234969356766184992705 477926227017574638744529)
                      ·
                        rfl

theorem cell23_930758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_930758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930758 prefixEnd_930758 := by exact prefixLift 930758
  have htrace : WordTrace (prefixWord ++ tailWord_930758) baseStart_930758 baseEnd_930758 := by
    simpa [prefixWord, tailWord_930758, baseEnd_930758] using wordTrace_append hprefix tailTrace_930758
  have hstable : (prefixWord ++ tailWord_930758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930758).length < 2 ^ (prefixWord ++ tailWord_930758).sum := by decide
  have hdescent : baseEnd_930758 < baseStart_930758 := by decide
  rcases family_descends (prefixWord ++ tailWord_930758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930766 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_930766 : Nat := 118140960795 + 930766 * 2 ^ 59
def prefixEnd_930766 : Nat := 4983230072969 + 3 ^ 40 * 930766 * 2
def baseEnd_930766 : Nat := 477930334862810607444491

theorem tailTrace_930766 : CollatzResearch.WordTrace tailWord_930766 prefixEnd_930766 477930334862810607444491 := by
  unfold tailWord_930766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243478118250152377785519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22631883297334146014856101 4243478118250152377785519)
  ·
    refine ⟨6365217177375228566678279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4243478118250152377785519 6365217177375228566678279)
    ·
      refine ⟨9547825766062842850017419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365217177375228566678279 9547825766062842850017419)
      ·
        refine ⟨14321738649094264275026129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547825766062842850017419 14321738649094264275026129)
        ·
          refine ⟨10741303986820698206269597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14321738649094264275026129 10741303986820698206269597)
          ·
            refine ⟨4027988995057761827351099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10741303986820698206269597 4027988995057761827351099)
            ·
              refine ⟨6041983492586642741026649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027988995057761827351099 6041983492586642741026649)
              ·
                refine ⟨4531487619439982055769987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041983492586642741026649 4531487619439982055769987)
                ·
                  refine ⟨6797231429159973083654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531487619439982055769987 6797231429159973083654981)
                  ·
                    refine ⟨1274480892967494953185309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797231429159973083654981 1274480892967494953185309)
                    ·
                      refine ⟨477930334862810607444491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274480892967494953185309 477930334862810607444491)
                      ·
                        rfl

theorem cell23_930766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_930766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930766 prefixEnd_930766 := by exact prefixLift 930766
  have htrace : WordTrace (prefixWord ++ tailWord_930766) baseStart_930766 baseEnd_930766 := by
    simpa [prefixWord, tailWord_930766, baseEnd_930766] using wordTrace_append hprefix tailTrace_930766
  have hstable : (prefixWord ++ tailWord_930766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930766).length < 2 ^ (prefixWord ++ tailWord_930766).sum := by decide
  have hdescent : baseEnd_930766 < baseStart_930766 := by decide
  rcases family_descends (prefixWord ++ tailWord_930766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930819 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_930819 : Nat := 118140960795 + 930819 * 2 ^ 59
def prefixEnd_930819 : Nat := 4983230072969 + 3 ^ 40 * 930819 * 2
def baseEnd_930819 : Nat := 477957549337498900081747

theorem tailTrace_930819 : CollatzResearch.WordTrace tailWord_930819 prefixEnd_930819 477957549337498900081747 := by
  unfold tailWord_930819
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949758014809209073963511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22633172009872806049309007 33949758014809209073963511)
  ·
    refine ⟨50924637022213813610945267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33949758014809209073963511 50924637022213813610945267)
    ·
      refine ⟨76386955533320720416417901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50924637022213813610945267 76386955533320720416417901)
      ·
        refine ⟨28645108324995270156156713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76386955533320720416417901 28645108324995270156156713)
        ·
          refine ⟨21483831243746452617117535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28645108324995270156156713 21483831243746452617117535)
          ·
            refine ⟨32225746865619678925676303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21483831243746452617117535 32225746865619678925676303)
            ·
              refine ⟨48338620298429518388514455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32225746865619678925676303 48338620298429518388514455)
              ·
                refine ⟨72507930447644277582771683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48338620298429518388514455 72507930447644277582771683)
                ·
                  refine ⟨108761895671466416374157525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72507930447644277582771683 108761895671466416374157525)
                  ·
                    refine ⟨2549106929799994133769317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108761895671466416374157525 2549106929799994133769317)
                    ·
                      refine ⟨477957549337498900081747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2549106929799994133769317 477957549337498900081747)
                      ·
                        rfl

theorem cell23_930819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_930819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930819 prefixEnd_930819 := by exact prefixLift 930819
  have htrace : WordTrace (prefixWord ++ tailWord_930819) baseStart_930819 baseEnd_930819 := by
    simpa [prefixWord, tailWord_930819, baseEnd_930819] using wordTrace_append hprefix tailTrace_930819
  have hstable : (prefixWord ++ tailWord_930819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930819).length < 2 ^ (prefixWord ++ tailWord_930819).sum := by decide
  have hdescent : baseEnd_930819 < baseStart_930819 := by decide
  rcases family_descends (prefixWord ++ tailWord_930819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930823 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_930823 : Nat := 118140960795 + 930823 * 2 ^ 59
def prefixEnd_930823 : Nat := 4983230072969 + 3 ^ 40 * 930823 * 2
def baseEnd_930823 : Nat := 477959603260116884431729

theorem tailTrace_930823 : CollatzResearch.WordTrace tailWord_930823 prefixEnd_930823 477959603260116884431729 := by
  unfold tailWord_930823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949903906794717757109123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22633269271196478504739415 33949903906794717757109123)
  ·
    refine ⟨50924855860192076635663685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33949903906794717757109123 50924855860192076635663685)
    ·
      refine ⟨9548410473786014369186941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50924855860192076635663685 9548410473786014369186941)
      ·
        refine ⟨3580653927669755388445103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9548410473786014369186941 3580653927669755388445103)
        ·
          refine ⟨5370980891504633082667655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580653927669755388445103 5370980891504633082667655)
          ·
            refine ⟨8056471337256949624001483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370980891504633082667655 8056471337256949624001483)
            ·
              refine ⟨12084707005885424436002225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056471337256949624001483 12084707005885424436002225)
              ·
                refine ⟨9063530254414068327001669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084707005885424436002225 9063530254414068327001669)
                ·
                  refine ⟨1699411922702637811312813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9063530254414068327001669 1699411922702637811312813)
                  ·
                    refine ⟨637279471013489179242305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699411922702637811312813 637279471013489179242305)
                    ·
                      refine ⟨477959603260116884431729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637279471013489179242305 477959603260116884431729)
                      ·
                        rfl

theorem cell23_930823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_930823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930823 prefixEnd_930823 := by exact prefixLift 930823
  have htrace : WordTrace (prefixWord ++ tailWord_930823) baseStart_930823 baseEnd_930823 := by
    simpa [prefixWord, tailWord_930823, baseEnd_930823] using wordTrace_append hprefix tailTrace_930823
  have hstable : (prefixWord ++ tailWord_930823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930823).length < 2 ^ (prefixWord ++ tailWord_930823).sum := by decide
  have hdescent : baseEnd_930823 < baseStart_930823 := by decide
  rcases family_descends (prefixWord ++ tailWord_930823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930834 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_930834 : Nat := 118140960795 + 930834 * 2 ^ 59
def prefixEnd_930834 : Nat := 4983230072969 + 3 ^ 40 * 930834 * 2
def baseEnd_930834 : Nat := 477965251547316341394179

theorem tailTrace_930834 : CollatzResearch.WordTrace tailWord_930834 prefixEnd_930834 477965251547316341394179 := by
  unfold tailWord_930834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487576277438716658939889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22633536739836577757173037 8487576277438716658939889)
  ·
    refine ⟨6365682208079037494204917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8487576277438716658939889 6365682208079037494204917)
    ·
      refine ⟨596782707007409765081711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6365682208079037494204917 596782707007409765081711)
      ·
        refine ⟨895174060511114647622567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596782707007409765081711 895174060511114647622567)
        ·
          refine ⟨1342761090766671971433851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895174060511114647622567 1342761090766671971433851)
          ·
            refine ⟨2014141636150007957150777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342761090766671971433851 2014141636150007957150777)
            ·
              refine ⟨1510606227112505967863083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014141636150007957150777 1510606227112505967863083)
              ·
                refine ⟨2265909340668758951794625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510606227112505967863083 2265909340668758951794625)
                ·
                  refine ⟨1699432005501569213845969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2265909340668758951794625 1699432005501569213845969)
                  ·
                    refine ⟨1274574004126176910384477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699432005501569213845969 1274574004126176910384477)
                    ·
                      refine ⟨477965251547316341394179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274574004126176910384477 477965251547316341394179)
                      ·
                        rfl

theorem cell23_930834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_930834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930834 prefixEnd_930834 := by exact prefixLift 930834
  have htrace : WordTrace (prefixWord ++ tailWord_930834) baseStart_930834 baseEnd_930834 := by
    simpa [prefixWord, tailWord_930834, baseEnd_930834] using wordTrace_append hprefix tailTrace_930834
  have hstable : (prefixWord ++ tailWord_930834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930834).length < 2 ^ (prefixWord ++ tailWord_930834).sum := by decide
  have hdescent : baseEnd_930834 < baseStart_930834 := by decide
  rcases family_descends (prefixWord ++ tailWord_930834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930840 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_930840 : Nat := 118140960795 + 930840 * 2 ^ 59
def prefixEnd_930840 : Nat := 4983230072969 + 3 ^ 40 * 930840 * 2
def baseEnd_930840 : Nat := 477968332431243317919151

theorem tailTrace_930840 : CollatzResearch.WordTrace tailWord_930840 prefixEnd_930840 477968332431243317919151 := by
  unfold tailWord_930840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975261973866564830238987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22633682631822086440318649 16975261973866564830238987)
  ·
    refine ⟨25462892960799847245358481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16975261973866564830238987 25462892960799847245358481)
    ·
      refine ⟨19097169720599885434018861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25462892960799847245358481 19097169720599885434018861)
      ·
        refine ⟨7161438645224957037757073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19097169720599885434018861 7161438645224957037757073)
        ·
          refine ⟨5371078983918717778317805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7161438645224957037757073 5371078983918717778317805)
          ·
            refine ⟨2014154618969519166869177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5371078983918717778317805 2014154618969519166869177)
            ·
              refine ⟨1510615964227139375151883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014154618969519166869177 1510615964227139375151883)
              ·
                refine ⟨2265923946340709062727825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510615964227139375151883 2265923946340709062727825)
                ·
                  refine ⟨1699442959755531797045869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2265923946340709062727825 1699442959755531797045869)
                  ·
                    refine ⟨637291109908324423892201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699442959755531797045869 637291109908324423892201)
                    ·
                      refine ⟨477968332431243317919151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637291109908324423892201 477968332431243317919151)
                      ·
                        rfl

theorem cell23_930840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_930840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930840 prefixEnd_930840 := by exact prefixLift 930840
  have htrace : WordTrace (prefixWord ++ tailWord_930840) baseStart_930840 baseEnd_930840 := by
    simpa [prefixWord, tailWord_930840, baseEnd_930840] using wordTrace_append hprefix tailTrace_930840
  have hstable : (prefixWord ++ tailWord_930840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930840).length < 2 ^ (prefixWord ++ tailWord_930840).sum := by decide
  have hdescent : baseEnd_930840 < baseStart_930840 := by decide
  rcases family_descends (prefixWord ++ tailWord_930840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930850 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_930850 : Nat := 118140960795 + 930850 * 2 ^ 59
def prefixEnd_930850 : Nat := 4983230072969 + 3 ^ 40 * 930850 * 2
def baseEnd_930850 : Nat := 159324489079262759598035

theorem tailTrace_930850 : CollatzResearch.WordTrace tailWord_930850 prefixEnd_930850 159324489079262759598035 := by
  unfold tailWord_930850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487722169424225342085501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22633925785131267578894669 8487722169424225342085501)
  ·
    refine ⟨3182895813534084503282063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8487722169424225342085501 3182895813534084503282063)
    ·
      refine ⟨4774343720301126754923095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182895813534084503282063 4774343720301126754923095)
      ·
        refine ⟨7161515580451690132384643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774343720301126754923095 7161515580451690132384643)
        ·
          refine ⟨10742273370677535198576965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161515580451690132384643 10742273370677535198576965)
          ·
            refine ⟨2014176257002037849733181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10742273370677535198576965 2014176257002037849733181)
            ·
              refine ⟨755316096375764193649943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2014176257002037849733181 755316096375764193649943)
              ·
                refine ⟨1132974144563646290474915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755316096375764193649943 1132974144563646290474915)
                ·
                  refine ⟨1699461216845469435712373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132974144563646290474915 1699461216845469435712373)
                  ·
                    refine ⟨159324489079262759598035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1699461216845469435712373 159324489079262759598035)
                    ·
                      rfl

theorem cell23_930850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_930850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930850 prefixEnd_930850 := by exact prefixLift 930850
  have htrace : WordTrace (prefixWord ++ tailWord_930850) baseStart_930850 baseEnd_930850 := by
    simpa [prefixWord, tailWord_930850, baseEnd_930850] using wordTrace_append hprefix tailTrace_930850
  have hstable : (prefixWord ++ tailWord_930850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930850).length < 2 ^ (prefixWord ++ tailWord_930850).sum := by decide
  have hdescent : baseEnd_930850 < baseStart_930850 := by decide
  rcases family_descends (prefixWord ++ tailWord_930850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930866 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_930866 : Nat := 118140960795 + 930866 * 2 ^ 59
def prefixEnd_930866 : Nat := 4983230072969 + 3 ^ 40 * 930866 * 2
def baseEnd_930866 : Nat := 477981682928260216194031

theorem tailTrace_930866 : CollatzResearch.WordTrace tailWord_930866 prefixEnd_930866 477981682928260216194031 := by
  unfold tailWord_930866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487868061409734025231113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22634314830425957400616301 8487868061409734025231113)
  ·
    refine ⟨6365901046057300518923335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8487868061409734025231113 6365901046057300518923335)
    ·
      refine ⟨9548851569085950778385003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365901046057300518923335 9548851569085950778385003)
      ·
        refine ⟨14323277353628926167577505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548851569085950778385003 14323277353628926167577505)
        ·
          refine ⟨10742458015221694625683129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323277353628926167577505 10742458015221694625683129)
          ·
            refine ⟨8056843511416270969262347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10742458015221694625683129 8056843511416270969262347)
            ·
              refine ⟨12085265267124406453893521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056843511416270969262347 12085265267124406453893521)
              ·
                refine ⟨9063948950343304840420141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085265267124406453893521 9063948950343304840420141)
                ·
                  refine ⟨3398980856378739315157553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9063948950343304840420141 3398980856378739315157553)
                  ·
                    refine ⟨2549235642284054486368165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398980856378739315157553 2549235642284054486368165)
                    ·
                      refine ⟨477981682928260216194031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2549235642284054486368165 477981682928260216194031)
                      ·
                        rfl

theorem cell23_930866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_930866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930866 prefixEnd_930866 := by exact prefixLift 930866
  have htrace : WordTrace (prefixWord ++ tailWord_930866) baseStart_930866 baseEnd_930866 := by
    simpa [prefixWord, tailWord_930866, baseEnd_930866] using wordTrace_append hprefix tailTrace_930866
  have hstable : (prefixWord ++ tailWord_930866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930866).length < 2 ^ (prefixWord ++ tailWord_930866).sum := by decide
  have hdescent : baseEnd_930866 < baseStart_930866 := by decide
  rcases family_descends (prefixWord ++ tailWord_930866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930873 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_930873 : Nat := 118140960795 + 930873 * 2 ^ 59
def prefixEnd_930873 : Nat := 4983230072969 + 3 ^ 40 * 930873 * 2
def baseEnd_930873 : Nat := 477985277292841688806499

theorem tailTrace_930873 : CollatzResearch.WordTrace tailWord_930873 prefixEnd_930873 477985277292841688806499 := by
  unfold tailWord_930873
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951727556613576296429273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22634485037742384197619515 33951727556613576296429273)
  ·
    refine ⟨25463795667460182222321955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33951727556613576296429273 25463795667460182222321955)
    ·
      refine ⟨38195693501190273333482933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25463795667460182222321955 38195693501190273333482933)
      ·
        refine ⟨3580846265736588125014025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38195693501190273333482933 3580846265736588125014025)
        ·
          refine ⟨2685634699302441093760519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580846265736588125014025 2685634699302441093760519)
          ·
            refine ⟨4028452048953661640640779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685634699302441093760519 4028452048953661640640779)
            ·
              refine ⟨6042678073430492460961169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028452048953661640640779 6042678073430492460961169)
              ·
                refine ⟨4532008555072869345720877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042678073430492460961169 4532008555072869345720877)
                ·
                  refine ⟨1699503208152326004645329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4532008555072869345720877 1699503208152326004645329)
                  ·
                    refine ⟨1274627406114244503483997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699503208152326004645329 1274627406114244503483997)
                    ·
                      refine ⟨477985277292841688806499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274627406114244503483997 477985277292841688806499)
                      ·
                        rfl

theorem cell23_930873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_930873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930873 prefixEnd_930873 := by exact prefixLift 930873
  have htrace : WordTrace (prefixWord ++ tailWord_930873) baseStart_930873 baseEnd_930873 := by
    simpa [prefixWord, tailWord_930873, baseEnd_930873] using wordTrace_append hprefix tailTrace_930873
  have hstable : (prefixWord ++ tailWord_930873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930873).length < 2 ^ (prefixWord ++ tailWord_930873).sum := by decide
  have hdescent : baseEnd_930873 < baseStart_930873 := by decide
  rcases family_descends (prefixWord ++ tailWord_930873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930876 : List Nat := [2, 2, 2, 2, 2, 2, 3, 8]
def baseStart_930876 : Nat := 118140960795 + 930876 * 2 ^ 59
def prefixEnd_930876 : Nat := 4983230072969 + 3 ^ 40 * 930876 * 2
def baseEnd_930876 : Nat := 17703215471659451002555

theorem tailTrace_930876 : CollatzResearch.WordTrace tailWord_930876 prefixEnd_930876 17703215471659451002555 := by
  unfold tailWord_930876
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975918487801353904394241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22634557983735138539192321 16975918487801353904394241)
  ·
    refine ⟨12731938865851015428295681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16975918487801353904394241 12731938865851015428295681)
    ·
      refine ⟨9548954149388261571221761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12731938865851015428295681 9548954149388261571221761)
      ·
        refine ⟨7161715612041196178416321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9548954149388261571221761 7161715612041196178416321)
        ·
          refine ⟨5371286709030897133812241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7161715612041196178416321 5371286709030897133812241)
          ·
            refine ⟨4028465031773172850359181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371286709030897133812241 4028465031773172850359181)
            ·
              refine ⟨1510674386914939818884693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028465031773172850359181 1510674386914939818884693)
              ·
                refine ⟨17703215471659451002555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1510674386914939818884693 17703215471659451002555)
                ·
                  rfl

theorem cell23_930876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 8].length) (baseStart_930876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930876 prefixEnd_930876 := by exact prefixLift 930876
  have htrace : WordTrace (prefixWord ++ tailWord_930876) baseStart_930876 baseEnd_930876 := by
    simpa [prefixWord, tailWord_930876, baseEnd_930876] using wordTrace_append hprefix tailTrace_930876
  have hstable : (prefixWord ++ tailWord_930876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930876).length < 2 ^ (prefixWord ++ tailWord_930876).sum := by decide
  have hdescent : baseEnd_930876 < baseStart_930876 := by decide
  rcases family_descends (prefixWord ++ tailWord_930876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930903 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_930903 : Nat := 118140960795 + 930903 * 2 ^ 59
def prefixEnd_930903 : Nat := 4983230072969 + 3 ^ 40 * 930903 * 2
def baseEnd_930903 : Nat := 478000681712476571431361

theorem tailTrace_930903 : CollatzResearch.WordTrace tailWord_930903 prefixEnd_930903 478000681712476571431361 := by
  unfold tailWord_930903
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952821746504891420021363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22635214497669927613347575 33952821746504891420021363)
  ·
    refine ⟨50929232619757337130032045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33952821746504891420021363 50929232619757337130032045)
    ·
      refine ⟨19098462232409001423762017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50929232619757337130032045 19098462232409001423762017)
      ·
        refine ⟨14323846674306751067821513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19098462232409001423762017 14323846674306751067821513)
        ·
          refine ⟨10742885005730063300866135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323846674306751067821513 10742885005730063300866135)
          ·
            refine ⟨16114327508595094951299203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742885005730063300866135 16114327508595094951299203)
            ·
              refine ⟨24171491262892642426948805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114327508595094951299203 24171491262892642426948805)
              ·
                refine ⟨4532154611792370455052901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24171491262892642426948805 4532154611792370455052901)
                ·
                  refine ⟨849778989711069460322419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4532154611792370455052901 849778989711069460322419)
                  ·
                    refine ⟨1274668484566604190483629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849778989711069460322419 1274668484566604190483629)
                    ·
                      refine ⟨478000681712476571431361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274668484566604190483629 478000681712476571431361)
                      ·
                        rfl

theorem cell23_930903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_930903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930903 prefixEnd_930903 := by exact prefixLift 930903
  have htrace : WordTrace (prefixWord ++ tailWord_930903) baseStart_930903 baseEnd_930903 := by
    simpa [prefixWord, tailWord_930903, baseEnd_930903] using wordTrace_append hprefix tailTrace_930903
  have hstable : (prefixWord ++ tailWord_930903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930903).length < 2 ^ (prefixWord ++ tailWord_930903).sum := by decide
  have hdescent : baseEnd_930903 < baseStart_930903 := by decide
  rcases family_descends (prefixWord ++ tailWord_930903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930910 : List Nat := [4, 4, 1, 1, 1, 2, 10]
def baseStart_930910 : Nat := 118140960795 + 930910 * 2 ^ 59
def prefixEnd_930910 : Nat := 4983230072969 + 3 ^ 40 * 930910 * 2
def baseEnd_930910 : Nat := 5901287358976025235109

theorem tailTrace_930910 : CollatzResearch.WordTrace tailWord_930910 prefixEnd_930910 5901287358976025235109 := by
  unfold tailWord_930910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244134632184941451940773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22635384704986354410350789 4244134632184941451940773)
  ·
    refine ⟨795775243534676522238895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4244134632184941451940773 795775243534676522238895)
    ·
      refine ⟨1193662865302014783358343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795775243534676522238895 1193662865302014783358343)
      ·
        refine ⟨1790494297953022175037515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193662865302014783358343 1790494297953022175037515)
        ·
          refine ⟨2685741446929533262556273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790494297953022175037515 2685741446929533262556273)
          ·
            refine ⟨2014306085197149946917205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685741446929533262556273 2014306085197149946917205)
            ·
              refine ⟨5901287358976025235109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2014306085197149946917205 5901287358976025235109)
              ·
                rfl

theorem cell23_930910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 10].length) (baseStart_930910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930910 prefixEnd_930910 := by exact prefixLift 930910
  have htrace : WordTrace (prefixWord ++ tailWord_930910) baseStart_930910 baseEnd_930910 := by
    simpa [prefixWord, tailWord_930910, baseEnd_930910] using wordTrace_append hprefix tailTrace_930910
  have hstable : (prefixWord ++ tailWord_930910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930910).length < 2 ^ (prefixWord ++ tailWord_930910).sum := by decide
  have hdescent : baseEnd_930910 < baseStart_930910 := by decide
  rcases family_descends (prefixWord ++ tailWord_930910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930936 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_930936 : Nat := 118140960795 + 930936 * 2 ^ 59
def prefixEnd_930936 : Nat := 4983230072969 + 3 ^ 40 * 930936 * 2
def baseEnd_930936 : Nat := 159339208858024980772903

theorem tailTrace_930936 : CollatzResearch.WordTrace tailWord_930936 prefixEnd_930936 159339208858024980772903 := by
  unfold tailWord_930936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977012677692669027986331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22636016903590225370648441 16977012677692669027986331)
  ·
    refine ⟨25465519016539003541979497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16977012677692669027986331 25465519016539003541979497)
    ·
      refine ⟨19099139262404252656484623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25465519016539003541979497 19099139262404252656484623)
      ·
        refine ⟨28648708893606378984726935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19099139262404252656484623 28648708893606378984726935)
        ·
          refine ⟨42973063340409568477090403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648708893606378984726935 42973063340409568477090403)
          ·
            refine ⟨64459595010614352715635605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42973063340409568477090403 64459595010614352715635605)
            ·
              refine ⟨3021543516122547783545419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64459595010614352715635605 3021543516122547783545419)
              ·
                refine ⟨4532315274183821675318129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021543516122547783545419 4532315274183821675318129)
                ·
                  refine ⟨3399236455637866256488597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4532315274183821675318129 3399236455637866256488597)
                  ·
                    refine ⟨159339208858024980772903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3399236455637866256488597 159339208858024980772903)
                    ·
                      rfl

theorem cell23_930936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_930936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930936 prefixEnd_930936 := by exact prefixLift 930936
  have htrace : WordTrace (prefixWord ++ tailWord_930936) baseStart_930936 baseEnd_930936 := by
    simpa [prefixWord, tailWord_930936, baseEnd_930936] using wordTrace_append hprefix tailTrace_930936
  have hstable : (prefixWord ++ tailWord_930936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930936).length < 2 ^ (prefixWord ++ tailWord_930936).sum := by decide
  have hdescent : baseEnd_930936 < baseStart_930936 := by decide
  rcases family_descends (prefixWord ++ tailWord_930936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930937 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 3, 3]
def baseStart_930937 : Nat := 118140960795 + 930937 * 2 ^ 59
def prefixEnd_930937 : Nat := 4983230072969 + 3 ^ 40 * 930937 * 2
def baseEnd_930937 : Nat := 478018140054729438406205

theorem tailTrace_930937 : CollatzResearch.WordTrace tailWord_930937 prefixEnd_930937 478018140054729438406205 := by
  unfold tailWord_930937
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954061828381715226759065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22636041218921143484506043 33954061828381715226759065)
  ·
    refine ⟨25465546371286286420069299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33954061828381715226759065 25465546371286286420069299)
    ·
      refine ⟨38198319556929429630103949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25465546371286286420069299 38198319556929429630103949)
      ·
        refine ⟨14324369833848536111288981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38198319556929429630103949 14324369833848536111288981)
        ·
          refine ⟨671454835961650130216671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14324369833848536111288981 671454835961650130216671)
          ·
            refine ⟨1007182253942475195325007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671454835961650130216671 1007182253942475195325007)
            ·
              refine ⟨1510773380913712792987511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007182253942475195325007 1510773380913712792987511)
              ·
                refine ⟨2266160071370569189481267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510773380913712792987511 2266160071370569189481267)
                ·
                  refine ⟨3399240107055853784221901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266160071370569189481267 3399240107055853784221901)
                  ·
                    refine ⟨1274715040145945169083213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399240107055853784221901 1274715040145945169083213)
                    ·
                      refine ⟨478018140054729438406205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1274715040145945169083213 478018140054729438406205)
                      ·
                        rfl

theorem cell23_930937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_930937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930937 prefixEnd_930937 := by exact prefixLift 930937
  have htrace : WordTrace (prefixWord ++ tailWord_930937) baseStart_930937 baseEnd_930937 := by
    simpa [prefixWord, tailWord_930937, baseEnd_930937] using wordTrace_append hprefix tailTrace_930937
  have hstable : (prefixWord ++ tailWord_930937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930937).length < 2 ^ (prefixWord ++ tailWord_930937).sum := by decide
  have hdescent : baseEnd_930937 < baseStart_930937 := by decide
  rcases family_descends (prefixWord ++ tailWord_930937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930956 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_930956 : Nat := 118140960795 + 930956 * 2 ^ 59
def prefixEnd_930956 : Nat := 4983230072969 + 3 ^ 40 * 930956 * 2
def baseEnd_930956 : Nat := 478027896187164864068617

theorem tailTrace_930956 : CollatzResearch.WordTrace tailWord_930956 prefixEnd_930956 478027896187164864068617 := by
  unfold tailWord_930956
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977377407656440735850361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22636503210208587647800481 16977377407656440735850361)
  ·
    refine ⟨12733033055742330551887771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16977377407656440735850361 12733033055742330551887771)
    ·
      refine ⟨19099549583613495827831657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12733033055742330551887771 19099549583613495827831657)
      ·
        refine ⟨14324662187710121870873743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19099549583613495827831657 14324662187710121870873743)
        ·
          refine ⟨21486993281565182806310615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14324662187710121870873743 21486993281565182806310615)
          ·
            refine ⟨32230489922347774209465923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21486993281565182806310615 32230489922347774209465923)
            ·
              refine ⟨48345734883521661314198885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32230489922347774209465923 48345734883521661314198885)
              ·
                refine ⟨9064825290660311496412291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48345734883521661314198885 9064825290660311496412291)
                ·
                  refine ⟨13597237935990467244618437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064825290660311496412291 13597237935990467244618437)
                  ·
                    refine ⟨2549482112998212608365957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13597237935990467244618437 2549482112998212608365957)
                    ·
                      refine ⟨478027896187164864068617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2549482112998212608365957 478027896187164864068617)
                      ·
                        rfl

theorem cell23_930956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_930956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930956 prefixEnd_930956 := by exact prefixLift 930956
  have htrace : WordTrace (prefixWord ++ tailWord_930956) baseStart_930956 baseEnd_930956 := by
    simpa [prefixWord, tailWord_930956, baseEnd_930956] using wordTrace_append hprefix tailTrace_930956
  have hstable : (prefixWord ++ tailWord_930956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930956).length < 2 ^ (prefixWord ++ tailWord_930956).sum := by decide
  have hdescent : baseEnd_930956 < baseStart_930956 := by decide
  rcases family_descends (prefixWord ++ tailWord_930956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930976 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_930976 : Nat := 118140960795 + 930976 * 2 ^ 59
def prefixEnd_930976 : Nat := 4983230072969 + 3 ^ 40 * 930976 * 2
def baseEnd_930976 : Nat := 478038165800254785818525

theorem tailTrace_930976 : CollatzResearch.WordTrace tailWord_930976 prefixEnd_930976 478038165800254785818525 := by
  unfold tailWord_930976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977742137620212443714391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22636989516826949924952521 16977742137620212443714391)
  ·
    refine ⟨25466613206430318665571587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16977742137620212443714391 25466613206430318665571587)
    ·
      refine ⟨38199919809645477998357381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25466613206430318665571587 38199919809645477998357381)
      ·
        refine ⟨7162484964308527124692009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38199919809645477998357381 7162484964308527124692009)
        ·
          refine ⟨5371863723231395343519007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7162484964308527124692009 5371863723231395343519007)
          ·
            refine ⟨8057795584847093015278511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371863723231395343519007 8057795584847093015278511)
            ·
              refine ⟨12086693377270639522917767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057795584847093015278511 12086693377270639522917767)
              ·
                refine ⟨18130040065905959284376651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12086693377270639522917767 18130040065905959284376651)
                ·
                  refine ⟨27195060098858938926564977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18130040065905959284376651 27195060098858938926564977)
                  ·
                    refine ⟨20396295074144204194923733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27195060098858938926564977 20396295074144204194923733)
                    ·
                      refine ⟨478038165800254785818525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20396295074144204194923733 478038165800254785818525)
                      ·
                        rfl

theorem cell23_930976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_930976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930976 prefixEnd_930976 := by exact prefixLift 930976
  have htrace : WordTrace (prefixWord ++ tailWord_930976) baseStart_930976 baseEnd_930976 := by
    simpa [prefixWord, tailWord_930976, baseEnd_930976] using wordTrace_append hprefix tailTrace_930976
  have hstable : (prefixWord ++ tailWord_930976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930976).length < 2 ^ (prefixWord ++ tailWord_930976).sum := by decide
  have hdescent : baseEnd_930976 < baseStart_930976 := by decide
  rcases family_descends (prefixWord ++ tailWord_930976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930977 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_930977 : Nat := 118140960795 + 930977 * 2 ^ 59
def prefixEnd_930977 : Nat := 4983230072969 + 3 ^ 40 * 930977 * 2
def baseEnd_930977 : Nat := 478038679280909281906021

theorem tailTrace_930977 : CollatzResearch.WordTrace tailWord_930977 prefixEnd_930977 478038679280909281906021 := by
  unfold tailWord_930977
  simp only [CollatzResearch.WordTrace]
  refine ⟨33955520748236802058215185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22637013832157868038810123 33955520748236802058215185)
  ·
    refine ⟨25466640561177601543661389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33955520748236802058215185 25466640561177601543661389)
    ·
      refine ⟨9549990210441600578873021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25466640561177601543661389 9549990210441600578873021)
      ·
        refine ⟨3581246328915600217077383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9549990210441600578873021 3581246328915600217077383)
        ·
          refine ⟨5371869493373400325616075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581246328915600217077383 5371869493373400325616075)
          ·
            refine ⟨8057804240060100488424113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371869493373400325616075 8057804240060100488424113)
            ·
              refine ⟨6043353180045075366318085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8057804240060100488424113 6043353180045075366318085)
              ·
                refine ⟨1133128721258451631184641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6043353180045075366318085 1133128721258451631184641)
                ·
                  refine ⟨849846540943838723388481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133128721258451631184641 849846540943838723388481)
                  ·
                    refine ⟨637384905707879042541361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849846540943838723388481 637384905707879042541361)
                    ·
                      refine ⟨478038679280909281906021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637384905707879042541361 478038679280909281906021)
                      ·
                        rfl

theorem cell23_930977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_930977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930977 prefixEnd_930977 := by exact prefixLift 930977
  have htrace : WordTrace (prefixWord ++ tailWord_930977) baseStart_930977 baseEnd_930977 := by
    simpa [prefixWord, tailWord_930977, baseEnd_930977] using wordTrace_append hprefix tailTrace_930977
  have hstable : (prefixWord ++ tailWord_930977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930977).length < 2 ^ (prefixWord ++ tailWord_930977).sum := by decide
  have hdescent : baseEnd_930977 < baseStart_930977 := by decide
  rcases family_descends (prefixWord ++ tailWord_930977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930994 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_930994 : Nat := 118140960795 + 930994 * 2 ^ 59
def prefixEnd_930994 : Nat := 4983230072969 + 3 ^ 40 * 930994 * 2
def baseEnd_930994 : Nat := 478047408452035715393443

theorem tailTrace_930994 : CollatzResearch.WordTrace tailWord_930994 prefixEnd_930994 478047408452035715393443 := by
  unfold tailWord_930994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489035197293803490396009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22637427192783475974389357 8489035197293803490396009)
  ·
    refine ⟨6366776397970352617797007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8489035197293803490396009 6366776397970352617797007)
    ·
      refine ⟨9550164596955528926695511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6366776397970352617797007 9550164596955528926695511)
      ·
        refine ⟨14325246895433293390043267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9550164596955528926695511 14325246895433293390043267)
        ·
          refine ⟨21487870343149940085064901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325246895433293390043267 21487870343149940085064901)
          ·
            refine ⟨4028975689340613765949669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21487870343149940085064901 4028975689340613765949669)
            ·
              refine ⟨755432941751365081115563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4028975689340613765949669 755432941751365081115563)
              ·
                refine ⟨1133149412627047621673345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755432941751365081115563 1133149412627047621673345)
                ·
                  refine ⟨849862059470285716255009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133149412627047621673345 849862059470285716255009)
                  ·
                    refine ⟨637396544602714287191257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849862059470285716255009 637396544602714287191257)
                    ·
                      refine ⟨478047408452035715393443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637396544602714287191257 478047408452035715393443)
                      ·
                        rfl

theorem cell23_930994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_930994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930994 prefixEnd_930994 := by exact prefixLift 930994
  have htrace : WordTrace (prefixWord ++ tailWord_930994) baseStart_930994 baseEnd_930994 := by
    simpa [prefixWord, tailWord_930994, baseEnd_930994] using wordTrace_append hprefix tailTrace_930994
  have hstable : (prefixWord ++ tailWord_930994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930994).length < 2 ^ (prefixWord ++ tailWord_930994).sum := by decide
  have hdescent : baseEnd_930994 < baseStart_930994 := by decide
  rcases family_descends (prefixWord ++ tailWord_930994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930998 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_930998 : Nat := 118140960795 + 930998 * 2 ^ 59
def prefixEnd_930998 : Nat := 4983230072969 + 3 ^ 40 * 930998 * 2
def baseEnd_930998 : Nat := 478049462374653699743425

theorem tailTrace_930998 : CollatzResearch.WordTrace tailWord_930998 prefixEnd_930998 478049462374653699743425 := by
  unfold tailWord_930998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122267917572545165295603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22637524454107148429819765 2122267917572545165295603)
  ·
    refine ⟨3183401876358817747943405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122267917572545165295603 3183401876358817747943405)
    ·
      refine ⟨1193775703634556655478777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3183401876358817747943405 1193775703634556655478777)
      ·
        refine ⟨895331777725917491609083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193775703634556655478777 895331777725917491609083)
        ·
          refine ⟨1342997666588876237413625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895331777725917491609083 1342997666588876237413625)
          ·
            refine ⟨1007248249941657178060219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342997666588876237413625 1007248249941657178060219)
            ·
              refine ⟨1510872374912485767090329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007248249941657178060219 1510872374912485767090329)
              ·
                refine ⟨1133154281184364325317747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510872374912485767090329 1133154281184364325317747)
                ·
                  refine ⟨1699731421776546487976621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133154281184364325317747 1699731421776546487976621)
                  ·
                    refine ⟨637399283166204932991233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699731421776546487976621 637399283166204932991233)
                    ·
                      refine ⟨478049462374653699743425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637399283166204932991233 478049462374653699743425)
                      ·
                        rfl

theorem cell23_930998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_930998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_930998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_930998 prefixEnd_930998 := by exact prefixLift 930998
  have htrace : WordTrace (prefixWord ++ tailWord_930998) baseStart_930998 baseEnd_930998 := by
    simpa [prefixWord, tailWord_930998, baseEnd_930998] using wordTrace_append hprefix tailTrace_930998
  have hstable : (prefixWord ++ tailWord_930998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930998).length < 2 ^ (prefixWord ++ tailWord_930998).sum := by decide
  have hdescent : baseEnd_930998 < baseStart_930998 := by decide
  rcases family_descends (prefixWord ++ tailWord_930998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931003 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 5, 2]
def baseStart_931003 : Nat := 118140960795 + 931003 * 2 ^ 59
def prefixEnd_931003 : Nat := 4983230072969 + 3 ^ 40 * 931003 * 2
def baseEnd_931003 : Nat := 478052029777926180180901

theorem tailTrace_931003 : CollatzResearch.WordTrace tailWord_931003 prefixEnd_931003 478052029777926180180901 := by
  unfold tailWord_931003
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956469046142608498661663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22637646030761738999107775 33956469046142608498661663)
  ·
    refine ⟨50934703569213912747992495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33956469046142608498661663 50934703569213912747992495)
    ·
      refine ⟨76402055353820869121988743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50934703569213912747992495 76402055353820869121988743)
      ·
        refine ⟨114603083030731303682983115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76402055353820869121988743 114603083030731303682983115)
        ·
          refine ⟨171904624546096955524474673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114603083030731303682983115 171904624546096955524474673)
          ·
            refine ⟨128928468409572716643356005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171904624546096955524474673 128928468409572716643356005)
            ·
              refine ⟨24174087826794884370629251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128928468409572716643356005 24174087826794884370629251)
              ·
                refine ⟨36261131740192326555943877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24174087826794884370629251 36261131740192326555943877)
                ·
                  refine ⟨6798962201286061229239477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36261131740192326555943877 6798962201286061229239477)
                  ·
                    refine ⟨637402706370568240241201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6798962201286061229239477 637402706370568240241201)
                    ·
                      refine ⟨478052029777926180180901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637402706370568240241201 478052029777926180180901)
                      ·
                        rfl

theorem cell23_931003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5, 2].length) (baseStart_931003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931003 prefixEnd_931003 := by exact prefixLift 931003
  have htrace : WordTrace (prefixWord ++ tailWord_931003) baseStart_931003 baseEnd_931003 := by
    simpa [prefixWord, tailWord_931003, baseEnd_931003] using wordTrace_append hprefix tailTrace_931003
  have hstable : (prefixWord ++ tailWord_931003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931003).length < 2 ^ (prefixWord ++ tailWord_931003).sum := by decide
  have hdescent : baseEnd_931003 < baseStart_931003 := by decide
  rcases family_descends (prefixWord ++ tailWord_931003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931050 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_931050 : Nat := 118140960795 + 931050 * 2 ^ 59
def prefixEnd_931050 : Nat := 4983230072969 + 3 ^ 40 * 931050 * 2
def baseEnd_931050 : Nat := 478076163368687496293185

theorem tailTrace_931050 : CollatzResearch.WordTrace tailWord_931050 prefixEnd_931050 478076163368687496293185 := by
  unfold tailWord_931050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489545819243083881405651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22638788851314890350415069 8489545819243083881405651)
  ·
    refine ⟨12734318728864625822108477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8489545819243083881405651 12734318728864625822108477)
    ·
      refine ⟨4775369523324234683290679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12734318728864625822108477 4775369523324234683290679)
      ·
        refine ⟨7163054284986352024936019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775369523324234683290679 7163054284986352024936019)
        ·
          refine ⟨10744581427479528037404029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163054284986352024936019 10744581427479528037404029)
          ·
            refine ⟨4029218035304823014026511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10744581427479528037404029 4029218035304823014026511)
            ·
              refine ⟨6043827052957234521039767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029218035304823014026511 6043827052957234521039767)
              ·
                refine ⟨9065740579435851781559651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043827052957234521039767 9065740579435851781559651)
                ·
                  refine ⟨13598610869153777672339477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9065740579435851781559651 13598610869153777672339477)
                  ·
                    refine ⟨637434884491583328390913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13598610869153777672339477 637434884491583328390913)
                    ·
                      refine ⟨478076163368687496293185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637434884491583328390913 478076163368687496293185)
                      ·
                        rfl

theorem cell23_931050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_931050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931050 prefixEnd_931050 := by exact prefixLift 931050
  have htrace : WordTrace (prefixWord ++ tailWord_931050) baseStart_931050 baseEnd_931050 := by
    simpa [prefixWord, tailWord_931050, baseEnd_931050] using wordTrace_append hprefix tailTrace_931050
  have hstable : (prefixWord ++ tailWord_931050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931050).length < 2 ^ (prefixWord ++ tailWord_931050).sum := by decide
  have hdescent : baseEnd_931050 < baseStart_931050 := by decide
  rcases family_descends (prefixWord ++ tailWord_931050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931056 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 12]
def baseStart_931056 : Nat := 118140960795 + 931056 * 2 ^ 59
def prefixEnd_931056 : Nat := 4983230072969 + 3 ^ 40 * 931056 * 2
def baseEnd_931056 : Nat := 53119916028068274757573

theorem tailTrace_931056 : CollatzResearch.WordTrace tailWord_931056 prefixEnd_931056 53119916028068274757573 := by
  unfold tailWord_931056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16979201057475299275170511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22638934743300399033560681 16979201057475299275170511)
  ·
    refine ⟨25468801586212948912755767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16979201057475299275170511 25468801586212948912755767)
    ·
      refine ⟨38203202379319423369133651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25468801586212948912755767 38203202379319423369133651)
      ·
        refine ⟨57304803568979135053700477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38203202379319423369133651 57304803568979135053700477)
        ·
          refine ⟨21489301338367175645137679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57304803568979135053700477 21489301338367175645137679)
          ·
            refine ⟨32233952007550763467706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21489301338367175645137679 32233952007550763467706519)
            ·
              refine ⟨48350928011326145201559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32233952007550763467706519 48350928011326145201559779)
              ·
                refine ⟨72526392016989217802339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48350928011326145201559779 72526392016989217802339669)
                ·
                  refine ⟨53119916028068274757573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 72526392016989217802339669 53119916028068274757573)
                  ·
                    rfl

theorem cell23_931056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_931056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931056 prefixEnd_931056 := by exact prefixLift 931056
  have htrace : WordTrace (prefixWord ++ tailWord_931056) baseStart_931056 baseEnd_931056 := by
    simpa [prefixWord, tailWord_931056, baseEnd_931056] using wordTrace_append hprefix tailTrace_931056
  have hstable : (prefixWord ++ tailWord_931056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931056).length < 2 ^ (prefixWord ++ tailWord_931056).sum := by decide
  have hdescent : baseEnd_931056 < baseStart_931056 := by decide
  rcases family_descends (prefixWord ++ tailWord_931056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931077 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_931077 : Nat := 118140960795 + 931077 * 2 ^ 59
def prefixEnd_931077 : Nat := 4983230072969 + 3 ^ 40 * 931077 * 2
def baseEnd_931077 : Nat := 159363342448786296885187

theorem tailTrace_931077 : CollatzResearch.WordTrace tailWord_931077 prefixEnd_931077 159363342448786296885187 := by
  unfold tailWord_931077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33959168047874519136855485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22639445365249679424570323 33959168047874519136855485)
  ·
    refine ⟨12734688017952944676320807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33959168047874519136855485 12734688017952944676320807)
    ·
      refine ⟨19102032026929417014481211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12734688017952944676320807 19102032026929417014481211)
      ·
        refine ⟨28653048040394125521721817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19102032026929417014481211 28653048040394125521721817)
        ·
          refine ⟨21489786030295594141291363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28653048040394125521721817 21489786030295594141291363)
          ·
            refine ⟨32234679045443391211937045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21489786030295594141291363 32234679045443391211937045)
            ·
              refine ⟨1511000580255158963059549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32234679045443391211937045 1511000580255158963059549)
              ·
                refine ⟨566625217595684611147331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511000580255158963059549 566625217595684611147331)
                ·
                  refine ⟨849937826393526916720997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566625217595684611147331 849937826393526916720997)
                  ·
                    refine ⟨159363342448786296885187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849937826393526916720997 159363342448786296885187)
                    ·
                      rfl

theorem cell23_931077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_931077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931077 prefixEnd_931077 := by exact prefixLift 931077
  have htrace : WordTrace (prefixWord ++ tailWord_931077) baseStart_931077 baseEnd_931077 := by
    simpa [prefixWord, tailWord_931077, baseEnd_931077] using wordTrace_append hprefix tailTrace_931077
  have hstable : (prefixWord ++ tailWord_931077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931077).length < 2 ^ (prefixWord ++ tailWord_931077).sum := by decide
  have hdescent : baseEnd_931077 < baseStart_931077 := by decide
  rcases family_descends (prefixWord ++ tailWord_931077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931120 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_931120 : Nat := 118140960795 + 931120 * 2 ^ 59
def prefixEnd_931120 : Nat := 4983230072969 + 3 ^ 40 * 931120 * 2
def baseEnd_931120 : Nat := 159370702338167407472621

theorem tailTrace_931120 : CollatzResearch.WordTrace tailWord_931120 prefixEnd_931120 159370702338167407472621 := by
  unfold tailWord_931120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980368193359368740335407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22640490924479158320447209 16980368193359368740335407)
  ·
    refine ⟨25470552290039053110503111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16980368193359368740335407 25470552290039053110503111)
    ·
      refine ⟨38205828435058579665754667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470552290039053110503111 38205828435058579665754667)
      ·
        refine ⟨57308742652587869498632001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205828435058579665754667 57308742652587869498632001)
        ·
          refine ⟨42981556989440902123974001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57308742652587869498632001 42981556989440902123974001)
          ·
            refine ⟨32236167742080676592980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42981556989440902123974001 32236167742080676592980501)
            ·
              refine ⟨1511070362910031715295961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32236167742080676592980501 1511070362910031715295961)
              ·
                refine ⟨1133302772182523786471971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511070362910031715295961 1133302772182523786471971)
                ·
                  refine ⟨1699954158273785679707957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133302772182523786471971 1699954158273785679707957)
                  ·
                    refine ⟨159370702338167407472621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1699954158273785679707957 159370702338167407472621)
                    ·
                      rfl

theorem cell23_931120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_931120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931120 prefixEnd_931120 := by exact prefixLift 931120
  have htrace : WordTrace (prefixWord ++ tailWord_931120) baseStart_931120 baseEnd_931120 := by
    simpa [prefixWord, tailWord_931120, baseEnd_931120] using wordTrace_append hprefix tailTrace_931120
  have hstable : (prefixWord ++ tailWord_931120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931120).length < 2 ^ (prefixWord ++ tailWord_931120).sum := by decide
  have hdescent : baseEnd_931120 < baseStart_931120 := by decide
  rcases family_descends (prefixWord ++ tailWord_931120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931137 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_931137 : Nat := 118140960795 + 931137 * 2 ^ 59
def prefixEnd_931137 : Nat := 4983230072969 + 3 ^ 40 * 931137 * 2
def baseEnd_931137 : Nat := 159373612061876218635095

theorem tailTrace_931137 : CollatzResearch.WordTrace tailWord_931137 prefixEnd_931137 159373612061876218635095 := by
  unfold tailWord_931137
  simp only [CollatzResearch.WordTrace]
  refine ⟨33961356427657149384039665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22640904285104766256026443 33961356427657149384039665)
  ·
    refine ⟨25471017320742862038029749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33961356427657149384039665 25471017320742862038029749)
    ·
      refine ⟨2387907873819643316065289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25471017320742862038029749 2387907873819643316065289)
      ·
        refine ⟨1790930905364732487048967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2387907873819643316065289 1790930905364732487048967)
        ·
          refine ⟨2686396358047098730573451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790930905364732487048967 2686396358047098730573451)
          ·
            refine ⟨4029594537070648095860177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686396358047098730573451 4029594537070648095860177)
            ·
              refine ⟨3022195902802986071895133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029594537070648095860177 3022195902802986071895133)
              ·
                refine ⟨1133323463551119776960675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3022195902802986071895133 1133323463551119776960675)
                ·
                  refine ⟨1699985195326679665441013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133323463551119776960675 1699985195326679665441013)
                  ·
                    refine ⟨159373612061876218635095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1699985195326679665441013 159373612061876218635095)
                    ·
                      rfl

theorem cell23_931137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_931137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931137 prefixEnd_931137 := by exact prefixLift 931137
  have htrace : WordTrace (prefixWord ++ tailWord_931137) baseStart_931137 baseEnd_931137 := by
    simpa [prefixWord, tailWord_931137, baseEnd_931137] using wordTrace_append hprefix tailTrace_931137
  have hstable : (prefixWord ++ tailWord_931137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931137).length < 2 ^ (prefixWord ++ tailWord_931137).sum := by decide
  have hdescent : baseEnd_931137 < baseStart_931137 := by decide
  rcases family_descends (prefixWord ++ tailWord_931137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931150 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_931150 : Nat := 118140960795 + 931150 * 2 ^ 59
def prefixEnd_931150 : Nat := 4983230072969 + 3 ^ 40 * 931150 * 2
def baseEnd_931150 : Nat := 159375837144712368347575

theorem tailTrace_931150 : CollatzResearch.WordTrace tailWord_931150 prefixEnd_931150 159375837144712368347575 := by
  unfold tailWord_931150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245228822076256575532863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22641220384406701736175269 4245228822076256575532863)
  ·
    refine ⟨6367843233114384863299295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245228822076256575532863 6367843233114384863299295)
    ·
      refine ⟨9551764849671577294948943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367843233114384863299295 9551764849671577294948943)
      ·
        refine ⟨14327647274507365942423415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9551764849671577294948943 14327647274507365942423415)
        ·
          refine ⟨21491470911761048913635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327647274507365942423415 21491470911761048913635123)
          ·
            refine ⟨32237206367641573370452685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491470911761048913635123 32237206367641573370452685)
            ·
              refine ⟨12088952387865590013919757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32237206367641573370452685 12088952387865590013919757)
              ·
                refine ⟨4533357145449596255219909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088952387865590013919757 4533357145449596255219909)
                ·
                  refine ⟨850004464771799297853733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4533357145449596255219909 850004464771799297853733)
                  ·
                    refine ⟨159375837144712368347575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850004464771799297853733 159375837144712368347575)
                    ·
                      rfl

theorem cell23_931150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_931150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931150 prefixEnd_931150 := by exact prefixLift 931150
  have htrace : WordTrace (prefixWord ++ tailWord_931150) baseStart_931150 baseEnd_931150 := by
    simpa [prefixWord, tailWord_931150, baseEnd_931150] using wordTrace_append hprefix tailTrace_931150
  have hstable : (prefixWord ++ tailWord_931150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931150).length < 2 ^ (prefixWord ++ tailWord_931150).sum := by decide
  have hdescent : baseEnd_931150 < baseStart_931150 := by decide
  rcases family_descends (prefixWord ++ tailWord_931150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931153 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_931153 : Nat := 118140960795 + 931153 * 2 ^ 59
def prefixEnd_931153 : Nat := 4983230072969 + 3 ^ 40 * 931153 * 2
def baseEnd_931153 : Nat := 478129051876100593305211

theorem tailTrace_931153 : CollatzResearch.WordTrace tailWord_931153 prefixEnd_931153 478129051876100593305211 := by
  unfold tailWord_931153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33961939995599184116622113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22641293330399456077748075 33961939995599184116622113)
  ·
    refine ⟨25471454996699388087466585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33961939995599184116622113 25471454996699388087466585)
    ·
      refine ⟨19103591247524541065599939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25471454996699388087466585 19103591247524541065599939)
      ·
        refine ⟨28655386871286811598399909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19103591247524541065599939 28655386871286811598399909)
        ·
          refine ⟨5372885038366277174699983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28655386871286811598399909 5372885038366277174699983)
          ·
            refine ⟨8059327557549415762049975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372885038366277174699983 8059327557549415762049975)
            ·
              refine ⟨12088991336324123643074963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059327557549415762049975 12088991336324123643074963)
              ·
                refine ⟨18133487004486185464612445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088991336324123643074963 18133487004486185464612445)
                ·
                  refine ⟨6800057626682319549229667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18133487004486185464612445 6800057626682319549229667)
                  ·
                    refine ⟨10200086440023479323844501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800057626682319549229667 10200086440023479323844501)
                    ·
                      refine ⟨478129051876100593305211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10200086440023479323844501 478129051876100593305211)
                      ·
                        rfl

theorem cell23_931153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_931153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931153 prefixEnd_931153 := by exact prefixLift 931153
  have htrace : WordTrace (prefixWord ++ tailWord_931153) baseStart_931153 baseEnd_931153 := by
    simpa [prefixWord, tailWord_931153, baseEnd_931153] using wordTrace_append hprefix tailTrace_931153
  have hstable : (prefixWord ++ tailWord_931153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931153).length < 2 ^ (prefixWord ++ tailWord_931153).sum := by decide
  have hdescent : baseEnd_931153 < baseStart_931153 := by decide
  rcases family_descends (prefixWord ++ tailWord_931153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931160 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_931160 : Nat := 118140960795 + 931160 * 2 ^ 59
def prefixEnd_931160 : Nat := 4983230072969 + 3 ^ 40 * 931160 * 2
def baseEnd_931160 : Nat := 478132646240682065917679

theorem tailTrace_931160 : CollatzResearch.WordTrace tailWord_931160 prefixEnd_931160 478132646240682065917679 := by
  unfold tailWord_931160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981097653286912156063467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22641463537715882874751289 16981097653286912156063467)
  ·
    refine ⟨25471646479930368234095201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16981097653286912156063467 25471646479930368234095201)
    ·
      refine ⟨19103734859947776175571401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25471646479930368234095201 19103734859947776175571401)
      ·
        refine ⟨14327801144960832131678551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19103734859947776175571401 14327801144960832131678551)
        ·
          refine ⟨21491701717441248197517827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327801144960832131678551 21491701717441248197517827)
          ·
            refine ⟨32237552576161872296276741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491701717441248197517827 32237552576161872296276741)
            ·
              refine ⟨6044541108030351055551889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32237552576161872296276741 6044541108030351055551889)
              ·
                refine ⟨4533405831022763291663917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044541108030351055551889 4533405831022763291663917)
                ·
                  refine ⟨1700027186633536234373969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4533405831022763291663917 1700027186633536234373969)
                  ·
                    refine ⟨1275020389975152175780477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1700027186633536234373969 1275020389975152175780477)
                    ·
                      refine ⟨478132646240682065917679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275020389975152175780477 478132646240682065917679)
                      ·
                        rfl

theorem cell23_931160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_931160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931160 prefixEnd_931160 := by exact prefixLift 931160
  have htrace : WordTrace (prefixWord ++ tailWord_931160) baseStart_931160 baseEnd_931160 := by
    simpa [prefixWord, tailWord_931160, baseEnd_931160] using wordTrace_append hprefix tailTrace_931160
  have hstable : (prefixWord ++ tailWord_931160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931160).length < 2 ^ (prefixWord ++ tailWord_931160).sum := by decide
  have hdescent : baseEnd_931160 < baseStart_931160 := by decide
  rcases family_descends (prefixWord ++ tailWord_931160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931170 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_931170 : Nat := 118140960795 + 931170 * 2 ^ 59
def prefixEnd_931170 : Nat := 4983230072969 + 3 ^ 40 * 931170 * 2
def baseEnd_931170 : Nat := 478137781047227026792633

theorem tailTrace_931170 : CollatzResearch.WordTrace tailWord_931170 prefixEnd_931170 478137781047227026792633 := by
  unfold tailWord_931170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490640009134399004997741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22641706691025064013327309 8490640009134399004997741)
  ·
    refine ⟨3183990003425399626874153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8490640009134399004997741 3183990003425399626874153)
    ·
      refine ⟨2387992502569049720155615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3183990003425399626874153 2387992502569049720155615)
      ·
        refine ⟨3581988753853574580233423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387992502569049720155615 3581988753853574580233423)
        ·
          refine ⟨5372983130780361870350135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581988753853574580233423 5372983130780361870350135)
          ·
            refine ⟨8059474696170542805525203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372983130780361870350135 8059474696170542805525203)
            ·
              refine ⟨12089212044255814208287805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059474696170542805525203 12089212044255814208287805)
              ·
                refine ⟨4533454516595930328107927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12089212044255814208287805 4533454516595930328107927)
                ·
                  refine ⟨6800181774893895492161891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533454516595930328107927 6800181774893895492161891)
                  ·
                    refine ⟨10200272662340843238242837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800181774893895492161891 10200272662340843238242837)
                    ·
                      refine ⟨478137781047227026792633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10200272662340843238242837 478137781047227026792633)
                      ·
                        rfl

theorem cell23_931170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_931170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931170 prefixEnd_931170 := by exact prefixLift 931170
  have htrace : WordTrace (prefixWord ++ tailWord_931170) baseStart_931170 baseEnd_931170 := by
    simpa [prefixWord, tailWord_931170, baseEnd_931170] using wordTrace_append hprefix tailTrace_931170
  have hstable : (prefixWord ++ tailWord_931170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931170).length < 2 ^ (prefixWord ++ tailWord_931170).sum := by decide
  have hdescent : baseEnd_931170 < baseStart_931170 := by decide
  rcases family_descends (prefixWord ++ tailWord_931170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931208 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_931208 : Nat := 118140960795 + 931208 * 2 ^ 59
def prefixEnd_931208 : Nat := 4983230072969 + 3 ^ 40 * 931208 * 2
def baseEnd_931208 : Nat := 478157293312097878117459

theorem tailTrace_931208 : CollatzResearch.WordTrace tailWord_931208 prefixEnd_931208 478157293312097878117459 := by
  unfold tailWord_931208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981973005199964254937139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22642630673599952339916185 16981973005199964254937139)
  ·
    refine ⟨25472959507799946382405709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16981973005199964254937139 25472959507799946382405709)
    ·
      refine ⟨9552359815424979893402141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25472959507799946382405709 9552359815424979893402141)
      ·
        refine ⟨3582134930784367460025803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9552359815424979893402141 3582134930784367460025803)
        ·
          refine ⟨5373202396176551190038705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582134930784367460025803 5373202396176551190038705)
          ·
            refine ⟨4029901797132413392529029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373202396176551190038705 4029901797132413392529029)
            ·
              refine ⟨755606586962327511099193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4029901797132413392529029 755606586962327511099193)
              ·
                refine ⟨566704940221745633324395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755606586962327511099193 566704940221745633324395)
                ·
                  refine ⟨850057410332618449986593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566704940221745633324395 850057410332618449986593)
                  ·
                    refine ⟨637543057749463837489945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850057410332618449986593 637543057749463837489945)
                    ·
                      refine ⟨478157293312097878117459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637543057749463837489945 478157293312097878117459)
                      ·
                        rfl

theorem cell23_931208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_931208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931208 prefixEnd_931208 := by exact prefixLift 931208
  have htrace : WordTrace (prefixWord ++ tailWord_931208) baseStart_931208 baseEnd_931208 := by
    simpa [prefixWord, tailWord_931208, baseEnd_931208] using wordTrace_append hprefix tailTrace_931208
  have hstable : (prefixWord ++ tailWord_931208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931208).length < 2 ^ (prefixWord ++ tailWord_931208).sum := by decide
  have hdescent : baseEnd_931208 < baseStart_931208 := by decide
  rcases family_descends (prefixWord ++ tailWord_931208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931214 : List Nat := [4, 1, 1, 4, 3, 1, 1, 8]
def baseStart_931214 : Nat := 118140960795 + 931214 * 2 ^ 59
def prefixEnd_931214 : Nat := 4983230072969 + 3 ^ 40 * 931214 * 2
def baseEnd_931214 : Nat := 17709643488741661283053

theorem tailTrace_931214 : CollatzResearch.WordTrace tailWord_931214 prefixEnd_931214 17709643488741661283053 := by
  unfold tailWord_931214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245520606047273941824087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22642776565585461023061797 4245520606047273941824087)
  ·
    refine ⟨6368280909070910912736131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245520606047273941824087 6368280909070910912736131)
    ·
      refine ⟨9552421363606366369104197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368280909070910912736131 9552421363606366369104197)
      ·
        refine ⟨1791079005676193694207037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9552421363606366369104197 1791079005676193694207037)
        ·
          refine ⟨671654627128572635327639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791079005676193694207037 671654627128572635327639)
          ·
            refine ⟨1007481940692858952991459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671654627128572635327639 1007481940692858952991459)
            ·
              refine ⟨1511222911039288429487189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007481940692858952991459 1511222911039288429487189)
              ·
                refine ⟨17709643488741661283053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1511222911039288429487189 17709643488741661283053)
                ·
                  rfl

theorem cell23_931214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_931214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931214 prefixEnd_931214 := by exact prefixLift 931214
  have htrace : WordTrace (prefixWord ++ tailWord_931214) baseStart_931214 baseEnd_931214 := by
    simpa [prefixWord, tailWord_931214, baseEnd_931214] using wordTrace_append hprefix tailTrace_931214
  have hstable : (prefixWord ++ tailWord_931214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931214).length < 2 ^ (prefixWord ++ tailWord_931214).sum := by decide
  have hdescent : baseEnd_931214 < baseStart_931214 := by decide
  rcases family_descends (prefixWord ++ tailWord_931214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931224 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_931224 : Nat := 118140960795 + 931224 * 2 ^ 59
def prefixEnd_931224 : Nat := 4983230072969 + 3 ^ 40 * 931224 * 2
def baseEnd_931224 : Nat := 478165509002569815517385

theorem tailTrace_931224 : CollatzResearch.WordTrace tailWord_931224 prefixEnd_931224 478165509002569815517385 := by
  unfold tailWord_931224
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982264789170981621228363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22643019718894642161637817 16982264789170981621228363)
  ·
    refine ⟨25473397183756472431842545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16982264789170981621228363 25473397183756472431842545)
    ·
      refine ⟨19105047887817354323881909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25473397183756472431842545 19105047887817354323881909)
      ·
        refine ⟨1791098239482876967863929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19105047887817354323881909 1791098239482876967863929)
        ·
          refine ⟨1343323679612157725897947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791098239482876967863929 1343323679612157725897947)
          ·
            refine ⟨2014985519418236588846921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343323679612157725897947 2014985519418236588846921)
            ·
              refine ⟨1511239139563677441635191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014985519418236588846921 1511239139563677441635191)
              ·
                refine ⟨2266858709345516162452787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511239139563677441635191 2266858709345516162452787)
                ·
                  refine ⟨3400288064018274243679181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266858709345516162452787 3400288064018274243679181)
                  ·
                    refine ⟨1275108024006852841379693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400288064018274243679181 1275108024006852841379693)
                    ·
                      refine ⟨478165509002569815517385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275108024006852841379693 478165509002569815517385)
                      ·
                        rfl

theorem cell23_931224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_931224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931224 prefixEnd_931224 := by exact prefixLift 931224
  have htrace : WordTrace (prefixWord ++ tailWord_931224) baseStart_931224 baseEnd_931224 := by
    simpa [prefixWord, tailWord_931224, baseEnd_931224] using wordTrace_append hprefix tailTrace_931224
  have hstable : (prefixWord ++ tailWord_931224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931224).length < 2 ^ (prefixWord ++ tailWord_931224).sum := by decide
  have hdescent : baseEnd_931224 < baseStart_931224 := by decide
  rcases family_descends (prefixWord ++ tailWord_931224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931234 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_931234 : Nat := 118140960795 + 931234 * 2 ^ 59
def prefixEnd_931234 : Nat := 4983230072969 + 3 ^ 40 * 931234 * 2
def baseEnd_931234 : Nat := 478170643809114776392339

theorem tailTrace_931234 : CollatzResearch.WordTrace tailWord_931234 prefixEnd_931234 478170643809114776392339 := by
  unfold tailWord_931234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491223577076433737580189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22643262872203823300213837 8491223577076433737580189)
  ·
    refine ⟨3184208841403662651592571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8491223577076433737580189 3184208841403662651592571)
    ·
      refine ⟨4776313262105493977388857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184208841403662651592571 4776313262105493977388857)
      ·
        refine ⟨3582234946579120483041643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4776313262105493977388857 3582234946579120483041643)
        ·
          refine ⟨5373352419868680724562465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582234946579120483041643 5373352419868680724562465)
          ·
            refine ⟨4030014314901510543421849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373352419868680724562465 4030014314901510543421849)
            ·
              refine ⟨3022510736176132907566387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030014314901510543421849 3022510736176132907566387)
              ·
                refine ⟨4533766104264199361349581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022510736176132907566387 4533766104264199361349581)
                ·
                  refine ⟨1700162289099074760506093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4533766104264199361349581 1700162289099074760506093)
                  ·
                    refine ⟨637560858412153035189785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700162289099074760506093 637560858412153035189785)
                    ·
                      refine ⟨478170643809114776392339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637560858412153035189785 478170643809114776392339)
                      ·
                        rfl

theorem cell23_931234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_931234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931234 prefixEnd_931234 := by exact prefixLift 931234
  have htrace : WordTrace (prefixWord ++ tailWord_931234) baseStart_931234 baseEnd_931234 := by
    simpa [prefixWord, tailWord_931234, baseEnd_931234] using wordTrace_append hprefix tailTrace_931234
  have hstable : (prefixWord ++ tailWord_931234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931234).length < 2 ^ (prefixWord ++ tailWord_931234).sum := by decide
  have hdescent : baseEnd_931234 < baseStart_931234 := by decide
  rcases family_descends (prefixWord ++ tailWord_931234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931243 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_931243 : Nat := 118140960795 + 931243 * 2 ^ 59
def prefixEnd_931243 : Nat := 4983230072969 + 3 ^ 40 * 931243 * 2
def baseEnd_931243 : Nat := 478175265135005241179797

theorem tailTrace_931243 : CollatzResearch.WordTrace tailWord_931243 prefixEnd_931243 478175265135005241179797 := by
  unfold tailWord_931243
  simp only [CollatzResearch.WordTrace]
  refine ⟨33965222565273129487398383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22643481710182086324932255 33965222565273129487398383)
  ·
    refine ⟨50947833847909694231097575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33965222565273129487398383 50947833847909694231097575)
    ·
      refine ⟨76421750771864541346646363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50947833847909694231097575 76421750771864541346646363)
      ·
        refine ⟨114632626157796812019969545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76421750771864541346646363 114632626157796812019969545)
        ·
          refine ⟨85974469618347609014977159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114632626157796812019969545 85974469618347609014977159)
          ·
            refine ⟨128961704427521413522465739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85974469618347609014977159 128961704427521413522465739)
            ·
              refine ⟨193442556641282120283698609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128961704427521413522465739 193442556641282120283698609)
              ·
                refine ⟨145081917480961590212773957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193442556641282120283698609 145081917480961590212773957)
                ·
                  refine ⟨27202859527680298164895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145081917480961590212773957 27202859527680298164895117)
                  ·
                    refine ⟨10201072322880111811835669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27202859527680298164895117 10201072322880111811835669)
                    ·
                      refine ⟨478175265135005241179797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10201072322880111811835669 478175265135005241179797)
                      ·
                        rfl

theorem cell23_931243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_931243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931243 prefixEnd_931243 := by exact prefixLift 931243
  have htrace : WordTrace (prefixWord ++ tailWord_931243) baseStart_931243 baseEnd_931243 := by
    simpa [prefixWord, tailWord_931243, baseEnd_931243] using wordTrace_append hprefix tailTrace_931243
  have hstable : (prefixWord ++ tailWord_931243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931243).length < 2 ^ (prefixWord ++ tailWord_931243).sum := by decide
  have hdescent : baseEnd_931243 < baseStart_931243 := by decide
  rcases family_descends (prefixWord ++ tailWord_931243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931250 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_931250 : Nat := 118140960795 + 931250 * 2 ^ 59
def prefixEnd_931250 : Nat := 4983230072969 + 3 ^ 40 * 931250 * 2
def baseEnd_931250 : Nat := 478178859499586713792265

theorem tailTrace_931250 : CollatzResearch.WordTrace tailWord_931250 prefixEnd_931250 478178859499586713792265 := by
  unfold tailWord_931250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491369469061942420725801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22643651917498513121935469 8491369469061942420725801)
  ·
    refine ⟨6368527101796456815544351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8491369469061942420725801 6368527101796456815544351)
    ·
      refine ⟨9552790652694685223316527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368527101796456815544351 9552790652694685223316527)
      ·
        refine ⟨14329185979042027834974791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9552790652694685223316527 14329185979042027834974791)
        ·
          refine ⟨21493778968563041752462187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329185979042027834974791 21493778968563041752462187)
          ·
            refine ⟨32240668452844562628693281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493778968563041752462187 32240668452844562628693281)
            ·
              refine ⟨24180501339633421971519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32240668452844562628693281 24180501339633421971519961)
              ·
                refine ⟨18135376004725066478639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24180501339633421971519961 18135376004725066478639971)
                ·
                  refine ⟨27203064007087599717959957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18135376004725066478639971 27203064007087599717959957)
                  ·
                    refine ⟨1275143625332231236779373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27203064007087599717959957 1275143625332231236779373)
                    ·
                      refine ⟨478178859499586713792265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275143625332231236779373 478178859499586713792265)
                      ·
                        rfl

theorem cell23_931250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_931250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931250 prefixEnd_931250 := by exact prefixLift 931250
  have htrace : WordTrace (prefixWord ++ tailWord_931250) baseStart_931250 baseEnd_931250 := by
    simpa [prefixWord, tailWord_931250, baseEnd_931250] using wordTrace_append hprefix tailTrace_931250
  have hstable : (prefixWord ++ tailWord_931250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931250).length < 2 ^ (prefixWord ++ tailWord_931250).sum := by decide
  have hdescent : baseEnd_931250 < baseStart_931250 := by decide
  rcases family_descends (prefixWord ++ tailWord_931250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931300 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_931300 : Nat := 118140960795 + 931300 * 2 ^ 59
def prefixEnd_931300 : Nat := 4983230072969 + 3 ^ 40 * 931300 * 2
def baseEnd_931300 : Nat := 159401511177437172722345

theorem tailTrace_931300 : CollatzResearch.WordTrace tailWord_931300 prefixEnd_931300 159401511177437172722345 := by
  unfold tailWord_931300
  simp only [CollatzResearch.WordTrace]
  refine ⟨16983650763033314111111677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22644867684044418814815569 16983650763033314111111677)
  ·
    refine ⟨6368869036137492791666879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16983650763033314111111677 6368869036137492791666879)
    ·
      refine ⟨9553303554206239187500319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368869036137492791666879 9553303554206239187500319)
      ·
        refine ⟨14329955331309358781250479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553303554206239187500319 14329955331309358781250479)
        ·
          refine ⟨21494932996964038171875719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329955331309358781250479 21494932996964038171875719)
          ·
            refine ⟨32242399495446057257813579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21494932996964038171875719 32242399495446057257813579)
            ·
              refine ⟨48363599243169085886720369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242399495446057257813579 48363599243169085886720369)
              ·
                refine ⟨36272699432376814415040277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48363599243169085886720369 36272699432376814415040277)
                ·
                  refine ⟨1700282785892663175705013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36272699432376814415040277 1700282785892663175705013)
                  ·
                    refine ⟨159401511177437172722345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1700282785892663175705013 159401511177437172722345)
                    ·
                      rfl

theorem cell23_931300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_931300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931300 prefixEnd_931300 := by exact prefixLift 931300
  have htrace : WordTrace (prefixWord ++ tailWord_931300) baseStart_931300 baseEnd_931300 := by
    simpa [prefixWord, tailWord_931300, baseEnd_931300] using wordTrace_append hprefix tailTrace_931300
  have hstable : (prefixWord ++ tailWord_931300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931300).length < 2 ^ (prefixWord ++ tailWord_931300).sum := by decide
  have hdescent : baseEnd_931300 < baseStart_931300 := by decide
  rcases family_descends (prefixWord ++ tailWord_931300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931332 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_931332 : Nat := 118140960795 + 931332 * 2 ^ 59
def prefixEnd_931332 : Nat := 4983230072969 + 3 ^ 40 * 931332 * 2
def baseEnd_931332 : Nat := 478220964913255392966889

theorem tailTrace_931332 : CollatzResearch.WordTrace tailWord_931332 prefixEnd_931332 478220964913255392966889 := by
  unfold tailWord_931332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984234330975348843694125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22645645774633798458258833 16984234330975348843694125)
  ·
    refine ⟨6369087874115755816385297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16984234330975348843694125 6369087874115755816385297)
    ·
      refine ⟨4776815905586816862288973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369087874115755816385297 4776815905586816862288973)
      ·
        refine ⟨1791305964595056323358365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4776815905586816862288973 1791305964595056323358365)
        ·
          refine ⟨671739736723146121259387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791305964595056323358365 671739736723146121259387)
          ·
            refine ⟨1007609605084719181889081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671739736723146121259387 1007609605084719181889081)
            ·
              refine ⟨755707203813539386416811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007609605084719181889081 755707203813539386416811)
              ·
                refine ⟨1133560805720309079625217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755707203813539386416811 1133560805720309079625217)
                ·
                  refine ⟨850170604290231809718913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133560805720309079625217 850170604290231809718913)
                  ·
                    refine ⟨637627953217673857289185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850170604290231809718913 637627953217673857289185)
                    ·
                      refine ⟨478220964913255392966889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637627953217673857289185 478220964913255392966889)
                      ·
                        rfl

theorem cell23_931332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_931332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931332 prefixEnd_931332 := by exact prefixLift 931332
  have htrace : WordTrace (prefixWord ++ tailWord_931332) baseStart_931332 baseEnd_931332 := by
    simpa [prefixWord, tailWord_931332, baseEnd_931332] using wordTrace_append hprefix tailTrace_931332
  have hstable : (prefixWord ++ tailWord_931332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931332).length < 2 ^ (prefixWord ++ tailWord_931332).sum := by decide
  have hdescent : baseEnd_931332 < baseStart_931332 := by decide
  rcases family_descends (prefixWord ++ tailWord_931332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931337 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 6, 2]
def baseStart_931337 : Nat := 118140960795 + 931337 * 2 ^ 59
def prefixEnd_931337 : Nat := 4983230072969 + 3 ^ 40 * 931337 * 2
def baseEnd_931337 : Nat := 478223532316527873404365

theorem tailTrace_931337 : CollatzResearch.WordTrace tailWord_931337 prefixEnd_931337 478223532316527873404365 := by
  unfold tailWord_931337
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968651026932583541320265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22645767351288389027546843 33968651026932583541320265)
  ·
    refine ⟨25476488270199437655990199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33968651026932583541320265 25476488270199437655990199)
    ·
      refine ⟨38214732405299156483985299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25476488270199437655990199 38214732405299156483985299)
      ·
        refine ⟨57322098607948734725977949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38214732405299156483985299 57322098607948734725977949)
        ·
          refine ⟨21495786977980775522241731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57322098607948734725977949 21495786977980775522241731)
          ·
            refine ⟨32243680466971163283362597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21495786977980775522241731 32243680466971163283362597)
            ·
              refine ⟨6045690087557093115630487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32243680466971163283362597 6045690087557093115630487)
              ·
                refine ⟨9068535131335639673445731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045690087557093115630487 9068535131335639673445731)
                ·
                  refine ⟨13602802697003459510168597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068535131335639673445731 13602802697003459510168597)
                  ·
                    refine ⟨637631376422037164539153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13602802697003459510168597 637631376422037164539153)
                    ·
                      refine ⟨478223532316527873404365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637631376422037164539153 478223532316527873404365)
                      ·
                        rfl

theorem cell23_931337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6, 2].length) (baseStart_931337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931337 prefixEnd_931337 := by exact prefixLift 931337
  have htrace : WordTrace (prefixWord ++ tailWord_931337) baseStart_931337 baseEnd_931337 := by
    simpa [prefixWord, tailWord_931337, baseEnd_931337] using wordTrace_append hprefix tailTrace_931337
  have hstable : (prefixWord ++ tailWord_931337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931337).length < 2 ^ (prefixWord ++ tailWord_931337).sum := by decide
  have hdescent : baseEnd_931337 < baseStart_931337 := by decide
  rcases family_descends (prefixWord ++ tailWord_931337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931381 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_931381 : Nat := 118140960795 + 931381 * 2 ^ 59
def prefixEnd_931381 : Nat := 4983230072969 + 3 ^ 40 * 931381 * 2
def baseEnd_931381 : Nat := 159415375155108567084721

theorem tailTrace_931381 : CollatzResearch.WordTrace tailWord_931381 prefixEnd_931381 159415375155108567084721 := by
  unfold tailWord_931381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970255838773179055921997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22646837225848786037281331 33970255838773179055921997)
  ·
    refine ⟨12738845939539942145970749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33970255838773179055921997 12738845939539942145970749)
    ·
      refine ⟨4777067227327478304739031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12738845939539942145970749 4777067227327478304739031)
      ·
        refine ⟨7165600840991217457108547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777067227327478304739031 7165600840991217457108547)
        ·
          refine ⟨10748401261486826185662821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165600840991217457108547 10748401261486826185662821)
          ·
            refine ⟨2015325236528779909811779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10748401261486826185662821 2015325236528779909811779)
            ·
              refine ⟨3022987854793169864717669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015325236528779909811779 3022987854793169864717669)
              ·
                refine ⟨566810222773719349634563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3022987854793169864717669 566810222773719349634563)
                ·
                  refine ⟨850215334160579024451845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566810222773719349634563 850215334160579024451845)
                  ·
                    refine ⟨159415375155108567084721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850215334160579024451845 159415375155108567084721)
                    ·
                      rfl

theorem cell23_931381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_931381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931381 prefixEnd_931381 := by exact prefixLift 931381
  have htrace : WordTrace (prefixWord ++ tailWord_931381) baseStart_931381 baseEnd_931381 := by
    simpa [prefixWord, tailWord_931381, baseEnd_931381] using wordTrace_append hprefix tailTrace_931381
  have hstable : (prefixWord ++ tailWord_931381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931381).length < 2 ^ (prefixWord ++ tailWord_931381).sum := by decide
  have hdescent : baseEnd_931381 < baseStart_931381 := by decide
  rcases family_descends (prefixWord ++ tailWord_931381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931398 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_931398 : Nat := 118140960795 + 931398 * 2 ^ 59
def prefixEnd_931398 : Nat := 4983230072969 + 3 ^ 40 * 931398 * 2
def baseEnd_931398 : Nat := 159418284878817378247195

theorem tailTrace_931398 : CollatzResearch.WordTrace tailWord_931398 prefixEnd_931398 159418284878817378247195 := by
  unfold tailWord_931398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061589871240987217477839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22647250586474393972860565 1061589871240987217477839)
  ·
    refine ⟨1592384806861480826216759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061589871240987217477839 1592384806861480826216759)
    ·
      refine ⟨2388577210292221239325139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592384806861480826216759 2388577210292221239325139)
      ·
        refine ⟨3582865815438331858987709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388577210292221239325139 3582865815438331858987709)
        ·
          refine ⟨1343574680789374447120391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3582865815438331858987709 1343574680789374447120391)
          ·
            refine ⟨2015362021184061670680587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343574680789374447120391 2015362021184061670680587)
            ·
              refine ⟨3023043031776092506020881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015362021184061670680587 3023043031776092506020881)
              ·
                refine ⟨2267282273832069379515661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023043031776092506020881 2267282273832069379515661)
                ·
                  refine ⟨850230852687026017318373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267282273832069379515661 850230852687026017318373)
                  ·
                    refine ⟨159418284878817378247195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850230852687026017318373 159418284878817378247195)
                    ·
                      rfl

theorem cell23_931398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_931398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931398 prefixEnd_931398 := by exact prefixLift 931398
  have htrace : WordTrace (prefixWord ++ tailWord_931398) baseStart_931398 baseEnd_931398 := by
    simpa [prefixWord, tailWord_931398, baseEnd_931398] using wordTrace_append hprefix tailTrace_931398
  have hstable : (prefixWord ++ tailWord_931398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931398).length < 2 ^ (prefixWord ++ tailWord_931398).sum := by decide
  have hdescent : baseEnd_931398 < baseStart_931398 := by decide
  rcases family_descends (prefixWord ++ tailWord_931398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931404 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_931404 : Nat := 118140960795 + 931404 * 2 ^ 59
def prefixEnd_931404 : Nat := 4983230072969 + 3 ^ 40 * 931404 * 2
def baseEnd_931404 : Nat := 478257935520379111266557

theorem tailTrace_931404 : CollatzResearch.WordTrace tailWord_931404 prefixEnd_931404 478257935520379111266557 := by
  unfold tailWord_931404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985547358844926992004633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22647396478459902656006177 16985547358844926992004633)
  ·
    refine ⟨12739160519133695244003475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16985547358844926992004633 12739160519133695244003475)
    ·
      refine ⟨19108740778700542866005213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739160519133695244003475 19108740778700542866005213)
      ·
        refine ⟨7165777792012703574751955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19108740778700542866005213 7165777792012703574751955)
        ·
          refine ⟨10748666688019055362127933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165777792012703574751955 10748666688019055362127933)
          ·
            refine ⟨4030750008007145760797975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10748666688019055362127933 4030750008007145760797975)
            ·
              refine ⟨6046125012010718641196963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030750008007145760797975 6046125012010718641196963)
              ·
                refine ⟨9069187518016077961795445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046125012010718641196963 9069187518016077961795445)
                ·
                  refine ⟨850236329814007308918323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9069187518016077961795445 850236329814007308918323)
                  ·
                    refine ⟨1275354494721010963377485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 850236329814007308918323 1275354494721010963377485)
                    ·
                      refine ⟨478257935520379111266557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275354494721010963377485 478257935520379111266557)
                      ·
                        rfl

theorem cell23_931404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_931404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931404 prefixEnd_931404 := by exact prefixLift 931404
  have htrace : WordTrace (prefixWord ++ tailWord_931404) baseStart_931404 baseEnd_931404 := by
    simpa [prefixWord, tailWord_931404, baseEnd_931404] using wordTrace_append hprefix tailTrace_931404
  have hstable : (prefixWord ++ tailWord_931404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931404).length < 2 ^ (prefixWord ++ tailWord_931404).sum := by decide
  have hdescent : baseEnd_931404 < baseStart_931404 := by decide
  rcases family_descends (prefixWord ++ tailWord_931404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931407 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 1, 5]
def baseStart_931407 : Nat := 118140960795 + 931407 * 2 ^ 59
def prefixEnd_931407 : Nat := 4983230072969 + 3 ^ 40 * 931407 * 2
def baseEnd_931407 : Nat := 159419825320780866509681

theorem tailTrace_931407 : CollatzResearch.WordTrace tailWord_931407 prefixEnd_931407 159419825320780866509681 := by
  unfold tailWord_931407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33971204136678985496368475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22647469424452656997578983 33971204136678985496368475)
  ·
    refine ⟨50956806205018478244552713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33971204136678985496368475 50956806205018478244552713)
    ·
      refine ⟨38217604653763858683414535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50956806205018478244552713 38217604653763858683414535)
      ·
        refine ⟨57326406980645788025121803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38217604653763858683414535 57326406980645788025121803)
        ·
          refine ⟨85989610470968682037682705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57326406980645788025121803 85989610470968682037682705)
          ·
            refine ⟨64492207853226511528262029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85989610470968682037682705 64492207853226511528262029)
            ·
              refine ⟨24184577944959941823098261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64492207853226511528262029 24184577944959941823098261)
              ·
                refine ⟨1133652091169997272957731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24184577944959941823098261 1133652091169997272957731)
                ·
                  refine ⟨1700478136754995909436597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133652091169997272957731 1700478136754995909436597)
                  ·
                    refine ⟨159419825320780866509681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1700478136754995909436597 159419825320780866509681)
                    ·
                      rfl

theorem cell23_931407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_931407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931407 prefixEnd_931407 := by exact prefixLift 931407
  have htrace : WordTrace (prefixWord ++ tailWord_931407) baseStart_931407 baseEnd_931407 := by
    simpa [prefixWord, tailWord_931407, baseEnd_931407] using wordTrace_append hprefix tailTrace_931407
  have hstable : (prefixWord ++ tailWord_931407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931407).length < 2 ^ (prefixWord ++ tailWord_931407).sum := by decide
  have hdescent : baseEnd_931407 < baseStart_931407 := by decide
  rcases family_descends (prefixWord ++ tailWord_931407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931438 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_931438 : Nat := 118140960795 + 931438 * 2 ^ 59
def prefixEnd_931438 : Nat := 4983230072969 + 3 ^ 40 * 931438 * 2
def baseEnd_931438 : Nat := 478275393862631978241401

theorem tailTrace_931438 : CollatzResearch.WordTrace tailWord_931438 prefixEnd_931438 478275393862631978241401 := by
  unfold tailWord_931438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246541849945834723843371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22648223199711118527164645 4246541849945834723843371)
  ·
    refine ⟨6369812774918752085765057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4246541849945834723843371 6369812774918752085765057)
    ·
      refine ⟨4777359581189064064323793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369812774918752085765057 4777359581189064064323793)
      ·
        refine ⟨3583019685891798048242845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777359581189064064323793 3583019685891798048242845)
        ·
          refine ⟨1343632382209424268091067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3583019685891798048242845 1343632382209424268091067)
          ·
            refine ⟨2015448573314136402136601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343632382209424268091067 2015448573314136402136601)
            ·
              refine ⟨1511586429985602301602451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015448573314136402136601 1511586429985602301602451)
              ·
                refine ⟨2267379644978403452403677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511586429985602301602451 2267379644978403452403677)
                ·
                  refine ⟨850267366866901294651379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267379644978403452403677 850267366866901294651379)
                  ·
                    refine ⟨1275401050300351941977069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 850267366866901294651379 1275401050300351941977069)
                    ·
                      refine ⟨478275393862631978241401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275401050300351941977069 478275393862631978241401)
                      ·
                        rfl

theorem cell23_931438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_931438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931438 prefixEnd_931438 := by exact prefixLift 931438
  have htrace : WordTrace (prefixWord ++ tailWord_931438) baseStart_931438 baseEnd_931438 := by
    simpa [prefixWord, tailWord_931438, baseEnd_931438] using wordTrace_append hprefix tailTrace_931438
  have hstable : (prefixWord ++ tailWord_931438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931438).length < 2 ^ (prefixWord ++ tailWord_931438).sum := by decide
  have hdescent : baseEnd_931438 < baseStart_931438 := by decide
  rcases family_descends (prefixWord ++ tailWord_931438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931461 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_931461 : Nat := 118140960795 + 931461 * 2 ^ 59
def prefixEnd_931461 : Nat := 4983230072969 + 3 ^ 40 * 931461 * 2
def baseEnd_931461 : Nat := 478287203917685388253795

theorem tailTrace_931461 : CollatzResearch.WordTrace tailWord_931461 prefixEnd_931461 478287203917685388253795 := by
  unfold tailWord_931461
  simp only [CollatzResearch.WordTrace]
  refine ⟨33973173678483352718834237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22648782452322235145889491 33973173678483352718834237)
  ·
    refine ⟨12739940129431257269562839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33973173678483352718834237 12739940129431257269562839)
    ·
      refine ⟨19109910194146885904344259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739940129431257269562839 19109910194146885904344259)
      ·
        refine ⟨28664865291220328856516389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19109910194146885904344259 28664865291220328856516389)
        ·
          refine ⟨5374662242103811660596823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28664865291220328856516389 5374662242103811660596823)
          ·
            refine ⟨8061993363155717490895235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374662242103811660596823 8061993363155717490895235)
            ·
              refine ⟨12092990044733576236342853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061993363155717490895235 12092990044733576236342853)
              ·
                refine ⟨2267435633387545544314285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12092990044733576236342853 2267435633387545544314285)
                ·
                  refine ⟨850288362520329579117857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267435633387545544314285 850288362520329579117857)
                  ·
                    refine ⟨637716271890247184338393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850288362520329579117857 637716271890247184338393)
                    ·
                      refine ⟨478287203917685388253795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637716271890247184338393 478287203917685388253795)
                      ·
                        rfl

theorem cell23_931461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_931461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931461 prefixEnd_931461 := by exact prefixLift 931461
  have htrace : WordTrace (prefixWord ++ tailWord_931461) baseStart_931461 baseEnd_931461 := by
    simpa [prefixWord, tailWord_931461, baseEnd_931461] using wordTrace_append hprefix tailTrace_931461
  have hstable : (prefixWord ++ tailWord_931461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931461).length < 2 ^ (prefixWord ++ tailWord_931461).sum := by decide
  have hdescent : baseEnd_931461 < baseStart_931461 := by decide
  rcases family_descends (prefixWord ++ tailWord_931461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931484 : List Nat := [2, 2, 3, 2, 3, 2, 9]
def baseStart_931484 : Nat := 118140960795 + 931484 * 2 ^ 59
def prefixEnd_931484 : Nat := 4983230072969 + 3 ^ 40 * 931484 * 2
def baseEnd_931484 : Nat := 5904926098428874052669

theorem tailTrace_931484 : CollatzResearch.WordTrace tailWord_931484 prefixEnd_931484 5904926098428874052669 := by
  unfold tailWord_931484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987006278700013823460753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22649341704933351764614337 16987006278700013823460753)
  ·
    refine ⟨12740254709025010367595565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16987006278700013823460753 12740254709025010367595565)
    ·
      refine ⟨4777595515884378887848337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12740254709025010367595565 4777595515884378887848337)
      ·
        refine ⟨3583196636913284165886253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777595515884378887848337 3583196636913284165886253)
        ·
          refine ⟨1343698738842481562207345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3583196636913284165886253 1343698738842481562207345)
          ·
            refine ⟨1007774054131861171655509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1343698738842481562207345 1007774054131861171655509)
            ·
              refine ⟨5904926098428874052669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1007774054131861171655509 5904926098428874052669)
              ·
                rfl

theorem cell23_931484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 9].length) (baseStart_931484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931484 prefixEnd_931484 := by exact prefixLift 931484
  have htrace : WordTrace (prefixWord ++ tailWord_931484) baseStart_931484 baseEnd_931484 := by
    simpa [prefixWord, tailWord_931484, baseEnd_931484] using wordTrace_append hprefix tailTrace_931484
  have hstable : (prefixWord ++ tailWord_931484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931484).length < 2 ^ (prefixWord ++ tailWord_931484).sum := by decide
  have hdescent : baseEnd_931484 < baseStart_931484 := by decide
  rcases family_descends (prefixWord ++ tailWord_931484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931574 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_931574 : Nat := 118140960795 + 931574 * 2 ^ 59
def prefixEnd_931574 : Nat := 4983230072969 + 3 ^ 40 * 931574 * 2
def baseEnd_931574 : Nat := 53149469692404827348975

theorem tailTrace_931574 : CollatzResearch.WordTrace tailWord_931574 prefixEnd_931574 53149469692404827348975 := by
  unfold tailWord_931574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123580945442123313606111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22651530084715982011798517 2123580945442123313606111)
  ·
    refine ⟨3185371418163184970409167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2123580945442123313606111 3185371418163184970409167)
    ·
      refine ⟨4778057127244777455613751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185371418163184970409167 4778057127244777455613751)
      ·
        refine ⟨7167085690867166183420627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778057127244777455613751 7167085690867166183420627)
        ·
          refine ⟨10750628536300749275130941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167085690867166183420627 10750628536300749275130941)
          ·
            refine ⟨4031485701112780978174103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10750628536300749275130941 4031485701112780978174103)
            ·
              refine ⟨6047228551669171467261155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031485701112780978174103 6047228551669171467261155)
              ·
                refine ⟨9070842827503757200891733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047228551669171467261155 9070842827503757200891733)
                ·
                  refine ⟨53149469692404827348975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9070842827503757200891733 53149469692404827348975)
                  ·
                    rfl

theorem cell23_931574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_931574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931574 prefixEnd_931574 := by exact prefixLift 931574
  have htrace : WordTrace (prefixWord ++ tailWord_931574) baseStart_931574 baseEnd_931574 := by
    simpa [prefixWord, tailWord_931574, baseEnd_931574] using wordTrace_append hprefix tailTrace_931574
  have hstable : (prefixWord ++ tailWord_931574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931574).length < 2 ^ (prefixWord ++ tailWord_931574).sum := by decide
  have hdescent : baseEnd_931574 < baseStart_931574 := by decide
  rcases family_descends (prefixWord ++ tailWord_931574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931602 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_931602 : Nat := 118140960795 + 931602 * 2 ^ 59
def prefixEnd_931602 : Nat := 4983230072969 + 3 ^ 40 * 931602 * 2
def baseEnd_931602 : Nat := 478359604689969336590647

theorem tailTrace_931602 : CollatzResearch.WordTrace tailWord_931602 prefixEnd_931602 478359604689969336590647 := by
  unfold tailWord_931602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494579092743133449929265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22652210913981689199811373 8494579092743133449929265)
  ·
    refine ⟨6370934319557350087446949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8494579092743133449929265 6370934319557350087446949)
    ·
      refine ⟨1194550184917003141396303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6370934319557350087446949 1194550184917003141396303)
      ·
        refine ⟨1791825277375504712094455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194550184917003141396303 1791825277375504712094455)
        ·
          refine ⟨2687737916063257068141683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791825277375504712094455 2687737916063257068141683)
          ·
            refine ⟨4031606874094885602212525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687737916063257068141683 4031606874094885602212525)
            ·
              refine ⟨1511852577785582100829697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031606874094885602212525 1511852577785582100829697)
              ·
                refine ⟨1133889433339186575622273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511852577785582100829697 1133889433339186575622273)
                ·
                  refine ⟨850417075004389931716705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133889433339186575622273 850417075004389931716705)
                  ·
                    refine ⟨637812806253292448787529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850417075004389931716705 637812806253292448787529)
                    ·
                      refine ⟨478359604689969336590647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637812806253292448787529 478359604689969336590647)
                      ·
                        rfl

theorem cell23_931602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_931602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931602 prefixEnd_931602 := by exact prefixLift 931602
  have htrace : WordTrace (prefixWord ++ tailWord_931602) baseStart_931602 baseEnd_931602 := by
    simpa [prefixWord, tailWord_931602, baseEnd_931602] using wordTrace_append hprefix tailTrace_931602
  have hstable : (prefixWord ++ tailWord_931602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931602).length < 2 ^ (prefixWord ++ tailWord_931602).sum := by decide
  have hdescent : baseEnd_931602 < baseStart_931602 := by decide
  rcases family_descends (prefixWord ++ tailWord_931602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931627 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_931627 : Nat := 118140960795 + 931627 * 2 ^ 59
def prefixEnd_931627 : Nat := 4983230072969 + 3 ^ 40 * 931627 * 2
def baseEnd_931627 : Nat := 478372441706331738778031

theorem tailTrace_931627 : CollatzResearch.WordTrace tailWord_931627 prefixEnd_931627 478372441706331738778031 := by
  unfold tailWord_931627
  simp only [CollatzResearch.WordTrace]
  refine ⟨33979228195881963069377135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22652818797254642046251423 33979228195881963069377135)
  ·
    refine ⟨50968842293822944604065703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33979228195881963069377135 50968842293822944604065703)
    ·
      refine ⟨76453263440734416906098555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50968842293822944604065703 76453263440734416906098555)
      ·
        refine ⟨114679895161101625359147833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76453263440734416906098555 114679895161101625359147833)
        ·
          refine ⟨86009921370826219019360875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114679895161101625359147833 86009921370826219019360875)
          ·
            refine ⟨129014882056239328529041313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86009921370826219019360875 129014882056239328529041313)
            ·
              refine ⟨96761161542179496396780985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129014882056239328529041313 96761161542179496396780985)
              ·
                refine ⟨72570871156634622297585739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96761161542179496396780985 72570871156634622297585739)
                ·
                  refine ⟨108856306734951933446378609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72570871156634622297585739 108856306734951933446378609)
                  ·
                    refine ⟨81642230051213950084783957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108856306734951933446378609 81642230051213950084783957)
                    ·
                      refine ⟨478372441706331738778031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 81642230051213950084783957 478372441706331738778031)
                      ·
                        rfl

theorem cell23_931627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_931627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931627 prefixEnd_931627 := by exact prefixLift 931627
  have htrace : WordTrace (prefixWord ++ tailWord_931627) baseStart_931627 baseEnd_931627 := by
    simpa [prefixWord, tailWord_931627, baseEnd_931627] using wordTrace_append hprefix tailTrace_931627
  have hstable : (prefixWord ++ tailWord_931627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931627).length < 2 ^ (prefixWord ++ tailWord_931627).sum := by decide
  have hdescent : baseEnd_931627 < baseStart_931627 := by decide
  rcases family_descends (prefixWord ++ tailWord_931627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931664 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 6]
def baseStart_931664 : Nat := 118140960795 + 931664 * 2 ^ 59
def prefixEnd_931664 : Nat := 4983230072969 + 3 ^ 40 * 931664 * 2
def baseEnd_931664 : Nat := 53154604498949788223929

theorem tailTrace_931664 : CollatzResearch.WordTrace tailWord_931664 prefixEnd_931664 53154604498949788223929 := by
  unfold tailWord_931664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16990288848373959194237023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22653718464498612258982697 16990288848373959194237023)
  ·
    refine ⟨25485433272560938791355535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16990288848373959194237023 25485433272560938791355535)
    ·
      refine ⟨38228149908841408187033303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25485433272560938791355535 38228149908841408187033303)
      ·
        refine ⟨57342224863262112280549955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38228149908841408187033303 57342224863262112280549955)
        ·
          refine ⟨86013337294893168420824933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57342224863262112280549955 86013337294893168420824933)
          ·
            refine ⟨16127500742792469078904675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86013337294893168420824933 16127500742792469078904675)
            ·
              refine ⟨24191251114188703618357013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127500742792469078904675 24191251114188703618357013)
              ·
                refine ⟨1133964895977595482110485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24191251114188703618357013 1133964895977595482110485)
                ·
                  refine ⟨53154604498949788223929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1133964895977595482110485 53154604498949788223929)
                  ·
                    rfl

theorem cell23_931664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_931664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931664 prefixEnd_931664 := by exact prefixLift 931664
  have htrace : WordTrace (prefixWord ++ tailWord_931664) baseStart_931664 baseEnd_931664 := by
    simpa [prefixWord, tailWord_931664, baseEnd_931664] using wordTrace_append hprefix tailTrace_931664
  have hstable : (prefixWord ++ tailWord_931664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931664).length < 2 ^ (prefixWord ++ tailWord_931664).sum := by decide
  have hdescent : baseEnd_931664 < baseStart_931664 := by decide
  rcases family_descends (prefixWord ++ tailWord_931664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931668 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_931668 : Nat := 118140960795 + 931668 * 2 ^ 59
def prefixEnd_931668 : Nat := 4983230072969 + 3 ^ 40 * 931668 * 2
def baseEnd_931668 : Nat := 159464498137722026121781

theorem tailTrace_931668 : CollatzResearch.WordTrace tailWord_931668 prefixEnd_931668 159464498137722026121781 := by
  unfold tailWord_931668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16990361794366713535809829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22653815725822284714413105 16990361794366713535809829)
  ·
    refine ⟨3185692836443758787964343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16990361794366713535809829 3185692836443758787964343)
    ·
      refine ⟨4778539254665638181946515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185692836443758787964343 4778539254665638181946515)
      ·
        refine ⟨7167808881998457272919773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778539254665638181946515 7167808881998457272919773)
        ·
          refine ⟨2687928330749421477344915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7167808881998457272919773 2687928330749421477344915)
          ·
            refine ⟨4031892496124132216017373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687928330749421477344915 4031892496124132216017373)
            ·
              refine ⟨1511959686046549581006515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031892496124132216017373 1511959686046549581006515)
              ·
                refine ⟨2267939529069824371509773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511959686046549581006515 2267939529069824371509773)
                ·
                  refine ⟨850477323401184139316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267939529069824371509773 850477323401184139316165)
                  ·
                    refine ⟨159464498137722026121781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850477323401184139316165 159464498137722026121781)
                    ·
                      rfl

theorem cell23_931668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_931668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931668 prefixEnd_931668 := by exact prefixLift 931668
  have htrace : WordTrace (prefixWord ++ tailWord_931668) baseStart_931668 baseEnd_931668 := by
    simpa [prefixWord, tailWord_931668, baseEnd_931668] using wordTrace_append hprefix tailTrace_931668
  have hstable : (prefixWord ++ tailWord_931668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931668).length < 2 ^ (prefixWord ++ tailWord_931668).sum := by decide
  have hdescent : baseEnd_931668 < baseStart_931668 := by decide
  rcases family_descends (prefixWord ++ tailWord_931668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931691 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 3]
def baseStart_931691 : Nat := 118140960795 + 931691 * 2 ^ 59
def prefixEnd_931691 : Nat := 4983230072969 + 3 ^ 40 * 931691 * 2
def baseEnd_931691 : Nat := 478405304468219488377737

theorem tailTrace_931691 : CollatzResearch.WordTrace tailWord_931691 prefixEnd_931691 478405304468219488377737 := by
  unfold tailWord_931691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981562467650101999706927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22654374978433401333137951 33981562467650101999706927)
  ·
    refine ⟨50972343701475152999560391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33981562467650101999706927 50972343701475152999560391)
    ·
      refine ⟨76458515552212729499340587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50972343701475152999560391 76458515552212729499340587)
      ·
        refine ⟨114687773328319094249010881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76458515552212729499340587 114687773328319094249010881)
        ·
          refine ⟨86015829996239320686758161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114687773328319094249010881 86015829996239320686758161)
          ·
            refine ⟨64511872497179490515068621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86015829996239320686758161 64511872497179490515068621)
            ·
              refine ⟨24191952186442308943150733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64511872497179490515068621 24191952186442308943150733)
              ·
                refine ⟨9071982069915865853681525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24191952186442308943150733 9071982069915865853681525)
                ·
                  refine ⟨850498319054612423782643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9071982069915865853681525 850498319054612423782643)
                  ·
                    refine ⟨1275747478581918635673965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 850498319054612423782643 1275747478581918635673965)
                    ·
                      refine ⟨478405304468219488377737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275747478581918635673965 478405304468219488377737)
                      ·
                        rfl

theorem cell23_931691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 3].length) (baseStart_931691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931691 prefixEnd_931691 := by exact prefixLift 931691
  have htrace : WordTrace (prefixWord ++ tailWord_931691) baseStart_931691 baseEnd_931691 := by
    simpa [prefixWord, tailWord_931691, baseEnd_931691] using wordTrace_append hprefix tailTrace_931691
  have hstable : (prefixWord ++ tailWord_931691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931691).length < 2 ^ (prefixWord ++ tailWord_931691).sum := by decide
  have hdescent : baseEnd_931691 < baseStart_931691 := by decide
  rcases family_descends (prefixWord ++ tailWord_931691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931719 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 1, 4]
def baseStart_931719 : Nat := 118140960795 + 931719 * 2 ^ 59
def prefixEnd_931719 : Nat := 4983230072969 + 3 ^ 40 * 931719 * 2
def baseEnd_931719 : Nat := 159473227308848459609203

theorem tailTrace_931719 : CollatzResearch.WordTrace tailWord_931719 prefixEnd_931719 159473227308848459609203 := by
  unfold tailWord_931719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33982583711548662781726211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22655055807699108521150807 33982583711548662781726211)
  ·
    refine ⟨50973875567322994172589317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33982583711548662781726211 50973875567322994172589317)
    ·
      refine ⟨9557601668873061407360497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50973875567322994172589317 9557601668873061407360497)
      ·
        refine ⟨7168201251654796055520373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9557601668873061407360497 7168201251654796055520373)
        ·
          refine ⟨672018867342637130205035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7168201251654796055520373 672018867342637130205035)
          ·
            refine ⟨1008028301013955695307553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672018867342637130205035 1008028301013955695307553)
            ·
              refine ⟨756021225760466771480665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008028301013955695307553 756021225760466771480665)
              ·
                refine ⟨567015919320350078610499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756021225760466771480665 567015919320350078610499)
                ·
                  refine ⟨850523878980525117915749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567015919320350078610499 850523878980525117915749)
                  ·
                    refine ⟨159473227308848459609203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850523878980525117915749 159473227308848459609203)
                    ·
                      rfl

theorem cell23_931719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_931719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931719 prefixEnd_931719 := by exact prefixLift 931719
  have htrace : WordTrace (prefixWord ++ tailWord_931719) baseStart_931719 baseEnd_931719 := by
    simpa [prefixWord, tailWord_931719, baseEnd_931719] using wordTrace_append hprefix tailTrace_931719
  have hstable : (prefixWord ++ tailWord_931719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931719).length < 2 ^ (prefixWord ++ tailWord_931719).sum := by decide
  have hdescent : baseEnd_931719 < baseStart_931719 := by decide
  rcases family_descends (prefixWord ++ tailWord_931719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931724 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_931724 : Nat := 118140960795 + 931724 * 2 ^ 59
def prefixEnd_931724 : Nat := 4983230072969 + 3 ^ 40 * 931724 * 2
def baseEnd_931724 : Nat := 159474083109939286421695

theorem tailTrace_931724 : CollatzResearch.WordTrace tailWord_931724 prefixEnd_931724 159474083109939286421695 := by
  unfold tailWord_931724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991383038265274317829113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22655177384353699090438817 16991383038265274317829113)
  ·
    refine ⟨12743537278698955738371835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16991383038265274317829113 12743537278698955738371835)
    ·
      refine ⟨19115305918048433607557753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12743537278698955738371835 19115305918048433607557753)
      ·
        refine ⟨14336479438536325205668315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19115305918048433607557753 14336479438536325205668315)
        ·
          refine ⟨21504719157804487808502473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336479438536325205668315 21504719157804487808502473)
          ·
            refine ⟨16128539368353365856376855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21504719157804487808502473 16128539368353365856376855)
            ·
              refine ⟨24192809052530048784565283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16128539368353365856376855 24192809052530048784565283)
              ·
                refine ⟨36289213578795073176847925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24192809052530048784565283 36289213578795073176847925)
                ·
                  refine ⟨3402113773012038110329493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36289213578795073176847925 3402113773012038110329493)
                  ·
                    refine ⟨159474083109939286421695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3402113773012038110329493 159474083109939286421695)
                    ·
                      rfl

theorem cell23_931724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_931724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931724 prefixEnd_931724 := by exact prefixLift 931724
  have htrace : WordTrace (prefixWord ++ tailWord_931724) baseStart_931724 baseEnd_931724 := by
    simpa [prefixWord, tailWord_931724, baseEnd_931724] using wordTrace_append hprefix tailTrace_931724
  have hstable : (prefixWord ++ tailWord_931724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931724).length < 2 ^ (prefixWord ++ tailWord_931724).sum := by decide
  have hdescent : baseEnd_931724 < baseStart_931724 := by decide
  rcases family_descends (prefixWord ++ tailWord_931724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931741 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_931741 : Nat := 118140960795 + 931741 * 2 ^ 59
def prefixEnd_931741 : Nat := 4983230072969 + 3 ^ 40 * 931741 * 2
def baseEnd_931741 : Nat := 159476992833648097584169

theorem tailTrace_931741 : CollatzResearch.WordTrace tailWord_931741 prefixEnd_931741 159476992833648097584169 := by
  unfold tailWord_931741
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983386117468960539027077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22655590744979307026018051 33983386117468960539027077)
  ·
    refine ⟨6371884897025430101067577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33983386117468960539027077 6371884897025430101067577)
    ·
      refine ⟨4778913672769072575800683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6371884897025430101067577 4778913672769072575800683)
      ·
        refine ⟨7168370509153608863701025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778913672769072575800683 7168370509153608863701025)
        ·
          refine ⟨5376277881865206647775769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7168370509153608863701025 5376277881865206647775769)
          ·
            refine ⟨4032208411398904985831827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376277881865206647775769 4032208411398904985831827)
            ·
              refine ⟨6048312617098357478747741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032208411398904985831827 6048312617098357478747741)
              ·
                refine ⟨2268117231411884054530403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6048312617098357478747741 2268117231411884054530403)
                ·
                  refine ⟨3402175847117826081795605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268117231411884054530403 3402175847117826081795605)
                  ·
                    refine ⟨159476992833648097584169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3402175847117826081795605 159476992833648097584169)
                    ·
                      rfl

theorem cell23_931741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_931741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931741 prefixEnd_931741 := by exact prefixLift 931741
  have htrace : WordTrace (prefixWord ++ tailWord_931741) baseStart_931741 baseEnd_931741 := by
    simpa [prefixWord, tailWord_931741, baseEnd_931741] using wordTrace_append hprefix tailTrace_931741
  have hstable : (prefixWord ++ tailWord_931741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931741).length < 2 ^ (prefixWord ++ tailWord_931741).sum := by decide
  have hdescent : baseEnd_931741 < baseStart_931741 := by decide
  rcases family_descends (prefixWord ++ tailWord_931741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931752 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_931752 : Nat := 118140960795 + 931752 * 2 ^ 59
def prefixEnd_931752 : Nat := 4983230072969 + 3 ^ 40 * 931752 * 2
def baseEnd_931752 : Nat := 478436626788143749714957

theorem tailTrace_931752 : CollatzResearch.WordTrace tailWord_931752 prefixEnd_931752 478436626788143749714957 := by
  unfold tailWord_931752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991893660214554708838755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22655858213619406278451673 16991893660214554708838755)
  ·
    refine ⟨25487840490321832063258133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16991893660214554708838755 25487840490321832063258133)
    ·
      refine ⟨1194742522983835877965225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25487840490321832063258133 1194742522983835877965225)
      ·
        refine ⟨896056892237876908473919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194742522983835877965225 896056892237876908473919)
        ·
          refine ⟨1344085338356815362710879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896056892237876908473919 1344085338356815362710879)
          ·
            refine ⟨2016128007535223044066319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344085338356815362710879 2016128007535223044066319)
            ·
              refine ⟨3024192011302834566099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016128007535223044066319 3024192011302834566099479)
              ·
                refine ⟨4536288016954251849149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024192011302834566099479 4536288016954251849149219)
                ·
                  refine ⟨6804432025431377773723829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536288016954251849149219 6804432025431377773723829)
                  ·
                    refine ⟨637915502384191666286609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6804432025431377773723829 637915502384191666286609)
                    ·
                      refine ⟨478436626788143749714957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637915502384191666286609 478436626788143749714957)
                      ·
                        rfl

theorem cell23_931752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_931752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931752 prefixEnd_931752 := by exact prefixLift 931752
  have htrace : WordTrace (prefixWord ++ tailWord_931752) baseStart_931752 baseEnd_931752 := by
    simpa [prefixWord, tailWord_931752, baseEnd_931752] using wordTrace_append hprefix tailTrace_931752
  have hstable : (prefixWord ++ tailWord_931752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931752).length < 2 ^ (prefixWord ++ tailWord_931752).sum := by decide
  have hdescent : baseEnd_931752 < baseStart_931752 := by decide
  rcases family_descends (prefixWord ++ tailWord_931752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931765 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_931765 : Nat := 118140960795 + 931765 * 2 ^ 59
def prefixEnd_931765 : Nat := 4983230072969 + 3 ^ 40 * 931765 * 2
def baseEnd_931765 : Nat := 478443302036652198852397

theorem tailTrace_931765 : CollatzResearch.WordTrace tailWord_931765 prefixEnd_931765 478443302036652198852397 := by
  unfold tailWord_931765
  simp only [CollatzResearch.WordTrace]
  refine ⟨33984261469382012637900749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22656174312921341758600499 33984261469382012637900749)
  ·
    refine ⟨12744098051018254739212781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33984261469382012637900749 12744098051018254739212781)
    ·
      refine ⟨4779036769131845527204793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12744098051018254739212781 4779036769131845527204793)
      ·
        refine ⟨3584277576848884145403595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4779036769131845527204793 3584277576848884145403595)
        ·
          refine ⟨5376416365273326218105393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584277576848884145403595 5376416365273326218105393)
          ·
            refine ⟨4032312273954994663579045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376416365273326218105393 4032312273954994663579045)
            ·
              refine ⟨756058551366561499421071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4032312273954994663579045 756058551366561499421071)
              ·
                refine ⟨1134087827049842249131607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756058551366561499421071 1134087827049842249131607)
                ·
                  refine ⟨1701131740574763373697411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134087827049842249131607 1701131740574763373697411)
                  ·
                    refine ⟨2551697610862145060546117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701131740574763373697411 2551697610862145060546117)
                    ·
                      refine ⟨478443302036652198852397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2551697610862145060546117 478443302036652198852397)
                      ·
                        rfl

theorem cell23_931765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_931765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931765 prefixEnd_931765 := by exact prefixLift 931765
  have htrace : WordTrace (prefixWord ++ tailWord_931765) baseStart_931765 baseEnd_931765 := by
    simpa [prefixWord, tailWord_931765, baseEnd_931765] using wordTrace_append hprefix tailTrace_931765
  have hstable : (prefixWord ++ tailWord_931765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931765).length < 2 ^ (prefixWord ++ tailWord_931765).sum := by decide
  have hdescent : baseEnd_931765 < baseStart_931765 := by decide
  rcases family_descends (prefixWord ++ tailWord_931765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931768 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_931768 : Nat := 118140960795 + 931768 * 2 ^ 59
def prefixEnd_931768 : Nat := 4983230072969 + 3 ^ 40 * 931768 * 2
def baseEnd_931768 : Nat := 478444842478615687114883

theorem tailTrace_931768 : CollatzResearch.WordTrace tailWord_931768 prefixEnd_931768 478444842478615687114883 := by
  unfold tailWord_931768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992185444185572075129979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22656247258914096100173305 16992185444185572075129979)
  ·
    refine ⟨25488278166278358112694969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16992185444185572075129979 25488278166278358112694969)
    ·
      refine ⟨19116208624708768584521227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25488278166278358112694969 19116208624708768584521227)
      ·
        refine ⟨28674312937063152876781841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19116208624708768584521227 28674312937063152876781841)
        ·
          refine ⟨21505734702797364657586381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28674312937063152876781841 21505734702797364657586381)
          ·
            refine ⟨8064650513549011746594893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21505734702797364657586381 8064650513549011746594893)
            ·
              refine ⟨3024243942580879404973085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064650513549011746594893 3024243942580879404973085)
              ·
                refine ⟨1134091478467829776864907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024243942580879404973085 1134091478467829776864907)
                ·
                  refine ⟨1701137217701744665297361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134091478467829776864907 1701137217701744665297361)
                  ·
                    refine ⟨1275852913276308498973021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1701137217701744665297361 1275852913276308498973021)
                    ·
                      refine ⟨478444842478615687114883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275852913276308498973021 478444842478615687114883)
                      ·
                        rfl

theorem cell23_931768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_931768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931768 prefixEnd_931768 := by exact prefixLift 931768
  have htrace : WordTrace (prefixWord ++ tailWord_931768) baseStart_931768 baseEnd_931768 := by
    simpa [prefixWord, tailWord_931768, baseEnd_931768] using wordTrace_append hprefix tailTrace_931768
  have hstable : (prefixWord ++ tailWord_931768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931768).length < 2 ^ (prefixWord ++ tailWord_931768).sum := by decide
  have hdescent : baseEnd_931768 < baseStart_931768 := by decide
  rcases family_descends (prefixWord ++ tailWord_931768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931805 : List Nat := [1, 4, 3, 1, 3, 2, 2, 7]
def baseStart_931805 : Nat := 118140960795 + 931805 * 2 ^ 59
def prefixEnd_931805 : Nat := 4983230072969 + 3 ^ 40 * 931805 * 2
def baseEnd_931805 : Nat := 17720883009734520087119

theorem tailTrace_931805 : CollatzResearch.WordTrace tailWord_931805 prefixEnd_931805 17720883009734520087119 := by
  unfold tailWord_931805
  simp only [CollatzResearch.WordTrace]
  refine ⟨33985720389237099469356869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22657146926158066312904579 33985720389237099469356869)
  ·
    refine ⟨6372322572981956150504413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33985720389237099469356869 6372322572981956150504413)
    ·
      refine ⟨2389620964868233556439155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6372322572981956150504413 2389620964868233556439155)
      ·
        refine ⟨3584431447302350334658733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389620964868233556439155 3584431447302350334658733)
        ·
          refine ⟨1344161792738381375497025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3584431447302350334658733 1344161792738381375497025)
          ·
            refine ⟨1008121344553786031622769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344161792738381375497025 1008121344553786031622769)
            ·
              refine ⟨756091008415339523717077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008121344553786031622769 756091008415339523717077)
              ·
                refine ⟨17720883009734520087119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 756091008415339523717077 17720883009734520087119)
                ·
                  rfl

theorem cell23_931805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 7].length) (baseStart_931805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931805 prefixEnd_931805 := by exact prefixLift 931805
  have htrace : WordTrace (prefixWord ++ tailWord_931805) baseStart_931805 baseEnd_931805 := by
    simpa [prefixWord, tailWord_931805, baseEnd_931805] using wordTrace_append hprefix tailTrace_931805
  have hstable : (prefixWord ++ tailWord_931805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931805).length < 2 ^ (prefixWord ++ tailWord_931805).sum := by decide
  have hdescent : baseEnd_931805 < baseStart_931805 := by decide
  rcases family_descends (prefixWord ++ tailWord_931805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2]
def baseStart_931808 : Nat := 118140960795 + 931808 * 2 ^ 59
def prefixEnd_931808 : Nat := 4983230072969 + 3 ^ 40 * 931808 * 2
def baseEnd_931808 : Nat := 478465381704795530614699

theorem tailTrace_931808 : CollatzResearch.WordTrace tailWord_931808 prefixEnd_931808 478465381704795530614699 := by
  unfold tailWord_931808
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992914904113115490858039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22657219872150820654477385 16992914904113115490858039)
  ·
    refine ⟨25489372356169673236287059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16992914904113115490858039 25489372356169673236287059)
    ·
      refine ⟨38234058534254509854430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25489372356169673236287059 38234058534254509854430589)
      ·
        refine ⟨14337771950345441195411471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38234058534254509854430589 14337771950345441195411471)
        ·
          refine ⟨21506657925518161793117207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337771950345441195411471 21506657925518161793117207)
          ·
            refine ⟨32259986888277242689675811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21506657925518161793117207 32259986888277242689675811)
            ·
              refine ⟨48389980332415864034513717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32259986888277242689675811 48389980332415864034513717)
              ·
                refine ⟨4536560656163987253235661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48389980332415864034513717 4536560656163987253235661)
                ·
                  refine ⟨1701210246061495219963373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4536560656163987253235661 1701210246061495219963373)
                  ·
                    refine ⟨637953842273060707486265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701210246061495219963373 637953842273060707486265)
                    ·
                      refine ⟨478465381704795530614699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 637953842273060707486265 478465381704795530614699)
                      ·
                        rfl

theorem cell23_931808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_931808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931808 prefixEnd_931808 := by exact prefixLift 931808
  have htrace : WordTrace (prefixWord ++ tailWord_931808) baseStart_931808 baseEnd_931808 := by
    simpa [prefixWord, tailWord_931808, baseEnd_931808] using wordTrace_append hprefix tailTrace_931808
  have hstable : (prefixWord ++ tailWord_931808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931808).length < 2 ^ (prefixWord ++ tailWord_931808).sum := by decide
  have hdescent : baseEnd_931808 < baseStart_931808 := by decide
  rcases family_descends (prefixWord ++ tailWord_931808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931811 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_931811 : Nat := 118140960795 + 931811 * 2 ^ 59
def prefixEnd_931811 : Nat := 4983230072969 + 3 ^ 40 * 931811 * 2
def baseEnd_931811 : Nat := 478466922146759018877185

theorem tailTrace_931811 : CollatzResearch.WordTrace tailWord_931811 prefixEnd_931811 478466922146759018877185 := by
  unfold tailWord_931811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33985939227215362494075287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22657292818143574996050191 33985939227215362494075287)
  ·
    refine ⟨50978908840823043741112931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33985939227215362494075287 50978908840823043741112931)
    ·
      refine ⟨76468363261234565611669397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50978908840823043741112931 76468363261234565611669397)
      ·
        refine ⟨3584454527870370263047003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76468363261234565611669397 3584454527870370263047003)
        ·
          refine ⟨5376681791805555394570505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584454527870370263047003 5376681791805555394570505)
          ·
            refine ⟨4032511343854166545927879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376681791805555394570505 4032511343854166545927879)
            ·
              refine ⟨6048767015781249818891819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032511343854166545927879 6048767015781249818891819)
              ·
                refine ⟨9073150523671874728337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048767015781249818891819 9073150523671874728337729)
                ·
                  refine ⟨6804862892753906046253297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9073150523671874728337729 6804862892753906046253297)
                  ·
                    refine ⟨5103647169565429534689973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6804862892753906046253297 5103647169565429534689973)
                    ·
                      refine ⟨478466922146759018877185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5103647169565429534689973 478466922146759018877185)
                      ·
                        rfl

theorem cell23_931811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_931811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931811 prefixEnd_931811 := by exact prefixLift 931811
  have htrace : WordTrace (prefixWord ++ tailWord_931811) baseStart_931811 baseEnd_931811 := by
    simpa [prefixWord, tailWord_931811, baseEnd_931811] using wordTrace_append hprefix tailTrace_931811
  have hstable : (prefixWord ++ tailWord_931811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931811).length < 2 ^ (prefixWord ++ tailWord_931811).sum := by decide
  have hdescent : baseEnd_931811 < baseStart_931811 := by decide
  rcases family_descends (prefixWord ++ tailWord_931811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931841 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_931841 : Nat := 118140960795 + 931841 * 2 ^ 59
def prefixEnd_931841 : Nat := 4983230072969 + 3 ^ 40 * 931841 * 2
def baseEnd_931841 : Nat := 478482326566393901502047

theorem tailTrace_931841 : CollatzResearch.WordTrace tailWord_931841 prefixEnd_931841 478482326566393901502047 := by
  unfold tailWord_931841
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987033417106677617667377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22658022278071118411778251 33987033417106677617667377)
  ·
    refine ⟨25490275062830008213250533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33987033417106677617667377 25490275062830008213250533)
    ·
      refine ⟨4779426574280626539984475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25490275062830008213250533 4779426574280626539984475)
      ·
        refine ⟨7169139861420939809976713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779426574280626539984475 7169139861420939809976713)
        ·
          refine ⟨5376854896065704857482535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7169139861420939809976713 5376854896065704857482535)
          ·
            refine ⟨8065282344098557286223803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376854896065704857482535 8065282344098557286223803)
            ·
              refine ⟨12097923516147835929335705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065282344098557286223803 12097923516147835929335705)
              ·
                refine ⟨9073442637110876947001779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12097923516147835929335705 9073442637110876947001779)
                ·
                  refine ⟨13610163955666315420502669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073442637110876947001779 13610163955666315420502669)
                  ·
                    refine ⟨5103811483374868282688501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13610163955666315420502669 5103811483374868282688501)
                    ·
                      refine ⟨478482326566393901502047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5103811483374868282688501 478482326566393901502047)
                      ·
                        rfl

theorem cell23_931841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_931841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931841 prefixEnd_931841 := by exact prefixLift 931841
  have htrace : WordTrace (prefixWord ++ tailWord_931841) baseStart_931841 baseEnd_931841 := by
    simpa [prefixWord, tailWord_931841, baseEnd_931841] using wordTrace_append hprefix tailTrace_931841
  have hstable : (prefixWord ++ tailWord_931841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931841).length < 2 ^ (prefixWord ++ tailWord_931841).sum := by decide
  have hdescent : baseEnd_931841 < baseStart_931841 := by decide
  rcases family_descends (prefixWord ++ tailWord_931841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931851 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_931851 : Nat := 118140960795 + 931851 * 2 ^ 59
def prefixEnd_931851 : Nat := 4983230072969 + 3 ^ 40 * 931851 * 2
def baseEnd_931851 : Nat := 478487461372938862377001

theorem tailTrace_931851 : CollatzResearch.WordTrace tailWord_931851 prefixEnd_931851 478487461372938862377001 := by
  unfold tailWord_931851
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987398147070449325531407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22658265431380299550354271 33987398147070449325531407)
  ·
    refine ⟨50981097220605673988297111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33987398147070449325531407 50981097220605673988297111)
    ·
      refine ⟨76471645830908510982445667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50981097220605673988297111 76471645830908510982445667)
      ·
        refine ⟨114707468746362766473668501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76471645830908510982445667 114707468746362766473668501)
        ·
          refine ⟨5376912597485754678453211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114707468746362766473668501 5376912597485754678453211)
          ·
            refine ⟨8065368896228632017679817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376912597485754678453211 8065368896228632017679817)
            ·
              refine ⟨6049026672171474013259863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065368896228632017679817 6049026672171474013259863)
              ·
                refine ⟨9073540008257211019889795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049026672171474013259863 9073540008257211019889795)
                ·
                  refine ⟨13610310012385816529834693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073540008257211019889795 13610310012385816529834693)
                  ·
                    refine ⟨2551933127322340599344005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13610310012385816529834693 2551933127322340599344005)
                    ·
                      refine ⟨478487461372938862377001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2551933127322340599344005 478487461372938862377001)
                      ·
                        rfl

theorem cell23_931851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_931851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931851 prefixEnd_931851 := by exact prefixLift 931851
  have htrace : WordTrace (prefixWord ++ tailWord_931851) baseStart_931851 baseEnd_931851 := by
    simpa [prefixWord, tailWord_931851, baseEnd_931851] using wordTrace_append hprefix tailTrace_931851
  have hstable : (prefixWord ++ tailWord_931851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931851).length < 2 ^ (prefixWord ++ tailWord_931851).sum := by decide
  have hdescent : baseEnd_931851 < baseStart_931851 := by decide
  rcases family_descends (prefixWord ++ tailWord_931851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931853 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_931853 : Nat := 118140960795 + 931853 * 2 ^ 59
def prefixEnd_931853 : Nat := 4983230072969 + 3 ^ 40 * 931853 * 2
def baseEnd_931853 : Nat := 478488488334247854551993

theorem tailTrace_931853 : CollatzResearch.WordTrace tailWord_931853 prefixEnd_931853 478488488334247854551993 := by
  unfold tailWord_931853
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987471093063203667104213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22658314062042135778069475 33987471093063203667104213)
  ·
    refine ⟨796581353743668835947755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33987471093063203667104213 796581353743668835947755)
    ·
      refine ⟨1194872030615503253921633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796581353743668835947755 1194872030615503253921633)
      ·
        refine ⟨896154022961627440441225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194872030615503253921633 896154022961627440441225)
        ·
          refine ⟨672115517221220580330919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896154022961627440441225 672115517221220580330919)
          ·
            refine ⟨1008173275831830870496379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672115517221220580330919 1008173275831830870496379)
            ·
              refine ⟨1512259913747746305744569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008173275831830870496379 1512259913747746305744569)
              ·
                refine ⟨1134194935310809729308427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512259913747746305744569 1134194935310809729308427)
                ·
                  refine ⟨1701292402966214593962641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134194935310809729308427 1701292402966214593962641)
                  ·
                    refine ⟨1275969302224660945471981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1701292402966214593962641 1275969302224660945471981)
                    ·
                      refine ⟨478488488334247854551993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1275969302224660945471981 478488488334247854551993)
                      ·
                        rfl

theorem cell23_931853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_931853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931853 prefixEnd_931853 := by exact prefixLift 931853
  have htrace : WordTrace (prefixWord ++ tailWord_931853) baseStart_931853 baseEnd_931853 := by
    simpa [prefixWord, tailWord_931853, baseEnd_931853] using wordTrace_append hprefix tailTrace_931853
  have hstable : (prefixWord ++ tailWord_931853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931853).length < 2 ^ (prefixWord ++ tailWord_931853).sum := by decide
  have hdescent : baseEnd_931853 < baseStart_931853 := by decide
  rcases family_descends (prefixWord ++ tailWord_931853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931895 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 5]
def baseStart_931895 : Nat := 118140960795 + 931895 * 2 ^ 59
def prefixEnd_931895 : Nat := 4983230072969 + 3 ^ 40 * 931895 * 2
def baseEnd_931895 : Nat := 53167783835748521136311

theorem tailTrace_931895 : CollatzResearch.WordTrace tailWord_931895 prefixEnd_931895 53167783835748521136311 := by
  unfold tailWord_931895
  simp only [CollatzResearch.WordTrace]
  refine ⟨33989002958911044840133139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22659335305940696560088759 33989002958911044840133139)
  ·
    refine ⟨50983504438366567260199709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33989002958911044840133139 50983504438366567260199709)
    ·
      refine ⟨19118814164387462722574891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50983504438366567260199709 19118814164387462722574891)
      ·
        refine ⟨28678221246581194083862337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19118814164387462722574891 28678221246581194083862337)
        ·
          refine ⟨21508665934935895562896753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28678221246581194083862337 21508665934935895562896753)
          ·
            refine ⟨16131499451201921672172565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508665934935895562896753 16131499451201921672172565)
            ·
              refine ⟨756164036775090078383089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16131499451201921672172565 756164036775090078383089)
              ·
                refine ⟨567123027581317558787317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756164036775090078383089 567123027581317558787317)
                ·
                  refine ⟨53167783835748521136311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 567123027581317558787317 53167783835748521136311)
                  ·
                    rfl

theorem cell23_931895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 5].length) (baseStart_931895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931895 prefixEnd_931895 := by exact prefixLift 931895
  have htrace : WordTrace (prefixWord ++ tailWord_931895) baseStart_931895 baseEnd_931895 := by
    simpa [prefixWord, tailWord_931895, baseEnd_931895] using wordTrace_append hprefix tailTrace_931895
  have hstable : (prefixWord ++ tailWord_931895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931895).length < 2 ^ (prefixWord ++ tailWord_931895).sum := by decide
  have hdescent : baseEnd_931895 < baseStart_931895 := by decide
  rcases family_descends (prefixWord ++ tailWord_931895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931905 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_931905 : Nat := 118140960795 + 931905 * 2 ^ 59
def prefixEnd_931905 : Nat := 4983230072969 + 3 ^ 40 * 931905 * 2
def baseEnd_931905 : Nat := 478515189328281651101753

theorem tailTrace_931905 : CollatzResearch.WordTrace tailWord_931905 prefixEnd_931905 478515189328281651101753 := by
  unfold tailWord_931905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33989367688874816547997169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22659578459249877698664779 33989367688874816547997169)
  ·
    refine ⟨25492025766656112410997877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33989367688874816547997169 25492025766656112410997877)
    ·
      refine ⟨2389877415624010538531051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25492025766656112410997877 2389877415624010538531051)
      ·
        refine ⟨3584816123436015807796577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389877415624010538531051 3584816123436015807796577)
        ·
          refine ⟨2688612092577011855847433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584816123436015807796577 2688612092577011855847433)
          ·
            refine ⟨2016459069432758891885575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688612092577011855847433 2016459069432758891885575)
            ·
              refine ⟨3024688604149138337828363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016459069432758891885575 3024688604149138337828363)
              ·
                refine ⟨4537032906223707506742545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024688604149138337828363 4537032906223707506742545)
                ·
                  refine ⟨3402774679667780630056909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537032906223707506742545 3402774679667780630056909)
                  ·
                    refine ⟨1276040504875417736271341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402774679667780630056909 1276040504875417736271341)
                    ·
                      refine ⟨478515189328281651101753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276040504875417736271341 478515189328281651101753)
                      ·
                        rfl

theorem cell23_931905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_931905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931905 prefixEnd_931905 := by exact prefixLift 931905
  have htrace : WordTrace (prefixWord ++ tailWord_931905) baseStart_931905 baseEnd_931905 := by
    simpa [prefixWord, tailWord_931905, baseEnd_931905] using wordTrace_append hprefix tailTrace_931905
  have hstable : (prefixWord ++ tailWord_931905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931905).length < 2 ^ (prefixWord ++ tailWord_931905).sum := by decide
  have hdescent : baseEnd_931905 < baseStart_931905 := by decide
  rcases family_descends (prefixWord ++ tailWord_931905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931925 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_931925 : Nat := 118140960795 + 931925 * 2 ^ 59
def prefixEnd_931925 : Nat := 4983230072969 + 3 ^ 40 * 931925 * 2
def baseEnd_931925 : Nat := 159508486313790524283887

theorem tailTrace_931925 : CollatzResearch.WordTrace tailWord_931925 prefixEnd_931925 159508486313790524283887 := by
  unfold tailWord_931925
  simp only [CollatzResearch.WordTrace]
  refine ⟨33990097148802359963725229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22660064765868239975816819 33990097148802359963725229)
  ·
    refine ⟨12746286430800884986396961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33990097148802359963725229 12746286430800884986396961)
    ·
      refine ⟨9559714823100663739797721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12746286430800884986396961 9559714823100663739797721)
      ·
        refine ⟨7169786117325497804848291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9559714823100663739797721 7169786117325497804848291)
        ·
          refine ⟨10754679175988246707272437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169786117325497804848291 10754679175988246707272437)
          ·
            refine ⟨1008251172748898128806791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10754679175988246707272437 1008251172748898128806791)
            ·
              refine ⟨1512376759123347193210187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008251172748898128806791 1512376759123347193210187)
              ·
                refine ⟨2268565138685020789815281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512376759123347193210187 2268565138685020789815281)
                ·
                  refine ⟨1701423854013765592361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2268565138685020789815281 1701423854013765592361461)
                  ·
                    refine ⟨159508486313790524283887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1701423854013765592361461 159508486313790524283887)
                    ·
                      rfl

theorem cell23_931925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_931925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931925 prefixEnd_931925 := by exact prefixLift 931925
  have htrace : WordTrace (prefixWord ++ tailWord_931925) baseStart_931925 baseEnd_931925 := by
    simpa [prefixWord, tailWord_931925, baseEnd_931925] using wordTrace_append hprefix tailTrace_931925
  have hstable : (prefixWord ++ tailWord_931925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931925).length < 2 ^ (prefixWord ++ tailWord_931925).sum := by decide
  have hdescent : baseEnd_931925 < baseStart_931925 := by decide
  rcases family_descends (prefixWord ++ tailWord_931925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931928 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_931928 : Nat := 118140960795 + 931928 * 2 ^ 59
def prefixEnd_931928 : Nat := 4983230072969 + 3 ^ 40 * 931928 * 2
def baseEnd_931928 : Nat := 478526999383335061114147

theorem tailTrace_931928 : CollatzResearch.WordTrace tailWord_931928 prefixEnd_931928 478526999383335061114147 := by
  unfold tailWord_931928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16995103283895745738042219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22660137711860994317389625 16995103283895745738042219)
  ·
    refine ⟨25492654925843618607063329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16995103283895745738042219 25492654925843618607063329)
    ·
      refine ⟨19119491194382713955297497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25492654925843618607063329 19119491194382713955297497)
      ·
        refine ⟨14339618395787035466473123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19119491194382713955297497 14339618395787035466473123)
        ·
          refine ⟨21509427593680553199709685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339618395787035466473123 21509427593680553199709685)
          ·
            refine ⟨2016508836907551862472783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21509427593680553199709685 2016508836907551862472783)
            ·
              refine ⟨3024763255361327793709175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016508836907551862472783 3024763255361327793709175)
              ·
                refine ⟨4537144883041991690563763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024763255361327793709175 4537144883041991690563763)
                ·
                  refine ⟨6805717324562987535845645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537144883041991690563763 6805717324562987535845645)
                  ·
                    refine ⟨2552143996711120325942117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6805717324562987535845645 2552143996711120325942117)
                    ·
                      refine ⟨478526999383335061114147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2552143996711120325942117 478526999383335061114147)
                      ·
                        rfl

theorem cell23_931928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_931928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_931928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_931928 prefixEnd_931928 := by exact prefixLift 931928
  have htrace : WordTrace (prefixWord ++ tailWord_931928) baseStart_931928 baseEnd_931928 := by
    simpa [prefixWord, tailWord_931928, baseEnd_931928] using wordTrace_append hprefix tailTrace_931928
  have hstable : (prefixWord ++ tailWord_931928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931928).length < 2 ^ (prefixWord ++ tailWord_931928).sum := by decide
  have hdescent : baseEnd_931928 < baseStart_931928 := by decide
  rcases family_descends (prefixWord ++ tailWord_931928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932032 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_932032 : Nat := 118140960795 + 932032 * 2 ^ 59
def prefixEnd_932032 : Nat := 4983230072969 + 3 ^ 40 * 932032 * 2
def baseEnd_932032 : Nat := 159526800457134218071223

theorem tailTrace_932032 : CollatzResearch.WordTrace tailWord_932032 prefixEnd_932032 159526800457134218071223 := by
  unfold tailWord_932032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996999879707358618935175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22662666506276478158580233 16996999879707358618935175)
  ·
    refine ⟨25495499819561037928402763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16996999879707358618935175 25495499819561037928402763)
    ·
      refine ⟨38243249729341556892604145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495499819561037928402763 38243249729341556892604145)
      ·
        refine ⟨28682437297006167669453109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38243249729341556892604145 28682437297006167669453109)
        ·
          refine ⟨2688978496594328219011229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28682437297006167669453109 2688978496594328219011229)
          ·
            refine ⟨1008366936222873082129211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2688978496594328219011229 1008366936222873082129211)
            ·
              refine ⟨1512550404334309623193817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008366936222873082129211 1512550404334309623193817)
              ·
                refine ⟨1134412803250732217395363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512550404334309623193817 1134412803250732217395363)
                ·
                  refine ⟨1701619204876098326093045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134412803250732217395363 1701619204876098326093045)
                  ·
                    refine ⟨159526800457134218071223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1701619204876098326093045 159526800457134218071223)
                    ·
                      rfl

theorem cell23_932032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_932032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932032 prefixEnd_932032 := by exact prefixLift 932032
  have htrace : WordTrace (prefixWord ++ tailWord_932032) baseStart_932032 baseEnd_932032 := by
    simpa [prefixWord, tailWord_932032, baseEnd_932032] using wordTrace_append hprefix tailTrace_932032
  have hstable : (prefixWord ++ tailWord_932032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932032).length < 2 ^ (prefixWord ++ tailWord_932032).sum := by decide
  have hdescent : baseEnd_932032 < baseStart_932032 := by decide
  rcases family_descends (prefixWord ++ tailWord_932032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932082 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_932082 : Nat := 118140960795 + 932082 * 2 ^ 59
def prefixEnd_932082 : Nat := 4983230072969 + 3 ^ 40 * 932082 * 2
def baseEnd_932082 : Nat := 478606075404127458588439

theorem tailTrace_932082 : CollatzResearch.WordTrace tailWord_932082 prefixEnd_932082 478606075404127458588439 := by
  unfold tailWord_932082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498955852308393944297625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22663882272822383851460333 8498955852308393944297625)
  ·
    refine ⟨6374216889231295458223219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8498955852308393944297625 6374216889231295458223219)
    ·
      refine ⟨9561325333846943187334829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374216889231295458223219 9561325333846943187334829)
      ·
        refine ⟨3585497000192603695250561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9561325333846943187334829 3585497000192603695250561)
        ·
          refine ⟨2689122750144452771437921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3585497000192603695250561 2689122750144452771437921)
          ·
            refine ⟨2016842062608339578578441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2689122750144452771437921 2016842062608339578578441)
            ·
              refine ⟨1512631546956254683933831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016842062608339578578441 1512631546956254683933831)
              ·
                refine ⟨2268947320434382025900747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512631546956254683933831 2268947320434382025900747)
                ·
                  refine ⟨3403420980651573038851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268947320434382025900747 3403420980651573038851121)
                  ·
                    refine ⟨2552565735488679779138341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3403420980651573038851121 2552565735488679779138341)
                    ·
                      refine ⟨478606075404127458588439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2552565735488679779138341 478606075404127458588439)
                      ·
                        rfl

theorem cell23_932082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_932082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932082 prefixEnd_932082 := by exact prefixLift 932082
  have htrace : WordTrace (prefixWord ++ tailWord_932082) baseStart_932082 baseEnd_932082 := by
    simpa [prefixWord, tailWord_932082, baseEnd_932082] using wordTrace_append hprefix tailTrace_932082
  have hstable : (prefixWord ++ tailWord_932082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932082).length < 2 ^ (prefixWord ++ tailWord_932082).sum := by decide
  have hdescent : baseEnd_932082 < baseStart_932082 := by decide
  rcases family_descends (prefixWord ++ tailWord_932082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932103 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_932103 : Nat := 118140960795 + 932103 * 2 ^ 59
def prefixEnd_932103 : Nat := 4983230072969 + 3 ^ 40 * 932103 * 2
def baseEnd_932103 : Nat := 478616858497871876425843

theorem tailTrace_932103 : CollatzResearch.WordTrace tailWord_932103 prefixEnd_932103 478616858497871876425843 := by
  unfold tailWord_932103
  simp only [CollatzResearch.WordTrace]
  refine ⟨33996589342157496363704963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22664392894771664242469975 33996589342157496363704963)
  ·
    refine ⟨50994884013236244545557445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33996589342157496363704963 50994884013236244545557445)
    ·
      refine ⟨9561540752481795852292021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50994884013236244545557445 9561540752481795852292021)
      ·
        refine ⟨896394445545168361152377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9561540752481795852292021 896394445545168361152377)
        ·
          refine ⟨672295834158876270864283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896394445545168361152377 672295834158876270864283)
          ·
            refine ⟨1008443751238314406296425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672295834158876270864283 1008443751238314406296425)
            ·
              refine ⟨756332813428735804722319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008443751238314406296425 756332813428735804722319)
              ·
                refine ⟨1134499220143103707083479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756332813428735804722319 1134499220143103707083479)
                ·
                  refine ⟨1701748830214655560625219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134499220143103707083479 1701748830214655560625219)
                  ·
                    refine ⟨2552623245321983340937829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701748830214655560625219 2552623245321983340937829)
                    ·
                      refine ⟨478616858497871876425843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2552623245321983340937829 478616858497871876425843)
                      ·
                        rfl

theorem cell23_932103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_932103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932103 prefixEnd_932103 := by exact prefixLift 932103
  have htrace : WordTrace (prefixWord ++ tailWord_932103) baseStart_932103 baseEnd_932103 := by
    simpa [prefixWord, tailWord_932103, baseEnd_932103] using wordTrace_append hprefix tailTrace_932103
  have hstable : (prefixWord ++ tailWord_932103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932103).length < 2 ^ (prefixWord ++ tailWord_932103).sum := by decide
  have hdescent : baseEnd_932103 < baseStart_932103 := by decide
  rcases family_descends (prefixWord ++ tailWord_932103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932119 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_932119 : Nat := 118140960795 + 932119 * 2 ^ 59
def prefixEnd_932119 : Nat := 4983230072969 + 3 ^ 40 * 932119 * 2
def baseEnd_932119 : Nat := 478625074188343813825769

theorem tailTrace_932119 : CollatzResearch.WordTrace tailWord_932119 prefixEnd_932119 478625074188343813825769 := by
  unfold tailWord_932119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33997172910099531096287411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22664781940066354064191607 33997172910099531096287411)
  ·
    refine ⟨50995759365149296644431117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33997172910099531096287411 50995759365149296644431117)
    ·
      refine ⟨19123409761930986241661669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50995759365149296644431117 19123409761930986241661669)
      ·
        refine ⟨3585639330362059920311563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19123409761930986241661669 3585639330362059920311563)
        ·
          refine ⟨5378458995543089880467345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585639330362059920311563 5378458995543089880467345)
          ·
            refine ⟨4033844246657317410350509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378458995543089880467345 4033844246657317410350509)
            ·
              refine ⟨1512691592496494028881441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4033844246657317410350509 1512691592496494028881441)
              ·
                refine ⟨1134518694372370521661081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512691592496494028881441 1134518694372370521661081)
                ·
                  refine ⟨850889020779277891245811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134518694372370521661081 850889020779277891245811)
                  ·
                    refine ⟨1276333531168916836868717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 850889020779277891245811 1276333531168916836868717)
                    ·
                      refine ⟨478625074188343813825769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276333531168916836868717 478625074188343813825769)
                      ·
                        rfl

theorem cell23_932119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_932119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932119 prefixEnd_932119 := by exact prefixLift 932119
  have htrace : WordTrace (prefixWord ++ tailWord_932119) baseStart_932119 baseEnd_932119 := by
    simpa [prefixWord, tailWord_932119, baseEnd_932119] using wordTrace_append hprefix tailTrace_932119
  have hstable : (prefixWord ++ tailWord_932119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932119).length < 2 ^ (prefixWord ++ tailWord_932119).sum := by decide
  have hdescent : baseEnd_932119 < baseStart_932119 := by decide
  rcases family_descends (prefixWord ++ tailWord_932119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932136 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_932136 : Nat := 118140960795 + 932136 * 2 ^ 59
def prefixEnd_932136 : Nat := 4983230072969 + 3 ^ 40 * 932136 * 2
def baseEnd_932136 : Nat := 478633803359470247313191

theorem tailTrace_932136 : CollatzResearch.WordTrace tailWord_932136 prefixEnd_932136 478633803359470247313191 := by
  unfold tailWord_932136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16998896475518971499828131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22665195300691961999770841 16998896475518971499828131)
  ·
    refine ⟨25498344713278457249742197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16998896475518971499828131 25498344713278457249742197)
    ·
      refine ⟨2390469816869855367163331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25498344713278457249742197 2390469816869855367163331)
      ·
        refine ⟨3585704725304783050744997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390469816869855367163331 3585704725304783050744997)
        ·
          refine ⟨672319635994646822014687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3585704725304783050744997 672319635994646822014687)
          ·
            refine ⟨1008479453991970233022031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672319635994646822014687 1008479453991970233022031)
            ·
              refine ⟨1512719180987955349533047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008479453991970233022031 1512719180987955349533047)
              ·
                refine ⟨2269078771481933024299571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512719180987955349533047 2269078771481933024299571)
                ·
                  refine ⟨3403618157222899536449357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269078771481933024299571 3403618157222899536449357)
                  ·
                    refine ⟨1276356808958587326168509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403618157222899536449357 1276356808958587326168509)
                    ·
                      refine ⟨478633803359470247313191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276356808958587326168509 478633803359470247313191)
                      ·
                        rfl

theorem cell23_932136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_932136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932136 prefixEnd_932136 := by exact prefixLift 932136
  have htrace : WordTrace (prefixWord ++ tailWord_932136) baseStart_932136 baseEnd_932136 := by
    simpa [prefixWord, tailWord_932136, baseEnd_932136] using wordTrace_append hprefix tailTrace_932136
  have hstable : (prefixWord ++ tailWord_932136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932136).length < 2 ^ (prefixWord ++ tailWord_932136).sum := by decide
  have hdescent : baseEnd_932136 < baseStart_932136 := by decide
  rcases family_descends (prefixWord ++ tailWord_932136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932146 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_932146 : Nat := 118140960795 + 932146 * 2 ^ 59
def prefixEnd_932146 : Nat := 4983230072969 + 3 ^ 40 * 932146 * 2
def baseEnd_932146 : Nat := 478638938166015208188145

theorem tailTrace_932146 : CollatzResearch.WordTrace tailWord_932146 prefixEnd_932146 478638938166015208188145 := by
  unfold tailWord_932146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499539420250428676880073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22665438454001143138346861 8499539420250428676880073)
  ·
    refine ⟨6374654565187821507660055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8499539420250428676880073 6374654565187821507660055)
    ·
      refine ⟨9561981847781732261490083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374654565187821507660055 9561981847781732261490083)
      ·
        refine ⟨14342972771672598392235125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9561981847781732261490083 14342972771672598392235125)
        ·
          refine ⟨1344653697344306099272043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14342972771672598392235125 1344653697344306099272043)
          ·
            refine ⟨2016980546016459148908065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344653697344306099272043 2016980546016459148908065)
            ·
              refine ⟨1512735409512344361681049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016980546016459148908065 1512735409512344361681049)
              ·
                refine ⟨1134551557134258271260787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512735409512344361681049 1134551557134258271260787)
                ·
                  refine ⟨1701827335701387406891181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134551557134258271260787 1701827335701387406891181)
                  ·
                    refine ⟨638185250888020277584193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701827335701387406891181 638185250888020277584193)
                    ·
                      refine ⟨478638938166015208188145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638185250888020277584193 478638938166015208188145)
                      ·
                        rfl

theorem cell23_932146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_932146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932146 prefixEnd_932146 := by exact prefixLift 932146
  have htrace : WordTrace (prefixWord ++ tailWord_932146) baseStart_932146 baseEnd_932146 := by
    simpa [prefixWord, tailWord_932146, baseEnd_932146] using wordTrace_append hprefix tailTrace_932146
  have hstable : (prefixWord ++ tailWord_932146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932146).length < 2 ^ (prefixWord ++ tailWord_932146).sum := by decide
  have hdescent : baseEnd_932146 < baseStart_932146 := by decide
  rcases family_descends (prefixWord ++ tailWord_932146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932175 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_932175 : Nat := 118140960795 + 932175 * 2 ^ 59
def prefixEnd_932175 : Nat := 4983230072969 + 3 ^ 40 * 932175 * 2
def baseEnd_932175 : Nat := 478653829104995594725511

theorem tailTrace_932175 : CollatzResearch.WordTrace tailWord_932175 prefixEnd_932175 478653829104995594725511 := by
  unfold tailWord_932175
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999215397896652660325979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22666143598597768440217319 33999215397896652660325979)
  ·
    refine ⟨50998823096844978990488969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33999215397896652660325979 50998823096844978990488969)
    ·
      refine ⟨38249117322633734242866727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50998823096844978990488969 38249117322633734242866727)
      ·
        refine ⟨57373675983950601364300091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38249117322633734242866727 57373675983950601364300091)
        ·
          refine ⟨86060513975925902046450137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57373675983950601364300091 86060513975925902046450137)
          ·
            refine ⟨64545385481944426534837603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86060513975925902046450137 64545385481944426534837603)
            ·
              refine ⟨96818078222916639802256405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64545385481944426534837603 96818078222916639802256405)
              ·
                refine ⟨4538347416699217490730769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96818078222916639802256405 4538347416699217490730769)
                ·
                  refine ⟨3403760562524413118048077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538347416699217490730769 3403760562524413118048077)
                  ·
                    refine ⟨1276410210946654919268029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403760562524413118048077 1276410210946654919268029)
                    ·
                      refine ⟨478653829104995594725511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276410210946654919268029 478653829104995594725511)
                      ·
                        rfl

theorem cell23_932175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_932175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932175 prefixEnd_932175 := by exact prefixLift 932175
  have htrace : WordTrace (prefixWord ++ tailWord_932175) baseStart_932175 baseEnd_932175 := by
    simpa [prefixWord, tailWord_932175, baseEnd_932175] using wordTrace_append hprefix tailTrace_932175
  have hstable : (prefixWord ++ tailWord_932175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932175).length < 2 ^ (prefixWord ++ tailWord_932175).sum := by decide
  have hdescent : baseEnd_932175 < baseStart_932175 := by decide
  rcases family_descends (prefixWord ++ tailWord_932175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932195 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 4, 5]
def baseStart_932195 : Nat := 118140960795 + 932195 * 2 ^ 59
def prefixEnd_932195 : Nat := 4983230072969 + 3 ^ 40 * 932195 * 2
def baseEnd_932195 : Nat := 159554699572695172158473

theorem tailTrace_932195 : CollatzResearch.WordTrace tailWord_932195 prefixEnd_932195 159554699572695172158473 := by
  unfold tailWord_932195
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999944857824196076054039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22666629905216130717369359 33999944857824196076054039)
  ·
    refine ⟨50999917286736294114081059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33999944857824196076054039 50999917286736294114081059)
    ·
      refine ⟨76499875930104441171121589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50999917286736294114081059 76499875930104441171121589)
      ·
        refine ⟨7171863368447291359792649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76499875930104441171121589 7171863368447291359792649)
        ·
          refine ⟨5378897526335468519844487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7171863368447291359792649 5378897526335468519844487)
          ·
            refine ⟨8068346289503202779766731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378897526335468519844487 8068346289503202779766731)
            ·
              refine ⟨12102519434254804169650097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068346289503202779766731 12102519434254804169650097)
              ·
                refine ⟨9076889575691103127237573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102519434254804169650097 9076889575691103127237573)
                ·
                  refine ⟨1701916795442081836357045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9076889575691103127237573 1701916795442081836357045)
                  ·
                    refine ⟨159554699572695172158473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1701916795442081836357045 159554699572695172158473)
                    ·
                      rfl

theorem cell23_932195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].length) (baseStart_932195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932195 prefixEnd_932195 := by exact prefixLift 932195
  have htrace : WordTrace (prefixWord ++ tailWord_932195) baseStart_932195 baseEnd_932195 := by
    simpa [prefixWord, tailWord_932195, baseEnd_932195] using wordTrace_append hprefix tailTrace_932195
  have hstable : (prefixWord ++ tailWord_932195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932195).length < 2 ^ (prefixWord ++ tailWord_932195).sum := by decide
  have hdescent : baseEnd_932195 < baseStart_932195 := by decide
  rcases family_descends (prefixWord ++ tailWord_932195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932205 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_932205 : Nat := 118140960795 + 932205 * 2 ^ 59
def prefixEnd_932205 : Nat := 4983230072969 + 3 ^ 40 * 932205 * 2
def baseEnd_932205 : Nat := 478669233524630477350373

theorem tailTrace_932205 : CollatzResearch.WordTrace tailWord_932205 prefixEnd_932205 478669233524630477350373 := by
  unfold tailWord_932205
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000309587787967783918069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22666873058525311855945379 34000309587787967783918069)
  ·
    refine ⟨3187529023855121979742319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34000309587787967783918069 3187529023855121979742319)
    ·
      refine ⟨4781293535782682969613479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187529023855121979742319 4781293535782682969613479)
      ·
        refine ⟨7171940303674024454420219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781293535782682969613479 7171940303674024454420219)
        ·
          refine ⟨10757910455511036681630329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171940303674024454420219 10757910455511036681630329)
          ·
            refine ⟨8068432841633277511222747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10757910455511036681630329 8068432841633277511222747)
            ·
              refine ⟨12102649262449916266834121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068432841633277511222747 12102649262449916266834121)
              ·
                refine ⟨9076986946837437200125591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102649262449916266834121 9076986946837437200125591)
                ·
                  refine ⟨13615480420256155800188387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9076986946837437200125591 13615480420256155800188387)
                  ·
                    refine ⟨20423220630384233700282581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13615480420256155800188387 20423220630384233700282581)
                    ·
                      refine ⟨478669233524630477350373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20423220630384233700282581 478669233524630477350373)
                      ·
                        rfl

theorem cell23_932205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_932205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932205 prefixEnd_932205 := by exact prefixLift 932205
  have htrace : WordTrace (prefixWord ++ tailWord_932205) baseStart_932205 baseEnd_932205 := by
    simpa [prefixWord, tailWord_932205, baseEnd_932205] using wordTrace_append hprefix tailTrace_932205
  have hstable : (prefixWord ++ tailWord_932205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932205).length < 2 ^ (prefixWord ++ tailWord_932205).sum := by decide
  have hdescent : baseEnd_932205 < baseStart_932205 := by decide
  rcases family_descends (prefixWord ++ tailWord_932205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932232 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_932232 : Nat := 118140960795 + 932232 * 2 ^ 59
def prefixEnd_932232 : Nat := 4983230072969 + 3 ^ 40 * 932232 * 2
def baseEnd_932232 : Nat := 478683097502301871712749

theorem tailTrace_932232 : CollatzResearch.WordTrace tailWord_932232 prefixEnd_932232 478683097502301871712749 := by
  unfold tailWord_932232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17000647179345075697575475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22667529572460100930100633 17000647179345075697575475)
  ·
    refine ⟨25500970769017613546363213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17000647179345075697575475 25500970769017613546363213)
    ·
      refine ⟨9562864038381605079886205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25500970769017613546363213 9562864038381605079886205)
      ·
        refine ⟨3586074014393101904957327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9562864038381605079886205 3586074014393101904957327)
        ·
          refine ⟨5379111021589652857435991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586074014393101904957327 5379111021589652857435991)
          ·
            refine ⟨8068666532384479286153987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379111021589652857435991 8068666532384479286153987)
            ·
              refine ⟨12102999798576718929230981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068666532384479286153987 12102999798576718929230981)
              ·
                refine ⟨2269312462233134799230809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12102999798576718929230981 2269312462233134799230809)
                ·
                  refine ⟨1701984346674851099423107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269312462233134799230809 1701984346674851099423107)
                  ·
                    refine ⟨2552976520012276649134661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701984346674851099423107 2552976520012276649134661)
                    ·
                      refine ⟨478683097502301871712749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2552976520012276649134661 478683097502301871712749)
                      ·
                        rfl

theorem cell23_932232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_932232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932232 prefixEnd_932232 := by exact prefixLift 932232
  have htrace : WordTrace (prefixWord ++ tailWord_932232) baseStart_932232 baseEnd_932232 := by
    simpa [prefixWord, tailWord_932232, baseEnd_932232] using wordTrace_append hprefix tailTrace_932232
  have hstable : (prefixWord ++ tailWord_932232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932232).length < 2 ^ (prefixWord ++ tailWord_932232).sum := by decide
  have hdescent : baseEnd_932232 < baseStart_932232 := by decide
  rcases family_descends (prefixWord ++ tailWord_932232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932245 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_932245 : Nat := 118140960795 + 932245 * 2 ^ 59
def prefixEnd_932245 : Nat := 4983230072969 + 3 ^ 40 * 932245 * 2
def baseEnd_932245 : Nat := 478689772750810320850189

theorem tailTrace_932245 : CollatzResearch.WordTrace tailWord_932245 prefixEnd_932245 478689772750810320850189 := by
  unfold tailWord_932245
  simp only [CollatzResearch.WordTrace]
  refine ⟨34001768507643054615374189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22667845671762036410249459 34001768507643054615374189)
  ·
    refine ⟨12750663190366145480765321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34001768507643054615374189 12750663190366145480765321)
    ·
      refine ⟨9562997392774609110573991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12750663190366145480765321 9562997392774609110573991)
      ·
        refine ⟨14344496089161913665860987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9562997392774609110573991 14344496089161913665860987)
        ·
          refine ⟨21516744133742870498791481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344496089161913665860987 21516744133742870498791481)
          ·
            refine ⟨16137558100307152874093611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21516744133742870498791481 16137558100307152874093611)
            ·
              refine ⟨24206337150460729311140417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137558100307152874093611 24206337150460729311140417)
              ·
                refine ⟨18154752862845546983355313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24206337150460729311140417 18154752862845546983355313)
                ·
                  refine ⟨13616064647134160237516485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18154752862845546983355313 13616064647134160237516485)
                  ·
                    refine ⟨2553012121337655044534341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13616064647134160237516485 2553012121337655044534341)
                    ·
                      refine ⟨478689772750810320850189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2553012121337655044534341 478689772750810320850189)
                      ·
                        rfl

theorem cell23_932245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_932245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932245 prefixEnd_932245 := by exact prefixLift 932245
  have htrace : WordTrace (prefixWord ++ tailWord_932245) baseStart_932245 baseEnd_932245 := by
    simpa [prefixWord, tailWord_932245, baseEnd_932245] using wordTrace_append hprefix tailTrace_932245
  have hstable : (prefixWord ++ tailWord_932245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932245).length < 2 ^ (prefixWord ++ tailWord_932245).sum := by decide
  have hdescent : baseEnd_932245 < baseStart_932245 := by decide
  rcases family_descends (prefixWord ++ tailWord_932245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932309 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_932309 : Nat := 118140960795 + 932309 * 2 ^ 59
def prefixEnd_932309 : Nat := 4983230072969 + 3 ^ 40 * 932309 * 2
def baseEnd_932309 : Nat := 478722635512698070449895

theorem tailTrace_932309 : CollatzResearch.WordTrace tailWord_932309 prefixEnd_932309 478722635512698070449895 := by
  unfold tailWord_932309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34004102779411193545703981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22669401852940795697135987 34004102779411193545703981)
  ·
    refine ⟨12751538542279197579638993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34004102779411193545703981 12751538542279197579638993)
    ·
      refine ⟨9563653906709398184729245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12751538542279197579638993 9563653906709398184729245)
      ·
        refine ⟨3586370215016024319273467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9563653906709398184729245 3586370215016024319273467)
        ·
          refine ⟨5379555322524036478910201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586370215016024319273467 5379555322524036478910201)
          ·
            refine ⟨4034666491893027359182651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379555322524036478910201 4034666491893027359182651)
            ·
              refine ⟨6051999737839541038773977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034666491893027359182651 6051999737839541038773977)
              ·
                refine ⟨4538999803379655779080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051999737839541038773977 4538999803379655779080483)
                ·
                  refine ⟨6808499705069483668620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538999803379655779080483 6808499705069483668620725)
                  ·
                    refine ⟨638296847350264093933193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808499705069483668620725 638296847350264093933193)
                    ·
                      refine ⟨478722635512698070449895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638296847350264093933193 478722635512698070449895)
                      ·
                        rfl

theorem cell23_932309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_932309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932309 prefixEnd_932309 := by exact prefixLift 932309
  have htrace : WordTrace (prefixWord ++ tailWord_932309) baseStart_932309 baseEnd_932309 := by
    simpa [prefixWord, tailWord_932309, baseEnd_932309] using wordTrace_append hprefix tailTrace_932309
  have hstable : (prefixWord ++ tailWord_932309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932309).length < 2 ^ (prefixWord ++ tailWord_932309).sum := by decide
  have hdescent : baseEnd_932309 < baseStart_932309 := by decide
  rcases family_descends (prefixWord ++ tailWord_932309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932319 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 1, 5]
def baseStart_932319 : Nat := 118140960795 + 932319 * 2 ^ 59
def prefixEnd_932319 : Nat := 4983230072969 + 3 ^ 40 * 932319 * 2
def baseEnd_932319 : Nat := 159575923439747677108283

theorem tailTrace_932319 : CollatzResearch.WordTrace tailWord_932319 prefixEnd_932319 159575923439747677108283 := by
  unfold tailWord_932319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34004467509374965253568011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22669645006249976835712007 34004467509374965253568011)
  ·
    refine ⟨51006701264062447880352017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34004467509374965253568011 51006701264062447880352017)
    ·
      refine ⟨38255025948046835910264013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51006701264062447880352017 38255025948046835910264013)
      ·
        refine ⟨14345634730517563466349005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38255025948046835910264013 14345634730517563466349005)
        ·
          refine ⟨5379613023944086299880877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14345634730517563466349005 5379613023944086299880877)
          ·
            refine ⟨2017354883979032362455329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5379613023944086299880877 2017354883979032362455329)
            ·
              refine ⟨1513016162984274271841497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017354883979032362455329 1513016162984274271841497)
              ·
                refine ⟨1134762122238205703881123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513016162984274271841497 1134762122238205703881123)
                ·
                  refine ⟨1702143183357308555821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134762122238205703881123 1702143183357308555821685)
                  ·
                    refine ⟨159575923439747677108283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1702143183357308555821685 159575923439747677108283)
                    ·
                      rfl

theorem cell23_932319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_932319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932319 prefixEnd_932319 := by exact prefixLift 932319
  have htrace : WordTrace (prefixWord ++ tailWord_932319) baseStart_932319 baseEnd_932319 := by
    simpa [prefixWord, tailWord_932319, baseEnd_932319] using wordTrace_append hprefix tailTrace_932319
  have hstable : (prefixWord ++ tailWord_932319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932319).length < 2 ^ (prefixWord ++ tailWord_932319).sum := by decide
  have hdescent : baseEnd_932319 < baseStart_932319 := by decide
  rcases family_descends (prefixWord ++ tailWord_932319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932332 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_932332 : Nat := 118140960795 + 932332 * 2 ^ 59
def prefixEnd_932332 : Nat := 4983230072969 + 3 ^ 40 * 932332 * 2
def baseEnd_932332 : Nat := 159578148522583826820763

theorem tailTrace_932332 : CollatzResearch.WordTrace tailWord_932332 prefixEnd_932332 159578148522583826820763 := by
  unfold tailWord_932332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17002470829163934236895625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22669961105551912315860833 17002470829163934236895625)
  ·
    refine ⟨12751853121872950677671719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17002470829163934236895625 12751853121872950677671719)
    ·
      refine ⟨19127779682809426016507579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12751853121872950677671719 19127779682809426016507579)
      ·
        refine ⟨28691669524214139024761369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19127779682809426016507579 28691669524214139024761369)
        ·
          refine ⟨21518752143160604268571027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28691669524214139024761369 21518752143160604268571027)
          ·
            refine ⟨32278128214740906402856541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21518752143160604268571027 32278128214740906402856541)
            ·
              refine ⟨12104298080527839901071203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32278128214740906402856541 12104298080527839901071203)
              ·
                refine ⟨18156447120791759851606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104298080527839901071203 18156447120791759851606805)
                ·
                  refine ⟨851083458787113743044069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18156447120791759851606805 851083458787113743044069)
                  ·
                    refine ⟨159578148522583826820763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851083458787113743044069 159578148522583826820763)
                    ·
                      rfl

theorem cell23_932332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_932332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932332 prefixEnd_932332 := by exact prefixLift 932332
  have htrace : WordTrace (prefixWord ++ tailWord_932332) baseStart_932332 baseEnd_932332 := by
    simpa [prefixWord, tailWord_932332, baseEnd_932332] using wordTrace_append hprefix tailTrace_932332
  have hstable : (prefixWord ++ tailWord_932332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932332).length < 2 ^ (prefixWord ++ tailWord_932332).sum := by decide
  have hdescent : baseEnd_932332 < baseStart_932332 := by decide
  rcases family_descends (prefixWord ++ tailWord_932332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932345 : List Nat := [1, 2, 1, 3, 1, 2, 13]
def baseStart_932345 : Nat := 118140960795 + 932345 * 2 ^ 59
def prefixEnd_932345 : Nat := 4983230072969 + 3 ^ 40 * 932345 * 2
def baseEnd_932345 : Nat := 5910384207608147279009

theorem tailTrace_932345 : CollatzResearch.WordTrace tailWord_932345 prefixEnd_932345 5910384207608147279009 := by
  unfold tailWord_932345
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005415807280771694014489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22670277204853847796009659 34005415807280771694014489)
  ·
    refine ⟨25504061855460578770510867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34005415807280771694014489 25504061855460578770510867)
    ·
      refine ⟨38256092783190868155766301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25504061855460578770510867 38256092783190868155766301)
      ·
        refine ⟨14346034793696575558412363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38256092783190868155766301 14346034793696575558412363)
        ·
          refine ⟨21519052190544863337618545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14346034793696575558412363 21519052190544863337618545)
          ·
            refine ⟨16139289142908647503213909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21519052190544863337618545 16139289142908647503213909)
            ·
              refine ⟨5910384207608147279009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 16139289142908647503213909 5910384207608147279009)
              ·
                rfl

theorem cell23_932345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 13].length) (baseStart_932345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932345 prefixEnd_932345 := by exact prefixLift 932345
  have htrace : WordTrace (prefixWord ++ tailWord_932345) baseStart_932345 baseEnd_932345 := by
    simpa [prefixWord, tailWord_932345, baseEnd_932345] using wordTrace_append hprefix tailTrace_932345
  have hstable : (prefixWord ++ tailWord_932345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932345).length < 2 ^ (prefixWord ++ tailWord_932345).sum := by decide
  have hdescent : baseEnd_932345 < baseStart_932345 := by decide
  rcases family_descends (prefixWord ++ tailWord_932345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932349 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_932349 : Nat := 118140960795 + 932349 * 2 ^ 59
def prefixEnd_932349 : Nat := 4983230072969 + 3 ^ 40 * 932349 * 2
def baseEnd_932349 : Nat := 159581058246292637983237

theorem tailTrace_932349 : CollatzResearch.WordTrace tailWord_932349 prefixEnd_932349 159581058246292637983237 := by
  unfold tailWord_932349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005561699266280377160101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22670374466177520251440067 34005561699266280377160101)
  ·
    refine ⟨6376042818612427570717519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34005561699266280377160101 6376042818612427570717519)
    ·
      refine ⟨9564064227918641356076279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376042818612427570717519 9564064227918641356076279)
      ·
        refine ⟨14346096341877962034114419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564064227918641356076279 14346096341877962034114419)
        ·
          refine ⟨21519144512816943051171629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14346096341877962034114419 21519144512816943051171629)
          ·
            refine ⟨8069679192306353644189361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21519144512816943051171629 8069679192306353644189361)
            ·
              refine ⟨6052259394229765233142021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8069679192306353644189361 6052259394229765233142021)
              ·
                refine ⟨1134798636418080981214129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6052259394229765233142021 1134798636418080981214129)
                ·
                  refine ⟨851098977313560735910597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134798636418080981214129 851098977313560735910597)
                  ·
                    refine ⟨159581058246292637983237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851098977313560735910597 159581058246292637983237)
                    ·
                      rfl

theorem cell23_932349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_932349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932349 prefixEnd_932349 := by exact prefixLift 932349
  have htrace : WordTrace (prefixWord ++ tailWord_932349) baseStart_932349 baseEnd_932349 := by
    simpa [prefixWord, tailWord_932349, baseEnd_932349] using wordTrace_append hprefix tailTrace_932349
  have hstable : (prefixWord ++ tailWord_932349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932349).length < 2 ^ (prefixWord ++ tailWord_932349).sum := by decide
  have hdescent : baseEnd_932349 < baseStart_932349 := by decide
  rcases family_descends (prefixWord ++ tailWord_932349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932362 : List Nat := [3, 1, 2, 2, 2, 1, 4, 8]
def baseStart_932362 : Nat := 118140960795 + 932362 * 2 ^ 59
def prefixEnd_932362 : Nat := 4983230072969 + 3 ^ 40 * 932362 * 2
def baseEnd_932362 : Nat := 17731475925458754188413

theorem tailTrace_932362 : CollatzResearch.WordTrace tailWord_932362 prefixEnd_932362 17731475925458754188413 := by
  unfold tailWord_932362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501508962054795899345835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22670690565479455731588893 8501508962054795899345835)
  ·
    refine ⟨12752263443082193849018753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501508962054795899345835 12752263443082193849018753)
    ·
      refine ⟨9564197582311645386764065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12752263443082193849018753 9564197582311645386764065)
      ·
        refine ⟨7173148186733734040073049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564197582311645386764065 7173148186733734040073049)
        ·
          refine ⟨5379861140050300530054787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7173148186733734040073049 5379861140050300530054787)
          ·
            refine ⟨8069791710075450795082181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379861140050300530054787 8069791710075450795082181)
            ·
              refine ⟨1513085945639147024077909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8069791710075450795082181 1513085945639147024077909)
              ·
                refine ⟨17731475925458754188413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1513085945639147024077909 17731475925458754188413)
                ·
                  rfl

theorem cell23_932362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_932362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932362 prefixEnd_932362 := by exact prefixLift 932362
  have htrace : WordTrace (prefixWord ++ tailWord_932362) baseStart_932362 baseEnd_932362 := by
    simpa [prefixWord, tailWord_932362, baseEnd_932362] using wordTrace_append hprefix tailTrace_932362
  have hstable : (prefixWord ++ tailWord_932362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932362).length < 2 ^ (prefixWord ++ tailWord_932362).sum := by decide
  have hdescent : baseEnd_932362 < baseStart_932362 := by decide
  rcases family_descends (prefixWord ++ tailWord_932362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932366 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_932366 : Nat := 118140960795 + 932366 * 2 ^ 59
def prefixEnd_932366 : Nat := 4983230072969 + 3 ^ 40 * 932366 * 2
def baseEnd_932366 : Nat := 159583967970001449145711

theorem tailTrace_932366 : CollatzResearch.WordTrace tailWord_932366 prefixEnd_932366 159583967970001449145711 := by
  unfold tailWord_932366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250772717525586535066119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22670787826803128187019301 4250772717525586535066119)
  ·
    refine ⟨6376159076288379802599179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250772717525586535066119 6376159076288379802599179)
    ·
      refine ⟨9564238614432569703898769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376159076288379802599179 9564238614432569703898769)
      ·
        refine ⟨7173178960824427277924077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564238614432569703898769 7173178960824427277924077)
        ·
          refine ⟨2689942110309160229221529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7173178960824427277924077 2689942110309160229221529)
          ·
            refine ⟨2017456582731870171916147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2689942110309160229221529 2017456582731870171916147)
            ·
              refine ⟨3026184874097805257874221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017456582731870171916147 3026184874097805257874221)
              ·
                refine ⟨1134819327786676971702833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026184874097805257874221 1134819327786676971702833)
                ·
                  refine ⟨851114495840007728777125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134819327786676971702833 851114495840007728777125)
                  ·
                    refine ⟨159583967970001449145711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851114495840007728777125 159583967970001449145711)
                    ·
                      rfl

theorem cell23_932366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_932366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932366 prefixEnd_932366 := by exact prefixLift 932366
  have htrace : WordTrace (prefixWord ++ tailWord_932366) baseStart_932366 baseEnd_932366 := by
    simpa [prefixWord, tailWord_932366, baseEnd_932366] using wordTrace_append hprefix tailTrace_932366
  have hstable : (prefixWord ++ tailWord_932366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932366).length < 2 ^ (prefixWord ++ tailWord_932366).sum := by decide
  have hdescent : baseEnd_932366 < baseStart_932366 := by decide
  rcases family_descends (prefixWord ++ tailWord_932366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932376 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_932376 : Nat := 118140960795 + 932376 * 2 ^ 59
def prefixEnd_932376 : Nat := 4983230072969 + 3 ^ 40 * 932376 * 2
def baseEnd_932376 : Nat := 478757038716549308312087

theorem tailTrace_932376 : CollatzResearch.WordTrace tailWord_932376 prefixEnd_932376 478757038716549308312087 := by
  unfold tailWord_932376
  simp only [CollatzResearch.WordTrace]
  refine ⟨17003273235084231994196491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22671030980112309325595321 17003273235084231994196491)
  ·
    refine ⟨25504909852626347991294737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17003273235084231994196491 25504909852626347991294737)
    ·
      refine ⟨19128682389469760993471053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25504909852626347991294737 19128682389469760993471053)
      ·
        refine ⟨7173255896051160372551645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19128682389469760993471053 7173255896051160372551645)
        ·
          refine ⟨2689970961019185139706867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7173255896051160372551645 2689970961019185139706867)
          ·
            refine ⟨4034956441528777709560301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689970961019185139706867 4034956441528777709560301)
            ·
              refine ⟨1513108665573291641085113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4034956441528777709560301 1513108665573291641085113)
              ·
                refine ⟨1134831499179968730813835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513108665573291641085113 1134831499179968730813835)
                ·
                  refine ⟨1702247248769953096220753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134831499179968730813835 1702247248769953096220753)
                  ·
                    refine ⟨1276685436577464822165565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702247248769953096220753 1276685436577464822165565)
                    ·
                      refine ⟨478757038716549308312087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276685436577464822165565 478757038716549308312087)
                      ·
                        rfl

theorem cell23_932376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_932376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932376 prefixEnd_932376 := by exact prefixLift 932376
  have htrace : WordTrace (prefixWord ++ tailWord_932376) baseStart_932376 baseEnd_932376 := by
    simpa [prefixWord, tailWord_932376, baseEnd_932376] using wordTrace_append hprefix tailTrace_932376
  have hstable : (prefixWord ++ tailWord_932376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932376).length < 2 ^ (prefixWord ++ tailWord_932376).sum := by decide
  have hdescent : baseEnd_932376 < baseStart_932376 := by decide
  rcases family_descends (prefixWord ++ tailWord_932376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932389 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_932389 : Nat := 118140960795 + 932389 * 2 ^ 59
def prefixEnd_932389 : Nat := 4983230072969 + 3 ^ 40 * 932389 * 2
def baseEnd_932389 : Nat := 478763713965057757449527

theorem tailTrace_932389 : CollatzResearch.WordTrace tailWord_932389 prefixEnd_932389 478763713965057757449527 := by
  unfold tailWord_932389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007020619121367208616221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22671347079414244805744147 34007020619121367208616221)
  ·
    refine ⟨12752632732170512703231083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34007020619121367208616221 12752632732170512703231083)
    ·
      refine ⟨19128949098255769054846625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752632732170512703231083 19128949098255769054846625)
      ·
        refine ⟨14346711823691826791134969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19128949098255769054846625 14346711823691826791134969)
        ·
          refine ⟨10760033867768870093351227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14346711823691826791134969 10760033867768870093351227)
          ·
            refine ⟨16140050801653305140026841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760033867768870093351227 16140050801653305140026841)
            ·
              refine ⟨12105038101239978855020131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16140050801653305140026841 12105038101239978855020131)
              ·
                refine ⟨18157557151859968282530197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12105038101239978855020131 18157557151859968282530197)
                ·
                  refine ⟨851135491493436013243603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18157557151859968282530197 851135491493436013243603)
                  ·
                    refine ⟨1276703237240154019865405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851135491493436013243603 1276703237240154019865405)
                    ·
                      refine ⟨478763713965057757449527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1276703237240154019865405 478763713965057757449527)
                      ·
                        rfl

theorem cell23_932389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_932389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932389 prefixEnd_932389 := by exact prefixLift 932389
  have htrace : WordTrace (prefixWord ++ tailWord_932389) baseStart_932389 baseEnd_932389 := by
    simpa [prefixWord, tailWord_932389, baseEnd_932389] using wordTrace_append hprefix tailTrace_932389
  have hstable : (prefixWord ++ tailWord_932389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932389).length < 2 ^ (prefixWord ++ tailWord_932389).sum := by decide
  have hdescent : baseEnd_932389 < baseStart_932389 := by decide
  rcases family_descends (prefixWord ++ tailWord_932389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932402 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_932402 : Nat := 118140960795 + 932402 * 2 ^ 59
def prefixEnd_932402 : Nat := 4983230072969 + 3 ^ 40 * 932402 * 2
def baseEnd_932402 : Nat := 478770389213566206586967

theorem tailTrace_932402 : CollatzResearch.WordTrace tailWord_932402 prefixEnd_932402 478770389213566206586967 := by
  unfold tailWord_932402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501873692018567607209865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22671663178716180285892973 8501873692018567607209865)
  ·
    refine ⟨6376405269013925705407399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8501873692018567607209865 6376405269013925705407399)
    ·
      refine ⟨9564607903520888558111099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376405269013925705407399 9564607903520888558111099)
      ·
        refine ⟨14346911855281332837166649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564607903520888558111099 14346911855281332837166649)
        ·
          refine ⟨10760183891460999627874987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14346911855281332837166649 10760183891460999627874987)
          ·
            refine ⟨16140275837191499441812481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760183891460999627874987 16140275837191499441812481)
            ·
              refine ⟨12105206877893624581359361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16140275837191499441812481 12105206877893624581359361)
              ·
                refine ⟨9078905158420218436019521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12105206877893624581359361 9078905158420218436019521)
                ·
                  refine ⟨6809178868815163827014641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9078905158420218436019521 6809178868815163827014641)
                  ·
                    refine ⟨5106884151611372870260981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809178868815163827014641 5106884151611372870260981)
                    ·
                      refine ⟨478770389213566206586967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5106884151611372870260981 478770389213566206586967)
                      ·
                        rfl

theorem cell23_932402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_932402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932402 prefixEnd_932402 := by exact prefixLift 932402
  have htrace : WordTrace (prefixWord ++ tailWord_932402) baseStart_932402 baseEnd_932402 := by
    simpa [prefixWord, tailWord_932402, baseEnd_932402] using wordTrace_append hprefix tailTrace_932402
  have hstable : (prefixWord ++ tailWord_932402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932402).length < 2 ^ (prefixWord ++ tailWord_932402).sum := by decide
  have hdescent : baseEnd_932402 < baseStart_932402 := by decide
  rcases family_descends (prefixWord ++ tailWord_932402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932420 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_932420 : Nat := 118140960795 + 932420 * 2 ^ 59
def prefixEnd_932420 : Nat := 4983230072969 + 3 ^ 40 * 932420 * 2
def baseEnd_932420 : Nat := 478779631865347136161885

theorem tailTrace_932420 : CollatzResearch.WordTrace tailWord_932420 prefixEnd_932420 478779631865347136161885 := by
  unfold tailWord_932420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004075641004529751497357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22672100854672706335329809 17004075641004529751497357)
  ·
    refine ⟨6376528365376698656811509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17004075641004529751497357 6376528365376698656811509)
    ·
      refine ⟨597799534254065499076079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6376528365376698656811509 597799534254065499076079)
      ·
        refine ⟨896699301381098248614119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597799534254065499076079 896699301381098248614119)
        ·
          refine ⟨1345048952071647372921179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896699301381098248614119 1345048952071647372921179)
          ·
            refine ⟨2017573428107471059381769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345048952071647372921179 2017573428107471059381769)
            ·
              refine ⟨1513180071080603294536327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017573428107471059381769 1513180071080603294536327)
              ·
                refine ⟨2269770106620904941804491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513180071080603294536327 2269770106620904941804491)
                ·
                  refine ⟨3404655159931357412706737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269770106620904941804491 3404655159931357412706737)
                  ·
                    refine ⟨2553491369948518059530053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404655159931357412706737 2553491369948518059530053)
                    ·
                      refine ⟨478779631865347136161885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2553491369948518059530053 478779631865347136161885)
                      ·
                        rfl

theorem cell23_932420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_932420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932420 prefixEnd_932420 := by exact prefixLift 932420
  have htrace : WordTrace (prefixWord ++ tailWord_932420) baseStart_932420 baseEnd_932420 := by
    simpa [prefixWord, tailWord_932420, baseEnd_932420] using wordTrace_append hprefix tailTrace_932420
  have hstable : (prefixWord ++ tailWord_932420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932420).length < 2 ^ (prefixWord ++ tailWord_932420).sum := by decide
  have hdescent : baseEnd_932420 < baseStart_932420 := by decide
  rcases family_descends (prefixWord ++ tailWord_932420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932432 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_932432 : Nat := 118140960795 + 932432 * 2 ^ 59
def prefixEnd_932432 : Nat := 4983230072969 + 3 ^ 40 * 932432 * 2
def baseEnd_932432 : Nat := 478785793633201089211829

theorem tailTrace_932432 : CollatzResearch.WordTrace tailWord_932432 prefixEnd_932432 478785793633201089211829 := by
  unfold tailWord_932432
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004294478982792776215775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22672392638643723701621033 17004294478982792776215775)
  ·
    refine ⟨25506441718474189164323663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004294478982792776215775 25506441718474189164323663)
    ·
      refine ⟨38259662577711283746485495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506441718474189164323663 38259662577711283746485495)
      ·
        refine ⟨57389493866566925619728243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38259662577711283746485495 57389493866566925619728243)
        ·
          refine ⟨86084240799850388429592365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57389493866566925619728243 86084240799850388429592365)
          ·
            refine ⟨32281590299943895661097137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86084240799850388429592365 32281590299943895661097137)
            ·
              refine ⟨24211192724957921745822853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32281590299943895661097137 24211192724957921745822853)
              ·
                refine ⟨4539598635929610327341785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24211192724957921745822853 4539598635929610327341785)
                ·
                  refine ⟨3404698976947207745506339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539598635929610327341785 3404698976947207745506339)
                  ·
                    refine ⟨5107048465420811618259509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3404698976947207745506339 5107048465420811618259509)
                    ·
                      refine ⟨478785793633201089211829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5107048465420811618259509 478785793633201089211829)
                      ·
                        rfl

theorem cell23_932432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_932432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932432 prefixEnd_932432 := by exact prefixLift 932432
  have htrace : WordTrace (prefixWord ++ tailWord_932432) baseStart_932432 baseEnd_932432 := by
    simpa [prefixWord, tailWord_932432, baseEnd_932432] using wordTrace_append hprefix tailTrace_932432
  have hstable : (prefixWord ++ tailWord_932432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932432).length < 2 ^ (prefixWord ++ tailWord_932432).sum := by decide
  have hdescent : baseEnd_932432 < baseStart_932432 := by decide
  rcases family_descends (prefixWord ++ tailWord_932432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932452 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 9]
def baseStart_932452 : Nat := 118140960795 + 932452 * 2 ^ 59
def prefixEnd_932452 : Nat := 4983230072969 + 3 ^ 40 * 932452 * 2
def baseEnd_932452 : Nat := 53199562582921223440193

theorem tailTrace_932452 : CollatzResearch.WordTrace tailWord_932452 prefixEnd_932452 53199562582921223440193 := by
  unfold tailWord_932452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004659208946564484079805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22672878945262085978773073 17004659208946564484079805)
  ·
    refine ⟨6376747203354961681529927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17004659208946564484079805 6376747203354961681529927)
    ·
      refine ⟨9565120805032442522294891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376747203354961681529927 9565120805032442522294891)
      ·
        refine ⟨14347681207548663783442337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565120805032442522294891 14347681207548663783442337)
        ·
          refine ⟨10760760905661497837581753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14347681207548663783442337 10760760905661497837581753)
          ·
            refine ⟨8070570679246123378186315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760760905661497837581753 8070570679246123378186315)
            ·
              refine ⟨12105856018869185067279473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070570679246123378186315 12105856018869185067279473)
              ·
                refine ⟨9079392014151888800459605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12105856018869185067279473 9079392014151888800459605)
                ·
                  refine ⟨53199562582921223440193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9079392014151888800459605 53199562582921223440193)
                  ·
                    rfl

theorem cell23_932452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_932452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932452 prefixEnd_932452 := by exact prefixLift 932452
  have htrace : WordTrace (prefixWord ++ tailWord_932452) baseStart_932452 baseEnd_932452 := by
    simpa [prefixWord, tailWord_932452, baseEnd_932452] using wordTrace_append hprefix tailTrace_932452
  have hstable : (prefixWord ++ tailWord_932452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932452).length < 2 ^ (prefixWord ++ tailWord_932452).sum := by decide
  have hdescent : baseEnd_932452 < baseStart_932452 := by decide
  rcases family_descends (prefixWord ++ tailWord_932452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932463 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 2, 2, 2]
def baseStart_932463 : Nat := 118140960795 + 932463 * 2 ^ 59
def prefixEnd_932463 : Nat := 4983230072969 + 3 ^ 40 * 932463 * 2
def baseEnd_932463 : Nat := 478801711533490467924187

theorem tailTrace_932463 : CollatzResearch.WordTrace tailWord_932463 prefixEnd_932463 478801711533490467924187 := by
  unfold tailWord_932463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34009719620853277846810043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22673146413902185231206695 34009719620853277846810043)
  ·
    refine ⟨51014579431279916770215065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34009719620853277846810043 51014579431279916770215065)
    ·
      refine ⟨38260934573459937577661299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51014579431279916770215065 38260934573459937577661299)
      ·
        refine ⟨57391401860189906366491949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38260934573459937577661299 57391401860189906366491949)
        ·
          refine ⟨21521775697571214887434481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57391401860189906366491949 21521775697571214887434481)
          ·
            refine ⟨16141331773178411165575861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21521775697571214887434481 16141331773178411165575861)
            ·
              refine ⟨1513249853735476046772737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16141331773178411165575861 1513249853735476046772737)
              ·
                refine ⟨1134937390301607035079553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513249853735476046772737 1134937390301607035079553)
                ·
                  refine ⟨851203042726205276309665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134937390301607035079553 851203042726205276309665)
                  ·
                    refine ⟨638402282044653957232249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 851203042726205276309665 638402282044653957232249)
                    ·
                      refine ⟨478801711533490467924187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638402282044653957232249 478801711533490467924187)
                      ·
                        rfl

theorem cell23_932463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2, 2].length) (baseStart_932463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932463 prefixEnd_932463 := by exact prefixLift 932463
  have htrace : WordTrace (prefixWord ++ tailWord_932463) baseStart_932463 baseEnd_932463 := by
    simpa [prefixWord, tailWord_932463, baseEnd_932463] using wordTrace_append hprefix tailTrace_932463
  have hstable : (prefixWord ++ tailWord_932463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932463).length < 2 ^ (prefixWord ++ tailWord_932463).sum := by decide
  have hdescent : baseEnd_932463 < baseStart_932463 := by decide
  rcases family_descends (prefixWord ++ tailWord_932463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932480 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2]
def baseStart_932480 : Nat := 118140960795 + 932480 * 2 ^ 59
def prefixEnd_932480 : Nat := 4983230072969 + 3 ^ 40 * 932480 * 2
def baseEnd_932480 : Nat := 478810440704616901411609

theorem tailTrace_932480 : CollatzResearch.WordTrace tailWord_932480 prefixEnd_932480 478810440704616901411609 := by
  unfold tailWord_932480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005169830895844875089447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22673559774527793166785929 17005169830895844875089447)
  ·
    refine ⟨25507754746343767312634171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17005169830895844875089447 25507754746343767312634171)
    ·
      refine ⟨38261632119515650968951257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25507754746343767312634171 38261632119515650968951257)
      ·
        refine ⟨28696224089636738226713443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38261632119515650968951257 28696224089636738226713443)
        ·
          refine ⟨43044336134455107340070165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28696224089636738226713443 43044336134455107340070165)
          ·
            refine ⟨2017703256302583156565789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43044336134455107340070165 2017703256302583156565789)
            ·
              refine ⟨756638721113468683712171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2017703256302583156565789 756638721113468683712171)
              ·
                refine ⟨1134958081670203025568257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756638721113468683712171 1134958081670203025568257)
                ·
                  refine ⟨851218561252652269176193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134958081670203025568257 851218561252652269176193)
                  ·
                    refine ⟨638413920939489201882145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 851218561252652269176193 638413920939489201882145)
                    ·
                      refine ⟨478810440704616901411609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638413920939489201882145 478810440704616901411609)
                      ·
                        rfl

theorem cell23_932480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_932480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932480 prefixEnd_932480 := by exact prefixLift 932480
  have htrace : WordTrace (prefixWord ++ tailWord_932480) baseStart_932480 baseEnd_932480 := by
    simpa [prefixWord, tailWord_932480, baseEnd_932480] using wordTrace_append hprefix tailTrace_932480
  have hstable : (prefixWord ++ tailWord_932480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932480).length < 2 ^ (prefixWord ++ tailWord_932480).sum := by decide
  have hdescent : baseEnd_932480 < baseStart_932480 := by decide
  rcases family_descends (prefixWord ++ tailWord_932480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932492 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_932492 : Nat := 118140960795 + 932492 * 2 ^ 59
def prefixEnd_932492 : Nat := 4983230072969 + 3 ^ 40 * 932492 * 2
def baseEnd_932492 : Nat := 478816602472470854461553

theorem tailTrace_932492 : CollatzResearch.WordTrace tailWord_932492 prefixEnd_932492 478816602472470854461553 := by
  unfold tailWord_932492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005388668874107899807865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22673851558498810533077153 17005388668874107899807865)
  ·
    refine ⟨12754041501655580924855899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17005388668874107899807865 12754041501655580924855899)
    ·
      refine ⟨19131062252483371387283849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12754041501655580924855899 19131062252483371387283849)
      ·
        refine ⟨14348296689362528540462887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19131062252483371387283849 14348296689362528540462887)
        ·
          refine ⟨21522445034043792810694331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348296689362528540462887 21522445034043792810694331)
          ·
            refine ⟨32283667551065689216041497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21522445034043792810694331 32283667551065689216041497)
            ·
              refine ⟨24212750663299266912031123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32283667551065689216041497 24212750663299266912031123)
              ·
                refine ⟨36319125994948900368046685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24212750663299266912031123 36319125994948900368046685)
                ·
                  refine ⟨13619672248105837638017507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36319125994948900368046685 13619672248105837638017507)
                  ·
                    refine ⟨20429508372158756457026261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13619672248105837638017507 20429508372158756457026261)
                    ·
                      refine ⟨478816602472470854461553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20429508372158756457026261 478816602472470854461553)
                      ·
                        rfl

theorem cell23_932492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_932492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932492 prefixEnd_932492 := by exact prefixLift 932492
  have htrace : WordTrace (prefixWord ++ tailWord_932492) baseStart_932492 baseEnd_932492 := by
    simpa [prefixWord, tailWord_932492, baseEnd_932492] using wordTrace_append hprefix tailTrace_932492
  have hstable : (prefixWord ++ tailWord_932492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932492).length < 2 ^ (prefixWord ++ tailWord_932492).sum := by decide
  have hdescent : baseEnd_932492 < baseStart_932492 := by decide
  rcases family_descends (prefixWord ++ tailWord_932492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932526 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_932526 : Nat := 118140960795 + 932526 * 2 ^ 59
def prefixEnd_932526 : Nat := 4983230072969 + 3 ^ 40 * 932526 * 2
def baseEnd_932526 : Nat := 478834060814723721436397

theorem tailTrace_932526 : CollatzResearch.WordTrace tailWord_932526 prefixEnd_932526 478834060814723721436397 := by
  unfold tailWord_932526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251502177453129950794179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22674678279750026404235621 4251502177453129950794179)
  ·
    refine ⟨6377253266179694926191269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251502177453129950794179 6377253266179694926191269)
    ·
      refine ⟨1195734987408692798660863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6377253266179694926191269 1195734987408692798660863)
      ·
        refine ⟨1793602481113039197991295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195734987408692798660863 1793602481113039197991295)
        ·
          refine ⟨2690403721669558796986943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793602481113039197991295 2690403721669558796986943)
          ·
            refine ⟨4035605582504338195480415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690403721669558796986943 4035605582504338195480415)
            ·
              refine ⟨6053408373756507293220623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035605582504338195480415 6053408373756507293220623)
              ·
                refine ⟨9080112560634760939830935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053408373756507293220623 9080112560634760939830935)
                ·
                  refine ⟨13620168840952141409746403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080112560634760939830935 13620168840952141409746403)
                  ·
                    refine ⟨20430253261428212114619605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13620168840952141409746403 20430253261428212114619605)
                    ·
                      refine ⟨478834060814723721436397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20430253261428212114619605 478834060814723721436397)
                      ·
                        rfl

theorem cell23_932526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_932526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932526 prefixEnd_932526 := by exact prefixLift 932526
  have htrace : WordTrace (prefixWord ++ tailWord_932526) baseStart_932526 baseEnd_932526 := by
    simpa [prefixWord, tailWord_932526, baseEnd_932526] using wordTrace_append hprefix tailTrace_932526
  have hstable : (prefixWord ++ tailWord_932526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932526).length < 2 ^ (prefixWord ++ tailWord_932526).sum := by decide
  have hdescent : baseEnd_932526 < baseStart_932526 := by decide
  rcases family_descends (prefixWord ++ tailWord_932526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932580 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_932580 : Nat := 118140960795 + 932580 * 2 ^ 59
def prefixEnd_932580 : Nat := 4983230072969 + 3 ^ 40 * 932580 * 2
def baseEnd_932580 : Nat := 159620596256688836720383

theorem tailTrace_932580 : CollatzResearch.WordTrace tailWord_932580 prefixEnd_932580 159620596256688836720383 := by
  unfold tailWord_932580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006993480714703414409597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22675991307619604552546129 17006993480714703414409597)
  ·
    refine ⟨6377622555268013780403599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17006993480714703414409597 6377622555268013780403599)
    ·
      refine ⟨9566433832902020670605399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377622555268013780403599 9566433832902020670605399)
      ·
        refine ⟨14349650749353031005908099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9566433832902020670605399 14349650749353031005908099)
        ·
          refine ⟨21524476124029546508862149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14349650749353031005908099 21524476124029546508862149)
          ·
            refine ⟨4035839273255539970411653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21524476124029546508862149 4035839273255539970411653)
            ·
              refine ⟨756719863735413744452185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4035839273255539970411653 756719863735413744452185)
              ·
                refine ⟨567539897801560308339139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756719863735413744452185 567539897801560308339139)
                ·
                  refine ⟨851309846702340462508709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567539897801560308339139 851309846702340462508709)
                  ·
                    refine ⟨159620596256688836720383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851309846702340462508709 159620596256688836720383)
                    ·
                      rfl

theorem cell23_932580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_932580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932580 prefixEnd_932580 := by exact prefixLift 932580
  have htrace : WordTrace (prefixWord ++ tailWord_932580) baseStart_932580 baseEnd_932580 := by
    simpa [prefixWord, tailWord_932580, baseEnd_932580] using wordTrace_append hprefix tailTrace_932580
  have hstable : (prefixWord ++ tailWord_932580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932580).length < 2 ^ (prefixWord ++ tailWord_932580).sum := by decide
  have hdescent : baseEnd_932580 < baseStart_932580 := by decide
  rcases family_descends (prefixWord ++ tailWord_932580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932597 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_932597 : Nat := 118140960795 + 932597 * 2 ^ 59
def prefixEnd_932597 : Nat := 4983230072969 + 3 ^ 40 * 932597 * 2
def baseEnd_932597 : Nat := 159623505980397647882857

theorem tailTrace_932597 : CollatzResearch.WordTrace tailWord_932597 prefixEnd_932597 159623505980397647882857 := by
  unfold tailWord_932597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014607002367818732188045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22676404668245212488125363 34014607002367818732188045)
  ·
    refine ⟨12755477625887932024570517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34014607002367818732188045 12755477625887932024570517)
    ·
      refine ⟨597913013713496813651743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12755477625887932024570517 597913013713496813651743)
      ·
        refine ⟨896869520570245220477615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597913013713496813651743 896869520570245220477615)
        ·
          refine ⟨1345304280855367830716423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896869520570245220477615 1345304280855367830716423)
          ·
            refine ⟨2017956421283051746074635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345304280855367830716423 2017956421283051746074635)
            ·
              refine ⟨3026934631924577619111953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017956421283051746074635 3026934631924577619111953)
              ·
                refine ⟨2270200973943433214333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026934631924577619111953 2270200973943433214333965)
                ·
                  refine ⟨851325365228787455375237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2270200973943433214333965 851325365228787455375237)
                  ·
                    refine ⟨159623505980397647882857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851325365228787455375237 159623505980397647882857)
                    ·
                      rfl

theorem cell23_932597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_932597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932597 prefixEnd_932597 := by exact prefixLift 932597
  have htrace : WordTrace (prefixWord ++ tailWord_932597) baseStart_932597 baseEnd_932597 := by
    simpa [prefixWord, tailWord_932597, baseEnd_932597] using wordTrace_append hprefix tailTrace_932597
  have hstable : (prefixWord ++ tailWord_932597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932597).length < 2 ^ (prefixWord ++ tailWord_932597).sum := by decide
  have hdescent : baseEnd_932597 < baseStart_932597 := by decide
  rcases family_descends (prefixWord ++ tailWord_932597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932637 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_932637 : Nat := 118140960795 + 932637 * 2 ^ 59
def prefixEnd_932637 : Nat := 4983230072969 + 3 ^ 40 * 932637 * 2
def baseEnd_932637 : Nat := 478891057167372787148387

theorem tailTrace_932637 : CollatzResearch.WordTrace tailWord_932637 prefixEnd_932637 478891057167372787148387 := by
  unfold tailWord_932637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34016065922222905563644165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22677377281481937042429443 34016065922222905563644165)
  ·
    refine ⟨6378012360416794793183281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34016065922222905563644165 6378012360416794793183281)
    ·
      refine ⟨4783509270312596094887461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6378012360416794793183281 4783509270312596094887461)
      ·
        refine ⟨896907988183611767791399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4783509270312596094887461 896907988183611767791399)
        ·
          refine ⟨1345361982275417651687099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896907988183611767791399 1345361982275417651687099)
          ·
            refine ⟨2018042973413126477530649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345361982275417651687099 2018042973413126477530649)
            ·
              refine ⟨1513532230059844858147987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018042973413126477530649 1513532230059844858147987)
              ·
                refine ⟨2270298345089767287221981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513532230059844858147987 2270298345089767287221981)
                ·
                  refine ⟨851361879408662732708243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2270298345089767287221981 851361879408662732708243)
                  ·
                    refine ⟨1277042819112994099062365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851361879408662732708243 1277042819112994099062365)
                    ·
                      refine ⟨478891057167372787148387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277042819112994099062365 478891057167372787148387)
                      ·
                        rfl

theorem cell23_932637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_932637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932637 prefixEnd_932637 := by exact prefixLift 932637
  have htrace : WordTrace (prefixWord ++ tailWord_932637) baseStart_932637 baseEnd_932637 := by
    simpa [prefixWord, tailWord_932637, baseEnd_932637] using wordTrace_append hprefix tailTrace_932637
  have hstable : (prefixWord ++ tailWord_932637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932637).length < 2 ^ (prefixWord ++ tailWord_932637).sum := by decide
  have hdescent : baseEnd_932637 < baseStart_932637 := by decide
  rcases family_descends (prefixWord ++ tailWord_932637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932663 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_932663 : Nat := 118140960795 + 932663 * 2 ^ 59
def prefixEnd_932663 : Nat := 4983230072969 + 3 ^ 40 * 932663 * 2
def baseEnd_932663 : Nat := 478904407664389685423267

theorem tailTrace_932663 : CollatzResearch.WordTrace tailWord_932663 prefixEnd_932663 478904407664389685423267 := by
  unfold tailWord_932663
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017014220128712004090643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678009480085808002727095 34017014220128712004090643)
  ·
    refine ⟨51025521330193068006135965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017014220128712004090643 51025521330193068006135965)
    ·
      refine ⟨19134570498822400502300987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51025521330193068006135965 19134570498822400502300987)
      ·
        refine ⟨28701855748233600753451481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134570498822400502300987 28701855748233600753451481)
        ·
          refine ⟨21526391811175200565088611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28701855748233600753451481 21526391811175200565088611)
          ·
            refine ⟨32289587716762800847632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21526391811175200565088611 32289587716762800847632917)
            ·
              refine ⟨1513574424223256289732793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32289587716762800847632917 1513574424223256289732793)
              ·
                refine ⟨1135180818167442217299595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513574424223256289732793 1135180818167442217299595)
                ·
                  refine ⟨1702771227251163325949393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135180818167442217299595 1702771227251163325949393)
                  ·
                    refine ⟨1277078420438372494462045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702771227251163325949393 1277078420438372494462045)
                    ·
                      refine ⟨478904407664389685423267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277078420438372494462045 478904407664389685423267)
                      ·
                        rfl

theorem cell23_932663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_932663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932663 prefixEnd_932663 := by exact prefixLift 932663
  have htrace : WordTrace (prefixWord ++ tailWord_932663) baseStart_932663 baseEnd_932663 := by
    simpa [prefixWord, tailWord_932663, baseEnd_932663] using wordTrace_append hprefix tailTrace_932663
  have hstable : (prefixWord ++ tailWord_932663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932663).length < 2 ^ (prefixWord ++ tailWord_932663).sum := by decide
  have hdescent : baseEnd_932663 < baseStart_932663 := by decide
  rcases family_descends (prefixWord ++ tailWord_932663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932666 : List Nat := [3, 1, 1, 1, 6, 1, 1, 9]
def baseStart_932666 : Nat := 118140960795 + 932666 * 2 ^ 59
def prefixEnd_932666 : Nat := 4983230072969 + 3 ^ 40 * 932666 * 2
def baseEnd_932666 : Nat := 17737257337272339766139

theorem tailTrace_932666 : CollatzResearch.WordTrace tailWord_932666 prefixEnd_932666 17737257337272339766139 := by
  unfold tailWord_932666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504280909779460879112463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22678082426078562344299901 8504280909779460879112463)
  ·
    refine ⟨12756421364669191318668695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504280909779460879112463 12756421364669191318668695)
    ·
      refine ⟨19134632047003786978003043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756421364669191318668695 19134632047003786978003043)
      ·
        refine ⟨28701948070505680467004565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134632047003786978003043 28701948070505680467004565)
        ·
          refine ⟨1345403815804953771890839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28701948070505680467004565 1345403815804953771890839)
          ·
            refine ⟨2018105723707430657836259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345403815804953771890839 2018105723707430657836259)
            ·
              refine ⟨3027158585561145986754389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018105723707430657836259 3027158585561145986754389)
              ·
                refine ⟨17737257337272339766139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3027158585561145986754389 17737257337272339766139)
                ·
                  rfl

theorem cell23_932666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_932666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932666 prefixEnd_932666 := by exact prefixLift 932666
  have htrace : WordTrace (prefixWord ++ tailWord_932666) baseStart_932666 baseEnd_932666 := by
    simpa [prefixWord, tailWord_932666, baseEnd_932666] using wordTrace_append hprefix tailTrace_932666
  have hstable : (prefixWord ++ tailWord_932666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932666).length < 2 ^ (prefixWord ++ tailWord_932666).sum := by decide
  have hdescent : baseEnd_932666 < baseStart_932666 := by decide
  rcases family_descends (prefixWord ++ tailWord_932666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932679 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 9]
def baseStart_932679 : Nat := 118140960795 + 932679 * 2 ^ 59
def prefixEnd_932679 : Nat := 4983230072969 + 3 ^ 40 * 932679 * 2
def baseEnd_932679 : Nat := 159637541118287207607731

theorem tailTrace_932679 : CollatzResearch.WordTrace tailWord_932679 prefixEnd_932679 159637541118287207607731 := by
  unfold tailWord_932679
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017597788070746736673091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678398525380497824448727 34017597788070746736673091)
  ·
    refine ⟨51026396682106120105009637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017597788070746736673091 51026396682106120105009637)
    ·
      refine ⟨9567449377894897519689307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51026396682106120105009637 9567449377894897519689307)
      ·
        refine ⟨14351174066842346279533961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567449377894897519689307 14351174066842346279533961)
        ·
          refine ⟨10763380550131759709650471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14351174066842346279533961 10763380550131759709650471)
          ·
            refine ⟨16145070825197639564475707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763380550131759709650471 16145070825197639564475707)
            ·
              refine ⟨24217606237796459346713561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16145070825197639564475707 24217606237796459346713561)
              ·
                refine ⟨18163204678347344510035171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24217606237796459346713561 18163204678347344510035171)
                ·
                  refine ⟨27244807017521016765052757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18163204678347344510035171 27244807017521016765052757)
                  ·
                    refine ⟨159637541118287207607731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27244807017521016765052757 159637541118287207607731)
                    ·
                      rfl

theorem cell23_932679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_932679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932679 prefixEnd_932679 := by exact prefixLift 932679
  have htrace : WordTrace (prefixWord ++ tailWord_932679) baseStart_932679 baseEnd_932679 := by
    simpa [prefixWord, tailWord_932679, baseEnd_932679] using wordTrace_append hprefix tailTrace_932679
  have hstable : (prefixWord ++ tailWord_932679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932679).length < 2 ^ (prefixWord ++ tailWord_932679).sum := by decide
  have hdescent : baseEnd_932679 < baseStart_932679 := by decide
  rcases family_descends (prefixWord ++ tailWord_932679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932693 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_932693 : Nat := 118140960795 + 932693 * 2 ^ 59
def prefixEnd_932693 : Nat := 4983230072969 + 3 ^ 40 * 932693 * 2
def baseEnd_932693 : Nat := 478919812084024568048129

theorem tailTrace_932693 : CollatzResearch.WordTrace tailWord_932693 prefixEnd_932693 478919812084024568048129 := by
  unfold tailWord_932693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018108410020027127682733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678738940013351418455155 34018108410020027127682733)
  ·
    refine ⟨12756790653757510172881025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34018108410020027127682733 12756790653757510172881025)
    ·
      refine ⟨9567592990318132629660769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12756790653757510172881025 9567592990318132629660769)
      ·
        refine ⟨7175694742738599472245577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9567592990318132629660769 7175694742738599472245577)
        ·
          refine ⟨5381771057053949604184183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7175694742738599472245577 5381771057053949604184183)
          ·
            refine ⟨8072656585580924406276275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381771057053949604184183 8072656585580924406276275)
            ·
              refine ⟨12108984878371386609414413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072656585580924406276275 12108984878371386609414413)
              ·
                refine ⟨4540869329389269978530405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12108984878371386609414413 4540869329389269978530405)
                ·
                  refine ⟨851412999260488120974451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4540869329389269978530405 851412999260488120974451)
                  ·
                    refine ⟨1277119498890732181461677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851412999260488120974451 1277119498890732181461677)
                    ·
                      refine ⟨478919812084024568048129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277119498890732181461677 478919812084024568048129)
                      ·
                        rfl

theorem cell23_932693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_932693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932693 prefixEnd_932693 := by exact prefixLift 932693
  have htrace : WordTrace (prefixWord ++ tailWord_932693) baseStart_932693 baseEnd_932693 := by
    simpa [prefixWord, tailWord_932693, baseEnd_932693] using wordTrace_append hprefix tailTrace_932693
  have hstable : (prefixWord ++ tailWord_932693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932693).length < 2 ^ (prefixWord ++ tailWord_932693).sum := by decide
  have hdescent : baseEnd_932693 < baseStart_932693 := by decide
  rcases family_descends (prefixWord ++ tailWord_932693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932703 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 3, 3, 2]
def baseStart_932703 : Nat := 118140960795 + 932703 * 2 ^ 59
def prefixEnd_932703 : Nat := 4983230072969 + 3 ^ 40 * 932703 * 2
def baseEnd_932703 : Nat := 478924946890569528923083

theorem tailTrace_932703 : CollatzResearch.WordTrace tailWord_932703 prefixEnd_932703 478924946890569528923083 := by
  unfold tailWord_932703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018473139983798835546763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678982093322532557031175 34018473139983798835546763)
  ·
    refine ⟨51027709709975698253320145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34018473139983798835546763 51027709709975698253320145)
    ·
      refine ⟨38270782282481773689990109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51027709709975698253320145 38270782282481773689990109)
      ·
        refine ⟨14351543355930665133746291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38270782282481773689990109 14351543355930665133746291)
        ·
          refine ⟨21527315033895997700619437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14351543355930665133746291 21527315033895997700619437)
          ·
            refine ⟨8072743137710999137732289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21527315033895997700619437 8072743137710999137732289)
            ·
              refine ⟨6054557353283249353299217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072743137710999137732289 6054557353283249353299217)
              ·
                refine ⟨4540918014962437014974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6054557353283249353299217 4540918014962437014974413)
                ·
                  refine ⟨1702844255610913880615405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4540918014962437014974413 1702844255610913880615405)
                  ·
                    refine ⟨638566595854092705230777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702844255610913880615405 638566595854092705230777)
                    ·
                      refine ⟨478924946890569528923083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638566595854092705230777 478924946890569528923083)
                      ·
                        rfl

theorem cell23_932703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_932703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932703 prefixEnd_932703 := by exact prefixLift 932703
  have htrace : WordTrace (prefixWord ++ tailWord_932703) baseStart_932703 baseEnd_932703 := by
    simpa [prefixWord, tailWord_932703, baseEnd_932703] using wordTrace_append hprefix tailTrace_932703
  have hstable : (prefixWord ++ tailWord_932703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932703).length < 2 ^ (prefixWord ++ tailWord_932703).sum := by decide
  have hdescent : baseEnd_932703 < baseStart_932703 := by decide
  rcases family_descends (prefixWord ++ tailWord_932703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932720 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2]
def baseStart_932720 : Nat := 118140960795 + 932720 * 2 ^ 59
def prefixEnd_932720 : Nat := 4983230072969 + 3 ^ 40 * 932720 * 2
def baseEnd_932720 : Nat := 478933676061695962410505

theorem tailTrace_932720 : CollatzResearch.WordTrace tailWord_932720 prefixEnd_932720 478933676061695962410505 := by
  unfold tailWord_932720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009546590461105369457807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22679395453948140492610409 17009546590461105369457807)
  ·
    refine ⟨25514319885691658054186711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17009546590461105369457807 25514319885691658054186711)
    ·
      refine ⟨38271479828537487081280067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25514319885691658054186711 38271479828537487081280067)
      ·
        refine ⟨57407219742806230621920101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38271479828537487081280067 57407219742806230621920101)
        ·
          refine ⟨10763853701776168241610019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57407219742806230621920101 10763853701776168241610019)
          ·
            refine ⟨16145780552664252362415029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763853701776168241610019 16145780552664252362415029)
            ·
              refine ⟨1513666926812273658976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16145780552664252362415029 1513666926812273658976409)
              ·
                refine ⟨1135250195109205244232307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513666926812273658976409 1135250195109205244232307)
                ·
                  refine ⟨1702875292663807866348461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135250195109205244232307 1702875292663807866348461)
                  ·
                    refine ⟨638578234748927949880673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702875292663807866348461 638578234748927949880673)
                    ·
                      refine ⟨478933676061695962410505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638578234748927949880673 478933676061695962410505)
                      ·
                        rfl

theorem cell23_932720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2].length) (baseStart_932720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932720 prefixEnd_932720 := by exact prefixLift 932720
  have htrace : WordTrace (prefixWord ++ tailWord_932720) baseStart_932720 baseEnd_932720 := by
    simpa [prefixWord, tailWord_932720, baseEnd_932720] using wordTrace_append hprefix tailTrace_932720
  have hstable : (prefixWord ++ tailWord_932720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932720).length < 2 ^ (prefixWord ++ tailWord_932720).sum := by decide
  have hdescent : baseEnd_932720 < baseStart_932720 := by decide
  rcases family_descends (prefixWord ++ tailWord_932720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932733 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_932733 : Nat := 118140960795 + 932733 * 2 ^ 59
def prefixEnd_932733 : Nat := 4983230072969 + 3 ^ 40 * 932733 * 2
def baseEnd_932733 : Nat := 478940351310204411547945

theorem tailTrace_932733 : CollatzResearch.WordTrace tailWord_932733 prefixEnd_932733 478940351310204411547945 := by
  unfold tailWord_932733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34019567329875113959138853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22679711553250075972759235 34019567329875113959138853)
  ·
    refine ⟨6378668874351583867338535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34019567329875113959138853 6378668874351583867338535)
    ·
      refine ⟨9568003311527375801007803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378668874351583867338535 9568003311527375801007803)
      ·
        refine ⟨14352004967291063701511705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568003311527375801007803 14352004967291063701511705)
        ·
          refine ⟨10764003725468297776133779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14352004967291063701511705 10764003725468297776133779)
          ·
            refine ⟨16146005588202446664200669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764003725468297776133779 16146005588202446664200669)
            ·
              refine ⟨6054752095575917499075251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16146005588202446664200669 6054752095575917499075251)
              ·
                refine ⟨9082128143363876248612877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6054752095575917499075251 9082128143363876248612877)
                ·
                  refine ⟨3405798053761453593229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9082128143363876248612877 3405798053761453593229829)
                  ·
                    refine ⟨638587135080272548730593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405798053761453593229829 638587135080272548730593)
                    ·
                      refine ⟨478940351310204411547945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638587135080272548730593 478940351310204411547945)
                      ·
                        rfl

theorem cell23_932733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_932733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932733 prefixEnd_932733 := by exact prefixLift 932733
  have htrace : WordTrace (prefixWord ++ tailWord_932733) baseStart_932733 baseEnd_932733 := by
    simpa [prefixWord, tailWord_932733, baseEnd_932733] using wordTrace_append hprefix tailTrace_932733
  have hstable : (prefixWord ++ tailWord_932733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932733).length < 2 ^ (prefixWord ++ tailWord_932733).sum := by decide
  have hdescent : baseEnd_932733 < baseStart_932733 := by decide
  rcases family_descends (prefixWord ++ tailWord_932733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932767 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 2, 2, 2]
def baseStart_932767 : Nat := 118140960795 + 932767 * 2 ^ 59
def prefixEnd_932767 : Nat := 4983230072969 + 3 ^ 40 * 932767 * 2
def baseEnd_932767 : Nat := 478957809652457278522789

theorem tailTrace_932767 : CollatzResearch.WordTrace tailWord_932767 prefixEnd_932767 478957809652457278522789 := by
  unfold tailWord_932767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020807411751937765876555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22680538274501291843917703 34020807411751937765876555)
  ·
    refine ⟨51031211117627906648814833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34020807411751937765876555 51031211117627906648814833)
    ·
      refine ⟨38273408338220929986611125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51031211117627906648814833 38273408338220929986611125)
      ·
        refine ⟨3588132031708212186244793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38273408338220929986611125 3588132031708212186244793)
        ·
          refine ⟨2691099023781159139683595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588132031708212186244793 2691099023781159139683595)
          ·
            refine ⟨4036648535671738709525393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691099023781159139683595 4036648535671738709525393)
            ·
              refine ⟨3027486401753804032144045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036648535671738709525393 3027486401753804032144045)
              ·
                refine ⟨1135307400657676512054017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3027486401753804032144045 1135307400657676512054017)
                ·
                  refine ⟨851480550493257384040513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135307400657676512054017 851480550493257384040513)
                  ·
                    refine ⟨638610412869943038030385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 851480550493257384040513 638610412869943038030385)
                    ·
                      refine ⟨478957809652457278522789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638610412869943038030385 478957809652457278522789)
                      ·
                        rfl

theorem cell23_932767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_932767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932767 prefixEnd_932767 := by exact prefixLift 932767
  have htrace : WordTrace (prefixWord ++ tailWord_932767) baseStart_932767 baseEnd_932767 := by
    simpa [prefixWord, tailWord_932767, baseEnd_932767] using wordTrace_append hprefix tailTrace_932767
  have hstable : (prefixWord ++ tailWord_932767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932767).length < 2 ^ (prefixWord ++ tailWord_932767).sum := by decide
  have hdescent : baseEnd_932767 < baseStart_932767 := by decide
  rcases family_descends (prefixWord ++ tailWord_932767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932823 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_932823 : Nat := 118140960795 + 932823 * 2 ^ 59
def prefixEnd_932823 : Nat := 4983230072969 + 3 ^ 40 * 932823 * 2
def baseEnd_932823 : Nat := 478986564569109059422531

theorem tailTrace_932823 : CollatzResearch.WordTrace tailWord_932823 prefixEnd_932823 478986564569109059422531 := by
  unfold tailWord_932823
  simp only [CollatzResearch.WordTrace]
  refine ⟨34022849899549059329915123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22681899933032706219943415 34022849899549059329915123)
  ·
    refine ⟨51034274849323588994872685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34022849899549059329915123 51034274849323588994872685)
    ·
      refine ⟨19137853068496345873077257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51034274849323588994872685 19137853068496345873077257)
      ·
        refine ⟨14353389801372259404807943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19137853068496345873077257 14353389801372259404807943)
        ·
          refine ⟨21530084702058389107211915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14353389801372259404807943 21530084702058389107211915)
          ·
            refine ⟨32295127053087583660817873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530084702058389107211915 32295127053087583660817873)
            ·
              refine ⟨24221345289815687745613405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32295127053087583660817873 24221345289815687745613405)
              ·
                refine ⟨9083004483680882904605027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24221345289815687745613405 9083004483680882904605027)
                ·
                  refine ⟨13624506725521324356907541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083004483680882904605027 13624506725521324356907541)
                  ·
                    refine ⟨638648752758812079230041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13624506725521324356907541 638648752758812079230041)
                    ·
                      refine ⟨478986564569109059422531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638648752758812079230041 478986564569109059422531)
                      ·
                        rfl

theorem cell23_932823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_932823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932823 prefixEnd_932823 := by exact prefixLift 932823
  have htrace : WordTrace (prefixWord ++ tailWord_932823) baseStart_932823 baseEnd_932823 := by
    simpa [prefixWord, tailWord_932823, baseEnd_932823] using wordTrace_append hprefix tailTrace_932823
  have hstable : (prefixWord ++ tailWord_932823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932823).length < 2 ^ (prefixWord ++ tailWord_932823).sum := by decide
  have hdescent : baseEnd_932823 < baseStart_932823 := by decide
  rcases family_descends (prefixWord ++ tailWord_932823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932836 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_932836 : Nat := 118140960795 + 932836 * 2 ^ 59
def prefixEnd_932836 : Nat := 4983230072969 + 3 ^ 40 * 932836 * 2
def baseEnd_932836 : Nat := 478993239817617508559971

theorem tailTrace_932836 : CollatzResearch.WordTrace tailWord_932836 prefixEnd_932836 478993239817617508559971 := by
  unfold tailWord_932836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011662024250981275069181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22682216032334641700092241 17011662024250981275069181)
  ·
    refine ⟨6379373259094117978150943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17011662024250981275069181 6379373259094117978150943)
    ·
      refine ⟨9569059888641176967226415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6379373259094117978150943 9569059888641176967226415)
      ·
        refine ⟨14353589832961765450839623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569059888641176967226415 14353589832961765450839623)
        ·
          refine ⟨21530384749442648176259435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14353589832961765450839623 21530384749442648176259435)
          ·
            refine ⟨32295577124163972264389153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530384749442648176259435 32295577124163972264389153)
            ·
              refine ⟨24221682843122979198291865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32295577124163972264389153 24221682843122979198291865)
              ·
                refine ⟨18166262132342234398718899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24221682843122979198291865 18166262132342234398718899)
                ·
                  refine ⟨27249393198513351598078349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166262132342234398718899 27249393198513351598078349)
                  ·
                    refine ⟨10218522449442506849279381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27249393198513351598078349 10218522449442506849279381)
                    ·
                      refine ⟨478993239817617508559971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10218522449442506849279381 478993239817617508559971)
                      ·
                        rfl

theorem cell23_932836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_932836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932836 prefixEnd_932836 := by exact prefixLift 932836
  have htrace : WordTrace (prefixWord ++ tailWord_932836) baseStart_932836 baseEnd_932836 := by
    simpa [prefixWord, tailWord_932836, baseEnd_932836] using wordTrace_append hprefix tailTrace_932836
  have hstable : (prefixWord ++ tailWord_932836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932836).length < 2 ^ (prefixWord ++ tailWord_932836).sum := by decide
  have hdescent : baseEnd_932836 < baseStart_932836 := by decide
  rcases family_descends (prefixWord ++ tailWord_932836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932860 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_932860 : Nat := 118140960795 + 932860 * 2 ^ 59
def prefixEnd_932860 : Nat := 4983230072969 + 3 ^ 40 * 932860 * 2
def baseEnd_932860 : Nat := 479005563353325414659861

theorem tailTrace_932860 : CollatzResearch.WordTrace tailWord_932860 prefixEnd_932860 479005563353325414659861 := by
  unfold tailWord_932860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17012099700207507324506017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22682799600276676432674689 17012099700207507324506017)
  ·
    refine ⟨12759074775155630493379513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17012099700207507324506017 12759074775155630493379513)
    ·
      refine ⟨9569306081366722870034635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12759074775155630493379513 9569306081366722870034635)
      ·
        refine ⟨14353959122050084305051953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569306081366722870034635 14353959122050084305051953)
        ·
          refine ⟨10765469341537563228788965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14353959122050084305051953 10765469341537563228788965)
          ·
            refine ⟨2018525501538293105397931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10765469341537563228788965 2018525501538293105397931)
            ·
              refine ⟨3027788252307439658096897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018525501538293105397931 3027788252307439658096897)
              ·
                refine ⟨2270841189230579743572673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027788252307439658096897 2270841189230579743572673)
                ·
                  refine ⟨1703130891922934807679505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270841189230579743572673 1703130891922934807679505)
                  ·
                    refine ⟨1277348168942201105759629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703130891922934807679505 1277348168942201105759629)
                    ·
                      refine ⟨479005563353325414659861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277348168942201105759629 479005563353325414659861)
                      ·
                        rfl

theorem cell23_932860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_932860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932860 prefixEnd_932860 := by exact prefixLift 932860
  have htrace : WordTrace (prefixWord ++ tailWord_932860) baseStart_932860 baseEnd_932860 := by
    simpa [prefixWord, tailWord_932860, baseEnd_932860] using wordTrace_append hprefix tailTrace_932860
  have hstable : (prefixWord ++ tailWord_932860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932860).length < 2 ^ (prefixWord ++ tailWord_932860).sum := by decide
  have hdescent : baseEnd_932860 < baseStart_932860 := by decide
  rcases family_descends (prefixWord ++ tailWord_932860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932890 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_932890 : Nat := 118140960795 + 932890 * 2 ^ 59
def prefixEnd_932890 : Nat := 4983230072969 + 3 ^ 40 * 932890 * 2
def baseEnd_932890 : Nat := 479020967772960297284723

theorem tailTrace_932890 : CollatzResearch.WordTrace tailWord_932890 prefixEnd_932890 479020967772960297284723 := by
  unfold tailWord_932890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506323397576582443151031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22683529060204219848402749 8506323397576582443151031)
  ·
    refine ⟨12759485096364873664726547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506323397576582443151031 12759485096364873664726547)
    ·
      refine ⟨19139227644547310497089821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12759485096364873664726547 19139227644547310497089821)
      ·
        refine ⟨7177210366705241436408683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19139227644547310497089821 7177210366705241436408683)
        ·
          refine ⟨10765815550057862154613025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177210366705241436408683 10765815550057862154613025)
          ·
            refine ⟨8074361662543396615959769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10765815550057862154613025 8074361662543396615959769)
            ·
              refine ⟨6055771246907547461969827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074361662543396615959769 6055771246907547461969827)
              ·
                refine ⟨9083656870361321192954741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055771246907547461969827 9083656870361321192954741)
                ·
                  refine ⟨851592831596373861839507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9083656870361321192954741 851592831596373861839507)
                  ·
                    refine ⟨1277389247394560792759261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851592831596373861839507 1277389247394560792759261)
                    ·
                      refine ⟨479020967772960297284723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277389247394560792759261 479020967772960297284723)
                      ·
                        rfl

theorem cell23_932890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_932890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932890 prefixEnd_932890 := by exact prefixLift 932890
  have htrace : WordTrace (prefixWord ++ tailWord_932890) baseStart_932890 baseEnd_932890 := by
    simpa [prefixWord, tailWord_932890, baseEnd_932890] using wordTrace_append hprefix tailTrace_932890
  have hstable : (prefixWord ++ tailWord_932890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932890).length < 2 ^ (prefixWord ++ tailWord_932890).sum := by decide
  have hdescent : baseEnd_932890 < baseStart_932890 := by decide
  rcases family_descends (prefixWord ++ tailWord_932890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932907 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 1, 1, 3]
def baseStart_932907 : Nat := 118140960795 + 932907 * 2 ^ 59
def prefixEnd_932907 : Nat := 4983230072969 + 3 ^ 40 * 932907 * 2
def baseEnd_932907 : Nat := 479029696944086730772145

theorem tailTrace_932907 : CollatzResearch.WordTrace tailWord_932907 prefixEnd_932907 479029696944086730772145 := by
  unfold tailWord_932907
  simp only [CollatzResearch.WordTrace]
  refine ⟨34025913631244741675972975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22683942420829827783981983 34025913631244741675972975)
  ·
    refine ⟨51038870446867112513959463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34025913631244741675972975 51038870446867112513959463)
    ·
      refine ⟨76558305670300668770939195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51038870446867112513959463 76558305670300668770939195)
      ·
        refine ⟨114837458505451003156408793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76558305670300668770939195 114837458505451003156408793)
        ·
          refine ⟨86128093879088252367306595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114837458505451003156408793 86128093879088252367306595)
          ·
            refine ⟨129192140818632378550959893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86128093879088252367306595 129192140818632378550959893)
            ·
              refine ⟨6055881600873392744576245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129192140818632378550959893 6055881600873392744576245)
              ·
                refine ⟨567738900081880569804023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6055881600873392744576245 567738900081880569804023)
                ·
                  refine ⟨851608350122820854706035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567738900081880569804023 851608350122820854706035)
                  ·
                    refine ⟨1277412525184231282059053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851608350122820854706035 1277412525184231282059053)
                    ·
                      refine ⟨479029696944086730772145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277412525184231282059053 479029696944086730772145)
                      ·
                        rfl

theorem cell23_932907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 1, 3].length) (baseStart_932907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932907 prefixEnd_932907 := by exact prefixLift 932907
  have htrace : WordTrace (prefixWord ++ tailWord_932907) baseStart_932907 baseEnd_932907 := by
    simpa [prefixWord, tailWord_932907, baseEnd_932907] using wordTrace_append hprefix tailTrace_932907
  have hstable : (prefixWord ++ tailWord_932907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932907).length < 2 ^ (prefixWord ++ tailWord_932907).sum := by decide
  have hdescent : baseEnd_932907 < baseStart_932907 := by decide
  rcases family_descends (prefixWord ++ tailWord_932907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932924 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_932924 : Nat := 118140960795 + 932924 * 2 ^ 59
def prefixEnd_932924 : Nat := 4983230072969 + 3 ^ 40 * 932924 * 2
def baseEnd_932924 : Nat := 479038426115213164259567

theorem tailTrace_932924 : CollatzResearch.WordTrace tailWord_932924 prefixEnd_932924 479038426115213164259567 := by
  unfold tailWord_932924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013266836091576789670913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22684355781455435719561217 17013266836091576789670913)
  ·
    refine ⟨12759950127068682592253185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17013266836091576789670913 12759950127068682592253185)
    ·
      refine ⟨9569962595301511944189889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12759950127068682592253185 9569962595301511944189889)
      ·
        refine ⟨7177471946476133958142417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9569962595301511944189889 7177471946476133958142417)
        ·
          refine ⟨5383103959857100468606813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177471946476133958142417 5383103959857100468606813)
          ·
            refine ⟨2018663984946412675727555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5383103959857100468606813 2018663984946412675727555)
            ·
              refine ⟨3027995977419619013591333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018663984946412675727555 3027995977419619013591333)
              ·
                refine ⟨567749245766178565048375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3027995977419619013591333 567749245766178565048375)
                ·
                  refine ⟨851623868649267847572563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567749245766178565048375 851623868649267847572563)
                  ·
                    refine ⟨1277435802973901771358845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851623868649267847572563 1277435802973901771358845)
                    ·
                      refine ⟨479038426115213164259567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277435802973901771358845 479038426115213164259567)
                      ·
                        rfl

theorem cell23_932924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_932924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932924 prefixEnd_932924 := by exact prefixLift 932924
  have htrace : WordTrace (prefixWord ++ tailWord_932924) baseStart_932924 baseEnd_932924 := by
    simpa [prefixWord, tailWord_932924, baseEnd_932924] using wordTrace_append hprefix tailTrace_932924
  have hstable : (prefixWord ++ tailWord_932924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932924).length < 2 ^ (prefixWord ++ tailWord_932924).sum := by decide
  have hdescent : baseEnd_932924 < baseStart_932924 := by decide
  rcases family_descends (prefixWord ++ tailWord_932924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932933 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_932933 : Nat := 118140960795 + 932933 * 2 ^ 59
def prefixEnd_932933 : Nat := 4983230072969 + 3 ^ 40 * 932933 * 2
def baseEnd_932933 : Nat := 479043047441103629047025

theorem tailTrace_932933 : CollatzResearch.WordTrace tailWord_932933 prefixEnd_932933 479043047441103629047025 := by
  unfold tailWord_932933
  simp only [CollatzResearch.WordTrace]
  refine ⟨34026861929150548116419453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22684574619433698744279635 34026861929150548116419453)
  ·
    refine ⟨12760073223431455543657295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34026861929150548116419453 12760073223431455543657295)
    ·
      refine ⟨19140109835147183315485943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12760073223431455543657295 19140109835147183315485943)
      ·
        refine ⟨28710164752720774973228915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19140109835147183315485943 28710164752720774973228915)
        ·
          refine ⟨43065247129081162459843373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28710164752720774973228915 43065247129081162459843373)
          ·
            refine ⟨16149467673405435922441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43065247129081162459843373 16149467673405435922441265)
            ·
              refine ⟨12112100755054076941830949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16149467673405435922441265 12112100755054076941830949)
              ·
                refine ⟨2271018891572639426593303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12112100755054076941830949 2271018891572639426593303)
                ·
                  refine ⟨3406528337358959139889955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271018891572639426593303 3406528337358959139889955)
                  ·
                    refine ⟨5109792506038438709834933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3406528337358959139889955 5109792506038438709834933)
                    ·
                      refine ⟨479043047441103629047025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5109792506038438709834933 479043047441103629047025)
                      ·
                        rfl

theorem cell23_932933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_932933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932933 prefixEnd_932933 := by exact prefixLift 932933
  have htrace : WordTrace (prefixWord ++ tailWord_932933) baseStart_932933 baseEnd_932933 := by
    simpa [prefixWord, tailWord_932933, baseEnd_932933] using wordTrace_append hprefix tailTrace_932933
  have hstable : (prefixWord ++ tailWord_932933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932933).length < 2 ^ (prefixWord ++ tailWord_932933).sum := by decide
  have hdescent : baseEnd_932933 < baseStart_932933 := by decide
  rcases family_descends (prefixWord ++ tailWord_932933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932958 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_932958 : Nat := 118140960795 + 932958 * 2 ^ 59
def prefixEnd_932958 : Nat := 4983230072969 + 3 ^ 40 * 932958 * 2
def baseEnd_932958 : Nat := 479055884457466031234411

theorem tailTrace_932958 : CollatzResearch.WordTrace tailWord_932958 prefixEnd_932958 479055884457466031234411 := by
  unfold tailWord_932958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253471719257497173259941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22685182502706651590719685 4253471719257497173259941)
  ·
    refine ⟨797525947360780719986239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4253471719257497173259941 797525947360780719986239)
    ·
      refine ⟨1196288921041171079979359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797525947360780719986239 1196288921041171079979359)
      ·
        refine ⟨1794433381561756619969039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196288921041171079979359 1794433381561756619969039)
        ·
          refine ⟨2691650072342634929953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794433381561756619969039 2691650072342634929953559)
          ·
            refine ⟨4037475108513952394930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691650072342634929953559 4037475108513952394930339)
            ·
              refine ⟨6056212662770928592395509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037475108513952394930339 6056212662770928592395509)
              ·
                refine ⟨567769937134774555537079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6056212662770928592395509 567769937134774555537079)
                ·
                  refine ⟨851654905702161833305619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567769937134774555537079 851654905702161833305619)
                  ·
                    refine ⟨1277482358553242749958429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851654905702161833305619 1277482358553242749958429)
                    ·
                      refine ⟨479055884457466031234411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277482358553242749958429 479055884457466031234411)
                      ·
                        rfl

theorem cell23_932958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_932958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932958 prefixEnd_932958 := by exact prefixLift 932958
  have htrace : WordTrace (prefixWord ++ tailWord_932958) baseStart_932958 baseEnd_932958 := by
    simpa [prefixWord, tailWord_932958, baseEnd_932958] using wordTrace_append hprefix tailTrace_932958
  have hstable : (prefixWord ++ tailWord_932958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932958).length < 2 ^ (prefixWord ++ tailWord_932958).sum := by decide
  have hdescent : baseEnd_932958 < baseStart_932958 := by decide
  rcases family_descends (prefixWord ++ tailWord_932958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932967 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_932967 : Nat := 118140960795 + 932967 * 2 ^ 59
def prefixEnd_932967 : Nat := 4983230072969 + 3 ^ 40 * 932967 * 2
def baseEnd_932967 : Nat := 479060505783356496021869

theorem tailTrace_932967 : CollatzResearch.WordTrace tailWord_932967 prefixEnd_932967 479060505783356496021869 := by
  unfold tailWord_932967
  simp only [CollatzResearch.WordTrace]
  refine ⟨34028102011027371923157155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22685401340684914615438103 34028102011027371923157155)
  ·
    refine ⟨51042153016541057884735733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34028102011027371923157155 51042153016541057884735733)
    ·
      refine ⟨4785201845300724176693975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51042153016541057884735733 4785201845300724176693975)
      ·
        refine ⟨7177802767951086265040963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785201845300724176693975 7177802767951086265040963)
        ·
          refine ⟨10766704151926629397561445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177802767951086265040963 10766704151926629397561445)
          ·
            refine ⟨2018757028486243012042771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10766704151926629397561445 2018757028486243012042771)
            ·
              refine ⟨3028135542729364518064157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018757028486243012042771 3028135542729364518064157)
              ·
                refine ⟨1135550828523511694274059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028135542729364518064157 1135550828523511694274059)
                ·
                  refine ⟨1703326242785267541411089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135550828523511694274059 1703326242785267541411089)
                  ·
                    refine ⟨1277494682088950656058317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703326242785267541411089 1277494682088950656058317)
                    ·
                      refine ⟨479060505783356496021869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277494682088950656058317 479060505783356496021869)
                      ·
                        rfl

theorem cell23_932967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_932967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932967 prefixEnd_932967 := by exact prefixLift 932967
  have htrace : WordTrace (prefixWord ++ tailWord_932967) baseStart_932967 baseEnd_932967 := by
    simpa [prefixWord, tailWord_932967, baseEnd_932967] using wordTrace_append hprefix tailTrace_932967
  have hstable : (prefixWord ++ tailWord_932967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932967).length < 2 ^ (prefixWord ++ tailWord_932967).sum := by decide
  have hdescent : baseEnd_932967 < baseStart_932967 := by decide
  rcases family_descends (prefixWord ++ tailWord_932967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932974 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_932974 : Nat := 118140960795 + 932974 * 2 ^ 59
def prefixEnd_932974 : Nat := 4983230072969 + 3 ^ 40 * 932974 * 2
def baseEnd_932974 : Nat := 159688033382645989544779

theorem tailTrace_932974 : CollatzResearch.WordTrace tailWord_932974 prefixEnd_932974 159688033382645989544779 := by
  unfold tailWord_932974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253544665250251514832747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22685571548001341412441317 4253544665250251514832747)
  ·
    refine ⟨6380316997875377272249121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253544665250251514832747 6380316997875377272249121)
    ·
      refine ⟨4785237748406532954186841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6380316997875377272249121 4785237748406532954186841)
      ·
        refine ⟨3588928311304899715640131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785237748406532954186841 3588928311304899715640131)
        ·
          refine ⟨5383392466957349573460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588928311304899715640131 5383392466957349573460197)
          ·
            refine ⟨1009386087554503045023787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5383392466957349573460197 1009386087554503045023787)
            ·
              refine ⟨1514079131331754567535681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009386087554503045023787 1514079131331754567535681)
              ·
                refine ⟨1135559348498815925651761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514079131331754567535681 1135559348498815925651761)
                ·
                  refine ⟨851669511374111944238821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135559348498815925651761 851669511374111944238821)
                  ·
                    refine ⟨159688033382645989544779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851669511374111944238821 159688033382645989544779)
                    ·
                      rfl

theorem cell23_932974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_932974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_932974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_932974 prefixEnd_932974 := by exact prefixLift 932974
  have htrace : WordTrace (prefixWord ++ tailWord_932974) baseStart_932974 baseEnd_932974 := by
    simpa [prefixWord, tailWord_932974, baseEnd_932974] using wordTrace_append hprefix tailTrace_932974
  have hstable : (prefixWord ++ tailWord_932974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932974).length < 2 ^ (prefixWord ++ tailWord_932974).sum := by decide
  have hdescent : baseEnd_932974 < baseStart_932974 := by decide
  rcases family_descends (prefixWord ++ tailWord_932974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933003 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_933003 : Nat := 118140960795 + 933003 * 2 ^ 59
def prefixEnd_933003 : Nat := 4983230072969 + 3 ^ 40 * 933003 * 2
def baseEnd_933003 : Nat := 479078991086918355171703

theorem tailTrace_933003 : CollatzResearch.WordTrace tailWord_933003 prefixEnd_933003 479078991086918355171703 := by
  unfold tailWord_933003
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029415038896950071467663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22686276692597966714311775 34029415038896950071467663)
  ·
    refine ⟨51044122558345425107201495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34029415038896950071467663 51044122558345425107201495)
    ·
      refine ⟨76566183837518137660802243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51044122558345425107201495 76566183837518137660802243)
      ·
        refine ⟨114849275756277206491203365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76566183837518137660802243 114849275756277206491203365)
        ·
          refine ⟨21534239204301976217100631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114849275756277206491203365 21534239204301976217100631)
          ·
            refine ⟨32301358806452964325650947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534239204301976217100631 32301358806452964325650947)
            ·
              refine ⟨48452038209679446488476421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32301358806452964325650947 48452038209679446488476421)
              ·
                refine ⟨9084757164314896216589329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48452038209679446488476421 9084757164314896216589329)
                ·
                  refine ⟨6813567873236172162441997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9084757164314896216589329 6813567873236172162441997)
                  ·
                    refine ⟨2555087952463564560915749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6813567873236172162441997 2555087952463564560915749)
                    ·
                      refine ⟨479078991086918355171703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2555087952463564560915749 479078991086918355171703)
                      ·
                        rfl

theorem cell23_933003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_933003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933003 prefixEnd_933003 := by exact prefixLift 933003
  have htrace : WordTrace (prefixWord ++ tailWord_933003) baseStart_933003 baseEnd_933003 := by
    simpa [prefixWord, tailWord_933003, baseEnd_933003] using wordTrace_append hprefix tailTrace_933003
  have hstable : (prefixWord ++ tailWord_933003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933003).length < 2 ^ (prefixWord ++ tailWord_933003).sum := by decide
  have hdescent : baseEnd_933003 < baseStart_933003 := by decide
  rcases family_descends (prefixWord ++ tailWord_933003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933010 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_933010 : Nat := 118140960795 + 933010 * 2 ^ 59
def prefixEnd_933010 : Nat := 4983230072969 + 3 ^ 40 * 933010 * 2
def baseEnd_933010 : Nat := 479082585451499827784171

theorem tailTrace_933010 : CollatzResearch.WordTrace tailWord_933010 prefixEnd_933010 479082585451499827784171 := by
  unfold tailWord_933010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507417587467897566743121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22686446899914393511314989 8507417587467897566743121)
  ·
    refine ⟨6380563190600923175057341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8507417587467897566743121 6380563190600923175057341)
    ·
      refine ⟨2392711196475346190646503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6380563190600923175057341 2392711196475346190646503)
      ·
        refine ⟨3589066794713019285969755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392711196475346190646503 3589066794713019285969755)
        ·
          refine ⟨5383600192069528928954633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589066794713019285969755 5383600192069528928954633)
          ·
            refine ⟨4037700144052146696715975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383600192069528928954633 4037700144052146696715975)
            ·
              refine ⟨6056550216078220045073963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037700144052146696715975 6056550216078220045073963)
              ·
                refine ⟨9084825324117330067610945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056550216078220045073963 9084825324117330067610945)
                ·
                  refine ⟨6813618993087997550708209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9084825324117330067610945 6813618993087997550708209)
                  ·
                    refine ⟨5110214244815998163031157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813618993087997550708209 5110214244815998163031157)
                    ·
                      refine ⟨479082585451499827784171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5110214244815998163031157 479082585451499827784171)
                      ·
                        rfl

theorem cell23_933010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_933010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933010 prefixEnd_933010 := by exact prefixLift 933010
  have htrace : WordTrace (prefixWord ++ tailWord_933010) baseStart_933010 baseEnd_933010 := by
    simpa [prefixWord, tailWord_933010, baseEnd_933010] using wordTrace_append hprefix tailTrace_933010
  have hstable : (prefixWord ++ tailWord_933010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933010).length < 2 ^ (prefixWord ++ tailWord_933010).sum := by decide
  have hdescent : baseEnd_933010 < baseStart_933010 := by decide
  rcases family_descends (prefixWord ++ tailWord_933010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933013 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_933013 : Nat := 118140960795 + 933013 * 2 ^ 59
def prefixEnd_933013 : Nat := 4983230072969 + 3 ^ 40 * 933013 * 2
def baseEnd_933013 : Nat := 159694708631154438682219

theorem tailTrace_933013 : CollatzResearch.WordTrace tailWord_933013 prefixEnd_933013 159694708631154438682219 := by
  unfold tailWord_933013
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029779768860721779331693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22686519845907147852887795 34029779768860721779331693)
  ·
    refine ⟨12761167413322770667249385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34029779768860721779331693 12761167413322770667249385)
    ·
      refine ⟨9570875559992078000437039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12761167413322770667249385 9570875559992078000437039)
      ·
        refine ⟨14356313339988117000655559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570875559992078000437039 14356313339988117000655559)
        ·
          refine ⟨21534470009982175500983339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356313339988117000655559 21534470009982175500983339)
          ·
            refine ⟨32301705014973263251475009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534470009982175500983339 32301705014973263251475009)
            ·
              refine ⟨24226278761229947438606257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32301705014973263251475009 24226278761229947438606257)
              ·
                refine ⟨18169709070922460578954693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24226278761229947438606257 18169709070922460578954693)
                ·
                  refine ⟨3406820450797961358554005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18169709070922460578954693 3406820450797961358554005)
                  ·
                    refine ⟨159694708631154438682219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3406820450797961358554005 159694708631154438682219)
                    ·
                      rfl

theorem cell23_933013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_933013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933013 prefixEnd_933013 := by exact prefixLift 933013
  have htrace : WordTrace (prefixWord ++ tailWord_933013) baseStart_933013 baseEnd_933013 := by
    simpa [prefixWord, tailWord_933013, baseEnd_933013] using wordTrace_append hprefix tailTrace_933013
  have hstable : (prefixWord ++ tailWord_933013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933013).length < 2 ^ (prefixWord ++ tailWord_933013).sum := by decide
  have hdescent : baseEnd_933013 < baseStart_933013 := by decide
  rcases family_descends (prefixWord ++ tailWord_933013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933033 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_933033 : Nat := 118140960795 + 933033 * 2 ^ 59
def prefixEnd_933033 : Nat := 4983230072969 + 3 ^ 40 * 933033 * 2
def baseEnd_933033 : Nat := 479094395506553237796565

theorem tailTrace_933033 : CollatzResearch.WordTrace tailWord_933033 prefixEnd_933033 479094395506553237796565 := by
  unfold tailWord_933033
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030509228788265195059753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22687006152525510130039835 34030509228788265195059753)
  ·
    refine ⟨25522881921591198896294815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34030509228788265195059753 25522881921591198896294815)
    ·
      refine ⟨38284322882386798344442223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25522881921591198896294815 38284322882386798344442223)
      ·
        refine ⟨57426484323580197516663335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38284322882386798344442223 57426484323580197516663335)
        ·
          refine ⟨86139726485370296274995003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57426484323580197516663335 86139726485370296274995003)
          ·
            refine ⟨129209589728055444412492505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86139726485370296274995003 129209589728055444412492505)
            ·
              refine ⟨96907192296041583309369379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129209589728055444412492505 96907192296041583309369379)
              ·
                refine ⟨145360788444062374964054069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96907192296041583309369379 145360788444062374964054069)
                ·
                  refine ⟨13627573916630847652880069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145360788444062374964054069 13627573916630847652880069)
                  ·
                    refine ⟨2555170109368283934915013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13627573916630847652880069 2555170109368283934915013)
                    ·
                      refine ⟨479094395506553237796565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2555170109368283934915013 479094395506553237796565)
                      ·
                        rfl

theorem cell23_933033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_933033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933033 prefixEnd_933033 := by exact prefixLift 933033
  have htrace : WordTrace (prefixWord ++ tailWord_933033) baseStart_933033 baseEnd_933033 := by
    simpa [prefixWord, tailWord_933033, baseEnd_933033] using wordTrace_append hprefix tailTrace_933033
  have hstable : (prefixWord ++ tailWord_933033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933033).length < 2 ^ (prefixWord ++ tailWord_933033).sum := by decide
  have hdescent : baseEnd_933033 < baseStart_933033 := by decide
  rcases family_descends (prefixWord ++ tailWord_933033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933057 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_933057 : Nat := 118140960795 + 933057 * 2 ^ 59
def prefixEnd_933057 : Nat := 4983230072969 + 3 ^ 40 * 933057 * 2
def baseEnd_933057 : Nat := 479106719042261143896455

theorem tailTrace_933057 : CollatzResearch.WordTrace tailWord_933057 prefixEnd_933057 479106719042261143896455 := by
  unfold tailWord_933057
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031384580701317293933425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22687589720467544862622283 34031384580701317293933425)
  ·
    refine ⟨25523538435525987970450069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34031384580701317293933425 25523538435525987970450069)
    ·
      refine ⟨1196415864165280686114847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25523538435525987970450069 1196415864165280686114847)
      ·
        refine ⟨1794623796247921029172271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196415864165280686114847 1794623796247921029172271)
        ·
          refine ⟨2691935694371881543758407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794623796247921029172271 2691935694371881543758407)
          ·
            refine ⟨4037903541557822315637611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691935694371881543758407 4037903541557822315637611)
            ·
              refine ⟨6056855312336733473456417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037903541557822315637611 6056855312336733473456417)
              ·
                refine ⟨4542641484252550105092313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056855312336733473456417 4542641484252550105092313)
                ·
                  refine ⟨3406981113189412578819235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542641484252550105092313 3406981113189412578819235)
                  ·
                    refine ⟨5110471669784118868228853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3406981113189412578819235 5110471669784118868228853)
                    ·
                      refine ⟨479106719042261143896455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5110471669784118868228853 479106719042261143896455)
                      ·
                        rfl

theorem cell23_933057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_933057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933057 prefixEnd_933057 := by exact prefixLift 933057
  have htrace : WordTrace (prefixWord ++ tailWord_933057) baseStart_933057 baseEnd_933057 := by
    simpa [prefixWord, tailWord_933057, baseEnd_933057] using wordTrace_append hprefix tailTrace_933057
  have hstable : (prefixWord ++ tailWord_933057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933057).length < 2 ^ (prefixWord ++ tailWord_933057).sum := by decide
  have hdescent : baseEnd_933057 < baseStart_933057 := by decide
  rcases family_descends (prefixWord ++ tailWord_933057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933058 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_933058 : Nat := 118140960795 + 933058 * 2 ^ 59
def prefixEnd_933058 : Nat := 4983230072969 + 3 ^ 40 * 933058 * 2
def baseEnd_933058 : Nat := 479107232522915639983951

theorem tailTrace_933058 : CollatzResearch.WordTrace tailWord_933058 prefixEnd_933058 479107232522915639983951 := by
  unfold tailWord_933058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507855263424423616179957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22687614035798462976479885 8507855263424423616179957)
  ·
    refine ⟨797611430946039714016871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8507855263424423616179957 797611430946039714016871)
    ·
      refine ⟨1196417146419059571025307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797611430946039714016871 1196417146419059571025307)
      ·
        refine ⟨1794625719628589356537961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196417146419059571025307 1794625719628589356537961)
        ·
          refine ⟨1345969289721442017403471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794625719628589356537961 1345969289721442017403471)
          ·
            refine ⟨2018953934582163026105207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345969289721442017403471 2018953934582163026105207)
            ·
              refine ⟨3028430901873244539157811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018953934582163026105207 3028430901873244539157811)
              ·
                refine ⟨4542646352809866808736717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028430901873244539157811 4542646352809866808736717)
                ·
                  refine ⟨1703492382303700053276269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542646352809866808736717 1703492382303700053276269)
                  ·
                    refine ⟨638809643363887519978601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703492382303700053276269 638809643363887519978601)
                    ·
                      refine ⟨479107232522915639983951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 638809643363887519978601 479107232522915639983951)
                      ·
                        rfl

theorem cell23_933058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_933058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933058 prefixEnd_933058 := by exact prefixLift 933058
  have htrace : WordTrace (prefixWord ++ tailWord_933058) baseStart_933058 baseEnd_933058 := by
    simpa [prefixWord, tailWord_933058, baseEnd_933058] using wordTrace_append hprefix tailTrace_933058
  have hstable : (prefixWord ++ tailWord_933058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933058).length < 2 ^ (prefixWord ++ tailWord_933058).sum := by decide
  have hdescent : baseEnd_933058 < baseStart_933058 := by decide
  rcases family_descends (prefixWord ++ tailWord_933058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933063 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_933063 : Nat := 118140960795 + 933063 * 2 ^ 59
def prefixEnd_933063 : Nat := 4983230072969 + 3 ^ 40 * 933063 * 2
def baseEnd_933063 : Nat := 479109799926188120421427

theorem tailTrace_933063 : CollatzResearch.WordTrace tailWord_933063 prefixEnd_933063 479109799926188120421427 := by
  unfold tailWord_933063
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031603418679580318651843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22687735612453053545767895 34031603418679580318651843)
  ·
    refine ⟨51047405128019370477977765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34031603418679580318651843 51047405128019370477977765)
    ·
      refine ⟨9571388461503631964620831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51047405128019370477977765 9571388461503631964620831)
      ·
        refine ⟨14357082692255447946931247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9571388461503631964620831 14357082692255447946931247)
        ·
          refine ⟨21535624038383171920396871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14357082692255447946931247 21535624038383171920396871)
          ·
            refine ⟨32303436057574757880595307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21535624038383171920396871 32303436057574757880595307)
            ·
              refine ⟨48455154086362136820892961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32303436057574757880595307 48455154086362136820892961)
              ·
                refine ⟨36341365564771602615669721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48455154086362136820892961 36341365564771602615669721)
                ·
                  refine ⟨27256024173578701961752291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36341365564771602615669721 27256024173578701961752291)
                  ·
                    refine ⟨40884036260368052942628437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27256024173578701961752291 40884036260368052942628437)
                    ·
                      refine ⟨479109799926188120421427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 40884036260368052942628437 479109799926188120421427)
                      ·
                        rfl

theorem cell23_933063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_933063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933063 prefixEnd_933063 := by exact prefixLift 933063
  have htrace : WordTrace (prefixWord ++ tailWord_933063) baseStart_933063 baseEnd_933063 := by
    simpa [prefixWord, tailWord_933063, baseEnd_933063] using wordTrace_append hprefix tailTrace_933063
  have hstable : (prefixWord ++ tailWord_933063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933063).length < 2 ^ (prefixWord ++ tailWord_933063).sum := by decide
  have hdescent : baseEnd_933063 < baseStart_933063 := by decide
  rcases family_descends (prefixWord ++ tailWord_933063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933100 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_933100 : Nat := 118140960795 + 933100 * 2 ^ 59
def prefixEnd_933100 : Nat := 4983230072969 + 3 ^ 40 * 933100 * 2
def baseEnd_933100 : Nat := 479128798710404475658757

theorem tailTrace_933100 : CollatzResearch.WordTrace tailWord_933100 prefixEnd_933100 479128798710404475658757 := by
  unfold tailWord_933100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016476459772767818874377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22688635279697023758499169 17016476459772767818874377)
  ·
    refine ⟨12762357344829575864155783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17016476459772767818874377 12762357344829575864155783)
    ·
      refine ⟨19143536017244363796233675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12762357344829575864155783 19143536017244363796233675)
      ·
        refine ⟨28715304025866545694350513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143536017244363796233675 28715304025866545694350513)
        ·
          refine ⟨21536478019399909270762885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28715304025866545694350513 21536478019399909270762885)
          ·
            refine ⟨4038089628637482988268041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21536478019399909270762885 4038089628637482988268041)
            ·
              refine ⟨3028567221478112241201031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038089628637482988268041 3028567221478112241201031)
              ·
                refine ⟨4542850832217168361801547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028567221478112241201031 4542850832217168361801547)
                ·
                  refine ⟨6814276248325752542702321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542850832217168361801547 6814276248325752542702321)
                  ·
                    refine ⟨5110707186244314407026741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6814276248325752542702321 5110707186244314407026741)
                    ·
                      refine ⟨479128798710404475658757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5110707186244314407026741 479128798710404475658757)
                      ·
                        rfl

theorem cell23_933100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_933100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933100 prefixEnd_933100 := by exact prefixLift 933100
  have htrace : WordTrace (prefixWord ++ tailWord_933100) baseStart_933100 baseEnd_933100 := by
    simpa [prefixWord, tailWord_933100, baseEnd_933100] using wordTrace_append hprefix tailTrace_933100
  have hstable : (prefixWord ++ tailWord_933100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933100).length < 2 ^ (prefixWord ++ tailWord_933100).sum := by decide
  have hdescent : baseEnd_933100 < baseStart_933100 := by decide
  rcases family_descends (prefixWord ++ tailWord_933100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933124 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_933124 : Nat := 118140960795 + 933124 * 2 ^ 59
def prefixEnd_933124 : Nat := 4983230072969 + 3 ^ 40 * 933124 * 2
def baseEnd_933124 : Nat := 159713707415370793919549

theorem tailTrace_933124 : CollatzResearch.WordTrace tailWord_933124 prefixEnd_933124 159713707415370793919549 := by
  unfold tailWord_933124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016914135729293868311213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22689218847639058491081617 17016914135729293868311213)
  ·
    refine ⟨6381342800898485200616705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17016914135729293868311213 6381342800898485200616705)
    ·
      refine ⟨4786007100673863900462529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6381342800898485200616705 4786007100673863900462529)
      ·
        refine ⟨3589505325505397925346897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4786007100673863900462529 3589505325505397925346897)
        ·
          refine ⟨2692128994129048444010173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589505325505397925346897 2692128994129048444010173)
          ·
            refine ⟨1009548372798393166503815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2692128994129048444010173 1009548372798393166503815)
            ·
              refine ⟨1514322559197589749755723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009548372798393166503815 1514322559197589749755723)
              ·
                refine ⟨2271483838796384624633585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514322559197589749755723 2271483838796384624633585)
                ·
                  refine ⟨1703612879097288468475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2271483838796384624633585 1703612879097288468475189)
                  ·
                    refine ⟨159713707415370793919549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1703612879097288468475189 159713707415370793919549)
                    ·
                      rfl

theorem cell23_933124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_933124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933124 prefixEnd_933124 := by exact prefixLift 933124
  have htrace : WordTrace (prefixWord ++ tailWord_933124) baseStart_933124 baseEnd_933124 := by
    simpa [prefixWord, tailWord_933124, baseEnd_933124] using wordTrace_append hprefix tailTrace_933124
  have hstable : (prefixWord ++ tailWord_933124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933124).length < 2 ^ (prefixWord ++ tailWord_933124).sum := by decide
  have hdescent : baseEnd_933124 < baseStart_933124 := by decide
  rcases family_descends (prefixWord ++ tailWord_933124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933188 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_933188 : Nat := 118140960795 + 933188 * 2 ^ 59
def prefixEnd_933188 : Nat := 4983230072969 + 3 ^ 40 * 933188 * 2
def baseEnd_933188 : Nat := 159724661669333377119451

theorem tailTrace_933188 : CollatzResearch.WordTrace tailWord_933188 prefixEnd_933188 159724661669333377119451 := by
  unfold tailWord_933188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018081271613363333476109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22690775028817817777968145 17018081271613363333476109)
  ·
    refine ⟨6381780476855011250053541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17018081271613363333476109 6381780476855011250053541)
    ·
      refine ⟨1196583839410314609385039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6381780476855011250053541 1196583839410314609385039)
      ·
        refine ⟨1794875759115471914077559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196583839410314609385039 1794875759115471914077559)
        ·
          refine ⟨2692313638673207871116339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794875759115471914077559 2692313638673207871116339)
          ·
            refine ⟨4038470458009811806674509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692313638673207871116339 4038470458009811806674509)
            ·
              refine ⟨1514426421753679427502941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4038470458009811806674509 1514426421753679427502941)
              ·
                refine ⟨567909908157629785313603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514426421753679427502941 567909908157629785313603)
                ·
                  refine ⟨851864862236444677970405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567909908157629785313603 851864862236444677970405)
                  ·
                    refine ⟨159724661669333377119451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851864862236444677970405 159724661669333377119451)
                    ·
                      rfl

theorem cell23_933188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_933188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933188 prefixEnd_933188 := by exact prefixLift 933188
  have htrace : WordTrace (prefixWord ++ tailWord_933188) baseStart_933188 baseEnd_933188 := by
    simpa [prefixWord, tailWord_933188, baseEnd_933188] using wordTrace_append hprefix tailTrace_933188
  have hstable : (prefixWord ++ tailWord_933188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933188).length < 2 ^ (prefixWord ++ tailWord_933188).sum := by decide
  have hdescent : baseEnd_933188 < baseStart_933188 := by decide
  rcases family_descends (prefixWord ++ tailWord_933188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933251 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 1, 1, 4]
def baseStart_933251 : Nat := 118140960795 + 933251 * 2 ^ 59
def prefixEnd_933251 : Nat := 4983230072969 + 3 ^ 40 * 933251 * 2
def baseEnd_933251 : Nat := 479206334289233384870563

theorem tailTrace_933251 : CollatzResearch.WordTrace tailWord_933251 prefixEnd_933251 479206334289233384870563 := by
  unfold tailWord_933251
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038460341998488426495607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22692306894665658950997071 34038460341998488426495607)
  ·
    refine ⟨51057690512997732639743411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34038460341998488426495607 51057690512997732639743411)
    ·
      refine ⟨76586535769496598959615117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51057690512997732639743411 76586535769496598959615117)
      ·
        refine ⟨28719950913561224609855669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76586535769496598959615117 28719950913561224609855669)
        ·
          refine ⟨2692495398146364807173969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28719950913561224609855669 2692495398146364807173969)
          ·
            refine ⟨2019371548609773605380477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2692495398146364807173969 2019371548609773605380477)
            ·
              refine ⟨757264330728665102017679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2019371548609773605380477 757264330728665102017679)
              ·
                refine ⟨1135896496092997653026519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757264330728665102017679 1135896496092997653026519)
                ·
                  refine ⟨1703844744139496479539779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135896496092997653026519 1703844744139496479539779)
                  ·
                    refine ⟨2555767116209244719309669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1703844744139496479539779 2555767116209244719309669)
                    ·
                      refine ⟨479206334289233384870563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2555767116209244719309669 479206334289233384870563)
                      ·
                        rfl

theorem cell23_933251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_933251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933251 prefixEnd_933251 := by exact prefixLift 933251
  have htrace : WordTrace (prefixWord ++ tailWord_933251) baseStart_933251 baseEnd_933251 := by
    simpa [prefixWord, tailWord_933251, baseEnd_933251] using wordTrace_append hprefix tailTrace_933251
  have hstable : (prefixWord ++ tailWord_933251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933251).length < 2 ^ (prefixWord ++ tailWord_933251).sum := by decide
  have hdescent : baseEnd_933251 < baseStart_933251 := by decide
  rcases family_descends (prefixWord ++ tailWord_933251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933257 : List Nat := [1, 2, 1, 1, 8, 10]
def baseStart_933257 : Nat := 118140960795 + 933257 * 2 ^ 59
def prefixEnd_933257 : Nat := 4983230072969 + 3 ^ 40 * 933257 * 2
def baseEnd_933257 : Nat := 1972055206473910952245

theorem tailTrace_933257 : CollatzResearch.WordTrace tailWord_933257 prefixEnd_933257 1972055206473910952245 := by
  unfold tailWord_933257
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038679179976751451214025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22692452786651167634142683 34038679179976751451214025)
  ·
    refine ⟨25529009384982563588410519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34038679179976751451214025 25529009384982563588410519)
    ·
      refine ⟨38293514077473845382615779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25529009384982563588410519 38293514077473845382615779)
      ·
        refine ⟨57440271116210768073923669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38293514077473845382615779 57440271116210768073923669)
        ·
          refine ⟨673128177143094938366293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 57440271116210768073923669 673128177143094938366293)
          ·
            refine ⟨1972055206473910952245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 673128177143094938366293 1972055206473910952245)
            ·
              rfl

theorem cell23_933257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 10].length) (baseStart_933257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933257 prefixEnd_933257 := by exact prefixLift 933257
  have htrace : WordTrace (prefixWord ++ tailWord_933257) baseStart_933257 baseEnd_933257 := by
    simpa [prefixWord, tailWord_933257, baseEnd_933257] using wordTrace_append hprefix tailTrace_933257
  have hstable : (prefixWord ++ tailWord_933257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933257).length < 2 ^ (prefixWord ++ tailWord_933257).sum := by decide
  have hdescent : baseEnd_933257 < baseStart_933257 := by decide
  rcases family_descends (prefixWord ++ tailWord_933257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933262 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_933262 : Nat := 118140960795 + 933262 * 2 ^ 59
def prefixEnd_933262 : Nat := 4983230072969 + 3 ^ 40 * 933262 * 2
def baseEnd_933262 : Nat := 479211982576432841833013

theorem tailTrace_933262 : CollatzResearch.WordTrace tailWord_933262 prefixEnd_933262 479211982576432841833013 := by
  unfold tailWord_933262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254857693119829663143255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22692574363305758203430693 4254857693119829663143255)
  ·
    refine ⟨6382286539679744494714883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254857693119829663143255 6382286539679744494714883)
    ·
      refine ⟨9573429809519616742072325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382286539679744494714883 9573429809519616742072325)
      ·
        refine ⟨1795018089284928139138561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9573429809519616742072325 1795018089284928139138561)
        ·
          refine ⟨1346263566963696104353921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795018089284928139138561 1346263566963696104353921)
          ·
            refine ⟨1009697675222772078265441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346263566963696104353921 1009697675222772078265441)
            ·
              refine ⟨757273256417079058699081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009697675222772078265441 757273256417079058699081)
              ·
                refine ⟨567954942312809294024311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757273256417079058699081 567954942312809294024311)
                ·
                  refine ⟨851932413469213941036467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567954942312809294024311 851932413469213941036467)
                  ·
                    refine ⟨1277898620203820911554701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851932413469213941036467 1277898620203820911554701)
                    ·
                      refine ⟨479211982576432841833013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277898620203820911554701 479211982576432841833013)
                      ·
                        rfl

theorem cell23_933262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_933262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933262 prefixEnd_933262 := by exact prefixLift 933262
  have htrace : WordTrace (prefixWord ++ tailWord_933262) baseStart_933262 baseEnd_933262 := by
    simpa [prefixWord, tailWord_933262, baseEnd_933262] using wordTrace_append hprefix tailTrace_933262
  have hstable : (prefixWord ++ tailWord_933262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933262).length < 2 ^ (prefixWord ++ tailWord_933262).sum := by decide
  have hdescent : baseEnd_933262 < baseStart_933262 := by decide
  rcases family_descends (prefixWord ++ tailWord_933262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933284 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_933284 : Nat := 118140960795 + 933284 * 2 ^ 59
def prefixEnd_933284 : Nat := 4983230072969 + 3 ^ 40 * 933284 * 2
def baseEnd_933284 : Nat := 479223279150831755757911

theorem tailTrace_933284 : CollatzResearch.WordTrace tailWord_933284 prefixEnd_933284 479223279150831755757911 := by
  unfold tailWord_933284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019831975439467531223453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22693109300585956708297937 17019831975439467531223453)
  ·
    refine ⟨6382436990789800324208795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17019831975439467531223453 6382436990789800324208795)
    ·
      refine ⟨9573655486184700486313193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382436990789800324208795 9573655486184700486313193)
      ·
        refine ⟨7180241614638525364734895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9573655486184700486313193 7180241614638525364734895)
        ·
          refine ⟨10770362421957788047102343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180241614638525364734895 10770362421957788047102343)
          ·
            refine ⟨16155543632936682070653515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770362421957788047102343 16155543632936682070653515)
            ·
              refine ⟨24233315449405023105980273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155543632936682070653515 24233315449405023105980273)
              ·
                refine ⟨18174986587053767329485205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24233315449405023105980273 18174986587053767329485205)
                ·
                  refine ⟨851952496268145343569619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18174986587053767329485205 851952496268145343569619)
                  ·
                    refine ⟨1277928744402218015354429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851952496268145343569619 1277928744402218015354429)
                    ·
                      refine ⟨479223279150831755757911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277928744402218015354429 479223279150831755757911)
                      ·
                        rfl

theorem cell23_933284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_933284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933284 prefixEnd_933284 := by exact prefixLift 933284
  have htrace : WordTrace (prefixWord ++ tailWord_933284) baseStart_933284 baseEnd_933284 := by
    simpa [prefixWord, tailWord_933284, baseEnd_933284] using wordTrace_append hprefix tailTrace_933284
  have hstable : (prefixWord ++ tailWord_933284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933284).length < 2 ^ (prefixWord ++ tailWord_933284).sum := by decide
  have hdescent : baseEnd_933284 < baseStart_933284 := by decide
  rcases family_descends (prefixWord ++ tailWord_933284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933287 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 7]
def baseStart_933287 : Nat := 118140960795 + 933287 * 2 ^ 59
def prefixEnd_933287 : Nat := 4983230072969 + 3 ^ 40 * 933287 * 2
def baseEnd_933287 : Nat := 159741606530931748006799

theorem tailTrace_933287 : CollatzResearch.WordTrace tailWord_933287 prefixEnd_933287 159741606530931748006799 := by
  unfold tailWord_933287
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039773369868066574806115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693182246578711049870743 34039773369868066574806115)
  ·
    refine ⟨51059660054802099862209173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34039773369868066574806115 51059660054802099862209173)
    ·
      refine ⟨2393421565068848431041055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51059660054802099862209173 2393421565068848431041055)
      ·
        refine ⟨3590132347603272646561583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393421565068848431041055 3590132347603272646561583)
        ·
          refine ⟨5385198521404908969842375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590132347603272646561583 5385198521404908969842375)
          ·
            refine ⟨8077797782107363454763563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385198521404908969842375 8077797782107363454763563)
            ·
              refine ⟨12116696673161045182145345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077797782107363454763563 12116696673161045182145345)
              ·
                refine ⟨9087522504870783886609009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116696673161045182145345 9087522504870783886609009)
                ·
                  refine ⟨6815641878653087914956757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087522504870783886609009 6815641878653087914956757)
                  ·
                    refine ⟨159741606530931748006799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6815641878653087914956757 159741606530931748006799)
                    ·
                      rfl

theorem cell23_933287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_933287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933287 prefixEnd_933287 := by exact prefixLift 933287
  have htrace : WordTrace (prefixWord ++ tailWord_933287) baseStart_933287 baseEnd_933287 := by
    simpa [prefixWord, tailWord_933287, baseEnd_933287] using wordTrace_append hprefix tailTrace_933287
  have hstable : (prefixWord ++ tailWord_933287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933287).length < 2 ^ (prefixWord ++ tailWord_933287).sum := by decide
  have hdescent : baseEnd_933287 < baseStart_933287 := by decide
  rcases family_descends (prefixWord ++ tailWord_933287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933297 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_933297 : Nat := 118140960795 + 933297 * 2 ^ 59
def prefixEnd_933297 : Nat := 4983230072969 + 3 ^ 40 * 933297 * 2
def baseEnd_933297 : Nat := 479229954399340204895351

theorem tailTrace_933297 : CollatzResearch.WordTrace tailWord_933297 prefixEnd_933297 479229954399340204895351 := by
  unfold tailWord_933297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040138099831838282670145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693425399887892188446763 34040138099831838282670145)
  ·
    refine ⟨25530103574873878712002609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34040138099831838282670145 25530103574873878712002609)
    ·
      refine ⟨19147577681155409034001957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25530103574873878712002609 19147577681155409034001957)
      ·
        refine ⟨3590170815216639193875367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19147577681155409034001957 3590170815216639193875367)
        ·
          refine ⟨5385256222824958790813051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590170815216639193875367 5385256222824958790813051)
          ·
            refine ⟨8077884334237438186219577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385256222824958790813051 8077884334237438186219577)
            ·
              refine ⟨6058413250678078639664683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077884334237438186219577 6058413250678078639664683)
              ·
                refine ⟨9087619876017117959497025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058413250678078639664683 9087619876017117959497025)
                ·
                  refine ⟨6815714907012838469622769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087619876017117959497025 6815714907012838469622769)
                  ·
                    refine ⟨5111786180259628852217077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6815714907012838469622769 5111786180259628852217077)
                    ·
                      refine ⟨479229954399340204895351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5111786180259628852217077 479229954399340204895351)
                      ·
                        rfl

theorem cell23_933297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_933297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933297 prefixEnd_933297 := by exact prefixLift 933297
  have htrace : WordTrace (prefixWord ++ tailWord_933297) baseStart_933297 baseEnd_933297 := by
    simpa [prefixWord, tailWord_933297, baseEnd_933297] using wordTrace_append hprefix tailTrace_933297
  have hstable : (prefixWord ++ tailWord_933297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933297).length < 2 ^ (prefixWord ++ tailWord_933297).sum := by decide
  have hdescent : baseEnd_933297 < baseStart_933297 := by decide
  rcases family_descends (prefixWord ++ tailWord_933297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933305 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 1, 2, 3]
def baseStart_933305 : Nat := 118140960795 + 933305 * 2 ^ 59
def prefixEnd_933305 : Nat := 4983230072969 + 3 ^ 40 * 933305 * 2
def baseEnd_933305 : Nat := 479234062244576173595315

theorem tailTrace_933305 : CollatzResearch.WordTrace tailWord_933305 prefixEnd_933305 479234062244576173595315 := by
  unfold tailWord_933305
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040429883802855648961369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693619922535237099307579 34040429883802855648961369)
  ·
    refine ⟨25530322412852141736721027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34040429883802855648961369 25530322412852141736721027)
    ·
      refine ⟨38295483619278212605081541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25530322412852141736721027 38295483619278212605081541)
      ·
        refine ⟨7180403178614664863452789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38295483619278212605081541 7180403178614664863452789)
        ·
          refine ⟨673162797995124830948699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7180403178614664863452789 673162797995124830948699)
          ·
            refine ⟨1009744196992687246423049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673162797995124830948699 1009744196992687246423049)
            ·
              refine ⟨757308147744515434817287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009744196992687246423049 757308147744515434817287)
              ·
                refine ⟨1135962221616773152225931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757308147744515434817287 1135962221616773152225931)
                ·
                  refine ⟨1703943332425159728338897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135962221616773152225931 1703943332425159728338897)
                  ·
                    refine ⟨1277957499318869796254173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703943332425159728338897 1277957499318869796254173)
                    ·
                      refine ⟨479234062244576173595315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277957499318869796254173 479234062244576173595315)
                      ·
                        rfl

theorem cell23_933305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_933305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933305 prefixEnd_933305 := by exact prefixLift 933305
  have htrace : WordTrace (prefixWord ++ tailWord_933305) baseStart_933305 baseEnd_933305 := by
    simpa [prefixWord, tailWord_933305, baseEnd_933305] using wordTrace_append hprefix tailTrace_933305
  have hstable : (prefixWord ++ tailWord_933305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933305).length < 2 ^ (prefixWord ++ tailWord_933305).sum := by decide
  have hdescent : baseEnd_933305 < baseStart_933305 := by decide
  rcases family_descends (prefixWord ++ tailWord_933305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933327 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_933327 : Nat := 118140960795 + 933327 * 2 ^ 59
def prefixEnd_933327 : Nat := 4983230072969 + 3 ^ 40 * 933327 * 2
def baseEnd_933327 : Nat := 479245358818975087520213

theorem tailTrace_933327 : CollatzResearch.WordTrace tailWord_933327 prefixEnd_933327 479245358818975087520213 := by
  unfold tailWord_933327
  simp only [CollatzResearch.WordTrace]
  refine ⟨34041232289723153406262235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22694154859815435604174823 34041232289723153406262235)
  ·
    refine ⟨51061848434584730109393353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34041232289723153406262235 51061848434584730109393353)
    ·
      refine ⟨38296386325938547582045015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51061848434584730109393353 38296386325938547582045015)
      ·
        refine ⟨57444579488907821373067523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38296386325938547582045015 57444579488907821373067523)
        ·
          refine ⟨86166869233361732059601285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57444579488907821373067523 86166869233361732059601285)
          ·
            refine ⟨16156287981255324761175241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86166869233361732059601285 16156287981255324761175241)
            ·
              refine ⟨12117215985941493570881431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16156287981255324761175241 12117215985941493570881431)
              ·
                refine ⟨18175823978912240356322147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117215985941493570881431 18175823978912240356322147)
                ·
                  refine ⟨27263735968368360534483221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18175823978912240356322147 27263735968368360534483221)
                  ·
                    refine ⟨1277987623517266900053901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27263735968368360534483221 1277987623517266900053901)
                    ·
                      refine ⟨479245358818975087520213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1277987623517266900053901 479245358818975087520213)
                      ·
                        rfl

theorem cell23_933327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_933327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933327 prefixEnd_933327 := by exact prefixLift 933327
  have htrace : WordTrace (prefixWord ++ tailWord_933327) baseStart_933327 baseEnd_933327 := by
    simpa [prefixWord, tailWord_933327, baseEnd_933327] using wordTrace_append hprefix tailTrace_933327
  have hstable : (prefixWord ++ tailWord_933327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933327).length < 2 ^ (prefixWord ++ tailWord_933327).sum := by decide
  have hdescent : baseEnd_933327 < baseStart_933327 := by decide
  rcases family_descends (prefixWord ++ tailWord_933327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933407 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 8]
def baseStart_933407 : Nat := 118140960795 + 933407 * 2 ^ 59
def prefixEnd_933407 : Nat := 4983230072969 + 3 ^ 40 * 933407 * 2
def baseEnd_933407 : Nat := 159762145757111591506615

theorem tailTrace_933407 : CollatzResearch.WordTrace tailWord_933407 prefixEnd_933407 159762145757111591506615 := by
  unfold tailWord_933407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34044150129433327069174475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22696100086288884712782983 34044150129433327069174475)
  ·
    refine ⟨51066225194149990603761713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34044150129433327069174475 51066225194149990603761713)
    ·
      refine ⟨38299668895612492952821285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51066225194149990603761713 38299668895612492952821285)
      ·
        refine ⟨7181187917927342428653991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38299668895612492952821285 7181187917927342428653991)
        ·
          refine ⟨10771781876891013642980987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181187917927342428653991 10771781876891013642980987)
          ·
            refine ⟨16157672815336520464471481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771781876891013642980987 16157672815336520464471481)
            ·
              refine ⟨12118254611502390348353611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16157672815336520464471481 12118254611502390348353611)
              ·
                refine ⟨18177381917253585522530417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118254611502390348353611 18177381917253585522530417)
                ·
                  refine ⟨13633036437940189141897813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18177381917253585522530417 13633036437940189141897813)
                  ·
                    refine ⟨159762145757111591506615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13633036437940189141897813 159762145757111591506615)
                    ·
                      rfl

theorem cell23_933407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_933407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933407 prefixEnd_933407 := by exact prefixLift 933407
  have htrace : WordTrace (prefixWord ++ tailWord_933407) baseStart_933407 baseEnd_933407 := by
    simpa [prefixWord, tailWord_933407, baseEnd_933407] using wordTrace_append hprefix tailTrace_933407
  have hstable : (prefixWord ++ tailWord_933407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933407).length < 2 ^ (prefixWord ++ tailWord_933407).sum := by decide
  have hdescent : baseEnd_933407 < baseStart_933407 := by decide
  rcases family_descends (prefixWord ++ tailWord_933407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933411 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 2, 5]
def baseStart_933411 : Nat := 118140960795 + 933411 * 2 ^ 59
def prefixEnd_933411 : Nat := 4983230072969 + 3 ^ 40 * 933411 * 2
def baseEnd_933411 : Nat := 159762830397984252956609

theorem tailTrace_933411 : CollatzResearch.WordTrace tailWord_933411 prefixEnd_933411 159762830397984252956609 := by
  unfold tailWord_933411
  simp only [CollatzResearch.WordTrace]
  refine ⟨34044296021418835752320087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22696197347612557168213391 34044296021418835752320087)
  ·
    refine ⟨51066444032128253628480131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34044296021418835752320087 51066444032128253628480131)
    ·
      refine ⟨76599666048192380442720197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51066444032128253628480131 76599666048192380442720197)
      ·
        refine ⟨14362437384036071333010037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76599666048192380442720197 14362437384036071333010037)
        ·
          refine ⟨1346478504753381687469691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14362437384036071333010037 1346478504753381687469691)
          ·
            refine ⟨2019717757130072531204537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346478504753381687469691 2019717757130072531204537)
            ·
              refine ⟨1514788317847554398403403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019717757130072531204537 1514788317847554398403403)
              ·
                refine ⟨2272182476771331597605105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514788317847554398403403 2272182476771331597605105)
                ·
                  refine ⟨1704136857578498698203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272182476771331597605105 1704136857578498698203829)
                  ·
                    refine ⟨159762830397984252956609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1704136857578498698203829 159762830397984252956609)
                    ·
                      rfl

theorem cell23_933411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].length) (baseStart_933411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933411 prefixEnd_933411 := by exact prefixLift 933411
  have htrace : WordTrace (prefixWord ++ tailWord_933411) baseStart_933411 baseEnd_933411 := by
    simpa [prefixWord, tailWord_933411, baseEnd_933411] using wordTrace_append hprefix tailTrace_933411
  have hstable : (prefixWord ++ tailWord_933411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933411).length < 2 ^ (prefixWord ++ tailWord_933411).sum := by decide
  have hdescent : baseEnd_933411 < baseStart_933411 := by decide
  rcases family_descends (prefixWord ++ tailWord_933411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933441 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_933441 : Nat := 118140960795 + 933441 * 2 ^ 59
def prefixEnd_933441 : Nat := 4983230072969 + 3 ^ 40 * 933441 * 2
def baseEnd_933441 : Nat := 159767965204529213831563

theorem tailTrace_933441 : CollatzResearch.WordTrace tailWord_933441 prefixEnd_933441 159767965204529213831563 := by
  unfold tailWord_933441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34045390211310150875912177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22696926807540100583941451 34045390211310150875912177)
  ·
    refine ⟨25534042658482613156934133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34045390211310150875912177 25534042658482613156934133)
    ·
      refine ⟨2393816499232744983462575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25534042658482613156934133 2393816499232744983462575)
      ·
        refine ⟨3590724748849117475193863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393816499232744983462575 3590724748849117475193863)
        ·
          refine ⟨5386087123273676212790795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590724748849117475193863 5386087123273676212790795)
          ·
            refine ⟨8079130684910514319186193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386087123273676212790795 8079130684910514319186193)
            ·
              refine ⟨6059348013682885739389645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079130684910514319186193 6059348013682885739389645)
              ·
                refine ⟨2272255505131082152271117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059348013682885739389645 2272255505131082152271117)
                ·
                  refine ⟨852095814424155807101669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2272255505131082152271117 852095814424155807101669)
                  ·
                    refine ⟨159767965204529213831563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852095814424155807101669 159767965204529213831563)
                    ·
                      rfl

theorem cell23_933441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_933441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933441 prefixEnd_933441 := by exact prefixLift 933441
  have htrace : WordTrace (prefixWord ++ tailWord_933441) baseStart_933441 baseEnd_933441 := by
    simpa [prefixWord, tailWord_933441, baseEnd_933441] using wordTrace_append hprefix tailTrace_933441
  have hstable : (prefixWord ++ tailWord_933441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933441).length < 2 ^ (prefixWord ++ tailWord_933441).sum := by decide
  have hdescent : baseEnd_933441 < baseStart_933441 := by decide
  rcases family_descends (prefixWord ++ tailWord_933441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933462 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_933462 : Nat := 118140960795 + 933462 * 2 ^ 59
def prefixEnd_933462 : Nat := 4983230072969 + 3 ^ 40 * 933462 * 2
def baseEnd_933462 : Nat := 159771559569110686444031

theorem tailTrace_933462 : CollatzResearch.WordTrace tailWord_933462 prefixEnd_933462 159771559569110686444031 := by
  unfold tailWord_933462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127884759014629466401665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22697437429489380974951093 2127884759014629466401665)
  ·
    refine ⟨1595913569260972099801249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127884759014629466401665 1595913569260972099801249)
    ·
      refine ⟨1196935176945729074850937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595913569260972099801249 1196935176945729074850937)
      ·
        refine ⟨897701382709296806138203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1196935176945729074850937 897701382709296806138203)
        ·
          refine ⟨1346552074063945209207305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897701382709296806138203 1346552074063945209207305)
          ·
            refine ⟨1009914055547958906905479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346552074063945209207305 1009914055547958906905479)
            ·
              refine ⟨1514871083321938360358219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009914055547958906905479 1514871083321938360358219)
              ·
                refine ⟨2272306624982907540537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514871083321938360358219 2272306624982907540537329)
                ·
                  refine ⟨1704229968737180655402997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272306624982907540537329 1704229968737180655402997)
                  ·
                    refine ⟨159771559569110686444031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1704229968737180655402997 159771559569110686444031)
                    ·
                      rfl

theorem cell23_933462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_933462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933462 prefixEnd_933462 := by exact prefixLift 933462
  have htrace : WordTrace (prefixWord ++ tailWord_933462) baseStart_933462 baseEnd_933462 := by
    simpa [prefixWord, tailWord_933462, baseEnd_933462] using wordTrace_append hprefix tailTrace_933462
  have hstable : (prefixWord ++ tailWord_933462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933462).length < 2 ^ (prefixWord ++ tailWord_933462).sum := by decide
  have hdescent : baseEnd_933462 < baseStart_933462 := by decide
  rcases family_descends (prefixWord ++ tailWord_933462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933468 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_933468 : Nat := 118140960795 + 933468 * 2 ^ 59
def prefixEnd_933468 : Nat := 4983230072969 + 3 ^ 40 * 933468 * 2
def baseEnd_933468 : Nat := 479317759591259035857065

theorem tailTrace_933468 : CollatzResearch.WordTrace tailWord_933468 prefixEnd_933468 479317759591259035857065 := by
  unfold tailWord_933468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023187491106167243572529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22697583321474889658096705 17023187491106167243572529)
  ·
    refine ⟨12767390618329625432679397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17023187491106167243572529 12767390618329625432679397)
    ·
      refine ⟨2393885740936804768627387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12767390618329625432679397 2393885740936804768627387)
      ·
        refine ⟨3590828611405207152941081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393885740936804768627387 3590828611405207152941081)
        ·
          refine ⟨2693121458553905364705811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590828611405207152941081 2693121458553905364705811)
          ·
            refine ⟨4039682187830858047058717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693121458553905364705811 4039682187830858047058717)
            ·
              refine ⟨1514880820436571767647019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4039682187830858047058717 1514880820436571767647019)
              ·
                refine ⟨2272321230654857651470529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514880820436571767647019 2272321230654857651470529)
                ·
                  refine ⟨1704240922991143238602897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272321230654857651470529 1704240922991143238602897)
                  ·
                    refine ⟨1278180692243357428952173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704240922991143238602897 1278180692243357428952173)
                    ·
                      refine ⟨479317759591259035857065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1278180692243357428952173 479317759591259035857065)
                      ·
                        rfl

theorem cell23_933468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_933468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933468 prefixEnd_933468 := by exact prefixLift 933468
  have htrace : WordTrace (prefixWord ++ tailWord_933468) baseStart_933468 baseEnd_933468 := by
    simpa [prefixWord, tailWord_933468, baseEnd_933468] using wordTrace_append hprefix tailTrace_933468
  have hstable : (prefixWord ++ tailWord_933468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933468).length < 2 ^ (prefixWord ++ tailWord_933468).sum := by decide
  have hdescent : baseEnd_933468 < baseStart_933468 := by decide
  rcases family_descends (prefixWord ++ tailWord_933468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933518 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_933518 : Nat := 118140960795 + 933518 * 2 ^ 59
def prefixEnd_933518 : Nat := 4983230072969 + 3 ^ 40 * 933518 * 2
def baseEnd_933518 : Nat := 159781144541327946743945

theorem tailTrace_933518 : CollatzResearch.WordTrace tailWord_933518 prefixEnd_933518 159781144541327946743945 := by
  unfold tailWord_933518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256024829003899128308151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22698799088020795350976805 4256024829003899128308151)
  ·
    refine ⟨6384037243505848692462227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256024829003899128308151 6384037243505848692462227)
    ·
      refine ⟨9576055865258773038693341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384037243505848692462227 9576055865258773038693341)
      ·
        refine ⟨3591020949472039889510003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9576055865258773038693341 3591020949472039889510003)
        ·
          refine ⟨5386531424208059834265005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591020949472039889510003 5386531424208059834265005)
          ·
            refine ⟨2019949284078022437849377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5386531424208059834265005 2019949284078022437849377)
            ·
              refine ⟨1514961963058516828387033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019949284078022437849377 1514961963058516828387033)
              ·
                refine ⟨1136221472293887621290275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514961963058516828387033 1136221472293887621290275)
                ·
                  refine ⟨1704332208440831431935413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136221472293887621290275 1704332208440831431935413)
                  ·
                    refine ⟨159781144541327946743945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1704332208440831431935413 159781144541327946743945)
                    ·
                      rfl

theorem cell23_933518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_933518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933518 prefixEnd_933518 := by exact prefixLift 933518
  have htrace : WordTrace (prefixWord ++ tailWord_933518) baseStart_933518 baseEnd_933518 := by
    simpa [prefixWord, tailWord_933518, baseEnd_933518] using wordTrace_append hprefix tailTrace_933518
  have hstable : (prefixWord ++ tailWord_933518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933518).length < 2 ^ (prefixWord ++ tailWord_933518).sum := by decide
  have hdescent : baseEnd_933518 < baseStart_933518 := by decide
  rcases family_descends (prefixWord ++ tailWord_933518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933584 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_933584 : Nat := 118140960795 + 933584 * 2 ^ 59
def prefixEnd_933584 : Nat := 4983230072969 + 3 ^ 40 * 933584 * 2
def baseEnd_933584 : Nat := 479377323347180582006531

theorem tailTrace_933584 : CollatzResearch.WordTrace tailWord_933584 prefixEnd_933584 479377323347180582006531 := by
  unfold tailWord_933584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025302924896043149183903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22700403899861390865578537 17025302924896043149183903)
  ·
    refine ⟨25537954387344064723775855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17025302924896043149183903 25537954387344064723775855)
    ·
      refine ⟨38306931581016097085663783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25537954387344064723775855 38306931581016097085663783)
      ·
        refine ⟨57460397371524145628495675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38306931581016097085663783 57460397371524145628495675)
        ·
          refine ⟨86190596057286218442743513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57460397371524145628495675 86190596057286218442743513)
          ·
            refine ⟨64642947042964663832057635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86190596057286218442743513 64642947042964663832057635)
            ·
              refine ⟨96964420564446995748086453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64642947042964663832057635 96964420564446995748086453)
              ·
                refine ⟨9090414427916905851383105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96964420564446995748086453 9090414427916905851383105)
                ·
                  refine ⟨6817810820937679388537329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090414427916905851383105 6817810820937679388537329)
                  ·
                    refine ⟨5113358115703259541402997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817810820937679388537329 5113358115703259541402997)
                    ·
                      refine ⟨479377323347180582006531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5113358115703259541402997 479377323347180582006531)
                      ·
                        rfl

theorem cell23_933584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_933584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933584 prefixEnd_933584 := by exact prefixLift 933584
  have htrace : WordTrace (prefixWord ++ tailWord_933584) baseStart_933584 baseEnd_933584 := by
    simpa [prefixWord, tailWord_933584, baseEnd_933584] using wordTrace_append hprefix tailTrace_933584
  have hstable : (prefixWord ++ tailWord_933584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933584).length < 2 ^ (prefixWord ++ tailWord_933584).sum := by decide
  have hdescent : baseEnd_933584 < baseStart_933584 := by decide
  rcases family_descends (prefixWord ++ tailWord_933584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933588 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_933588 : Nat := 118140960795 + 933588 * 2 ^ 59
def prefixEnd_933588 : Nat := 4983230072969 + 3 ^ 40 * 933588 * 2
def baseEnd_933588 : Nat := 479379377269798566356513

theorem tailTrace_933588 : CollatzResearch.WordTrace tailWord_933588 prefixEnd_933588 479379377269798566356513 := by
  unfold tailWord_933588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025375870888797490756709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22700501161185063321008945 17025375870888797490756709)
  ·
    refine ⟨3192257975791649529516883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17025375870888797490756709 3192257975791649529516883)
    ·
      refine ⟨4788386963687474294275325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192257975791649529516883 4788386963687474294275325)
      ·
        refine ⟨1795645111382802860353247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4788386963687474294275325 1795645111382802860353247)
        ·
          refine ⟨2693467667074204290529871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795645111382802860353247 2693467667074204290529871)
          ·
            refine ⟨4040201500611306435794807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693467667074204290529871 4040201500611306435794807)
            ·
              refine ⟨6060302250916959653692211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040201500611306435794807 6060302250916959653692211)
              ·
                refine ⟨9090453376375439480538317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060302250916959653692211 9090453376375439480538317)
                ·
                  refine ⟨3408920016140789805201869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9090453376375439480538317 3408920016140789805201869)
                  ·
                    refine ⟨1278345006052796176950701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408920016140789805201869 1278345006052796176950701)
                    ·
                      refine ⟨479379377269798566356513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1278345006052796176950701 479379377269798566356513)
                      ·
                        rfl

theorem cell23_933588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_933588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933588 prefixEnd_933588 := by exact prefixLift 933588
  have htrace : WordTrace (prefixWord ++ tailWord_933588) baseStart_933588 baseEnd_933588 := by
    simpa [prefixWord, tailWord_933588, baseEnd_933588] using wordTrace_append hprefix tailTrace_933588
  have hstable : (prefixWord ++ tailWord_933588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933588).length < 2 ^ (prefixWord ++ tailWord_933588).sum := by decide
  have hdescent : baseEnd_933588 < baseStart_933588 := by decide
  rcases family_descends (prefixWord ++ tailWord_933588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933605 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_933605 : Nat := 118140960795 + 933605 * 2 ^ 59
def prefixEnd_933605 : Nat := 4983230072969 + 3 ^ 40 * 933605 * 2
def baseEnd_933605 : Nat := 479388106440924999843935

theorem tailTrace_933605 : CollatzResearch.WordTrace tailWord_933605 prefixEnd_933605 479388106440924999843935 := by
  unfold tailWord_933605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051371782716006884882269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22700914521810671256588179 34051371782716006884882269)
  ·
    refine ⟨12769264418518502581830851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34051371782716006884882269 12769264418518502581830851)
    ·
      refine ⟨19153896627777753872746277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769264418518502581830851 19153896627777753872746277)
      ·
        refine ⟨3591355617708328851139927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19153896627777753872746277 3591355617708328851139927)
        ·
          refine ⟨5387033426562493276709891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591355617708328851139927 5387033426562493276709891)
          ·
            refine ⟨8080550139843739915064837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387033426562493276709891 8080550139843739915064837)
            ·
              refine ⟨1515103151220701234074657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8080550139843739915064837 1515103151220701234074657)
              ·
                refine ⟨1136327363415525925555993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515103151220701234074657 1136327363415525925555993)
                ·
                  refine ⟨852245522561644444166995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136327363415525925555993 852245522561644444166995)
                  ·
                    refine ⟨1278368283842466666250493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 852245522561644444166995 1278368283842466666250493)
                    ·
                      refine ⟨479388106440924999843935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1278368283842466666250493 479388106440924999843935)
                      ·
                        rfl

theorem cell23_933605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_933605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933605 prefixEnd_933605 := by exact prefixLift 933605
  have htrace : WordTrace (prefixWord ++ tailWord_933605) baseStart_933605 baseEnd_933605 := by
    simpa [prefixWord, tailWord_933605, baseEnd_933605] using wordTrace_append hprefix tailTrace_933605
  have hstable : (prefixWord ++ tailWord_933605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933605).length < 2 ^ (prefixWord ++ tailWord_933605).sum := by decide
  have hdescent : baseEnd_933605 < baseStart_933605 := by decide
  rcases family_descends (prefixWord ++ tailWord_933605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933668 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 7]
def baseStart_933668 : Nat := 118140960795 + 933668 * 2 ^ 59
def prefixEnd_933668 : Nat := 4983230072969 + 3 ^ 40 * 933668 * 2
def baseEnd_933668 : Nat := 53268939524684250372905

theorem tailTrace_933668 : CollatzResearch.WordTrace tailWord_933668 prefixEnd_933668 53268939524684250372905 := by
  unfold tailWord_933668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17026834790743884322212829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22702446387658512429617105 17026834790743884322212829)
  ·
    refine ⟨6385063046528956620829811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17026834790743884322212829 6385063046528956620829811)
    ·
      refine ⟨9577594569793434931244717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385063046528956620829811 9577594569793434931244717)
      ·
        refine ⟨3591597963672538099216769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9577594569793434931244717 3591597963672538099216769)
        ·
          refine ⟨2693698472754403574412577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591597963672538099216769 2693698472754403574412577)
          ·
            refine ⟨2020273854565802680809433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693698472754403574412577 2020273854565802680809433)
            ·
              refine ⟨1515205390924352010607075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020273854565802680809433 1515205390924352010607075)
              ·
                refine ⟨2272808086386528015910613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515205390924352010607075 2272808086386528015910613)
                ·
                  refine ⟨53268939524684250372905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2272808086386528015910613 53268939524684250372905)
                  ·
                    rfl

theorem cell23_933668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_933668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933668 prefixEnd_933668 := by exact prefixLift 933668
  have htrace : WordTrace (prefixWord ++ tailWord_933668) baseStart_933668 baseEnd_933668 := by
    simpa [prefixWord, tailWord_933668, baseEnd_933668] using wordTrace_append hprefix tailTrace_933668
  have hstable : (prefixWord ++ tailWord_933668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933668).length < 2 ^ (prefixWord ++ tailWord_933668).sum := by decide
  have hdescent : baseEnd_933668 < baseStart_933668 := by decide
  rcases family_descends (prefixWord ++ tailWord_933668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933681 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_933681 : Nat := 118140960795 + 933681 * 2 ^ 59
def prefixEnd_933681 : Nat := 4983230072969 + 3 ^ 40 * 933681 * 2
def baseEnd_933681 : Nat := 159809043656888900831195

theorem tailTrace_933681 : CollatzResearch.WordTrace tailWord_933681 prefixEnd_933681 159809043656888900831195 := by
  unfold tailWord_933681
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054143730440671864648897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22702762486960447909765931 34054143730440671864648897)
  ·
    refine ⟨25540607797830503898486673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34054143730440671864648897 25540607797830503898486673)
    ·
      refine ⟨19155455848372877923865005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25540607797830503898486673 19155455848372877923865005)
      ·
        refine ⟨7183295943139829221449377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19155455848372877923865005 7183295943139829221449377)
        ·
          refine ⟨5387471957354871916087033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183295943139829221449377 5387471957354871916087033)
          ·
            refine ⟨4040603968016153937065275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387471957354871916087033 4040603968016153937065275)
            ·
              refine ⟨6060905952024230905597913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040603968016153937065275 6060905952024230905597913)
              ·
                refine ⟨4545679464018173179198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060905952024230905597913 4545679464018173179198435)
                ·
                  refine ⟨6818519196027259768797653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545679464018173179198435 6818519196027259768797653)
                  ·
                    refine ⟨159809043656888900831195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6818519196027259768797653 159809043656888900831195)
                    ·
                      rfl

theorem cell23_933681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_933681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933681 prefixEnd_933681 := by exact prefixLift 933681
  have htrace : WordTrace (prefixWord ++ tailWord_933681) baseStart_933681 baseEnd_933681 := by
    simpa [prefixWord, tailWord_933681, baseEnd_933681] using wordTrace_append hprefix tailTrace_933681
  have hstable : (prefixWord ++ tailWord_933681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933681).length < 2 ^ (prefixWord ++ tailWord_933681).sum := by decide
  have hdescent : baseEnd_933681 < baseStart_933681 := by decide
  rcases family_descends (prefixWord ++ tailWord_933681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933701 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_933701 : Nat := 118140960795 + 933701 * 2 ^ 59
def prefixEnd_933701 : Nat := 4983230072969 + 3 ^ 40 * 933701 * 2
def baseEnd_933701 : Nat := 479437400583756624243493

theorem tailTrace_933701 : CollatzResearch.WordTrace tailWord_933701 prefixEnd_933701 479437400583756624243493 := by
  unfold tailWord_933701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054873190368215280376957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22703248793578810186917971 34054873190368215280376957)
  ·
    refine ⟨12770577446388080730141359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34054873190368215280376957 12770577446388080730141359)
    ·
      refine ⟨19155866169582121095212039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770577446388080730141359 19155866169582121095212039)
      ·
        refine ⟨28733799254373181642818059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19155866169582121095212039 28733799254373181642818059)
        ·
          refine ⟨43100698881559772464227089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28733799254373181642818059 43100698881559772464227089)
          ·
            refine ⟨32325524161169829348170317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43100698881559772464227089 32325524161169829348170317)
            ·
              refine ⟨12122071560438686005563869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32325524161169829348170317 12122071560438686005563869)
              ·
                refine ⟨4545776835164507252086451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12122071560438686005563869 4545776835164507252086451)
                ·
                  refine ⟨6818665252746760878129677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545776835164507252086451 6818665252746760878129677)
                  ·
                    refine ⟨2556999469780035329298629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6818665252746760878129677 2556999469780035329298629)
                    ·
                      refine ⟨479437400583756624243493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2556999469780035329298629 479437400583756624243493)
                      ·
                        rfl

theorem cell23_933701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_933701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933701 prefixEnd_933701 := by exact prefixLift 933701
  have htrace : WordTrace (prefixWord ++ tailWord_933701) baseStart_933701 baseEnd_933701 := by
    simpa [prefixWord, tailWord_933701, baseEnd_933701] using wordTrace_append hprefix tailTrace_933701
  have hstable : (prefixWord ++ tailWord_933701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933701).length < 2 ^ (prefixWord ++ tailWord_933701).sum := by decide
  have hdescent : baseEnd_933701 < baseStart_933701 := by decide
  rcases family_descends (prefixWord ++ tailWord_933701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933822 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_933822 : Nat := 118140960795 + 933822 * 2 ^ 59
def prefixEnd_933822 : Nat := 4983230072969 + 3 ^ 40 * 933822 * 2
def baseEnd_933822 : Nat := 159833177247650216943479

theorem tailTrace_933822 : CollatzResearch.WordTrace tailWord_933822 prefixEnd_933822 159833177247650216943479 := by
  unfold tailWord_933822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257410802866231618191465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22706190948619901963687813 4257410802866231618191465)
  ·
    refine ⟨3193058102149673713643599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4257410802866231618191465 3193058102149673713643599)
    ·
      refine ⟨4789587153224510570465399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193058102149673713643599 4789587153224510570465399)
      ·
        refine ⟨7184380729836765855698099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789587153224510570465399 7184380729836765855698099)
        ·
          refine ⟨10776571094755148783547149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184380729836765855698099 10776571094755148783547149)
          ·
            refine ⟨4041214160533180793830181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10776571094755148783547149 4041214160533180793830181)
            ·
              refine ⟨757727655099971398843159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4041214160533180793830181 757727655099971398843159)
              ·
                refine ⟨1136591482649957098264739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757727655099971398843159 1136591482649957098264739)
                ·
                  refine ⟨1704887223974935647397109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136591482649957098264739 1704887223974935647397109)
                  ·
                    refine ⟨159833177247650216943479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1704887223974935647397109 159833177247650216943479)
                    ·
                      rfl

theorem cell23_933822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_933822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933822 prefixEnd_933822 := by exact prefixLift 933822
  have htrace : WordTrace (prefixWord ++ tailWord_933822) baseStart_933822 baseEnd_933822 := by
    simpa [prefixWord, tailWord_933822, baseEnd_933822] using wordTrace_append hprefix tailTrace_933822
  have hstable : (prefixWord ++ tailWord_933822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933822).length < 2 ^ (prefixWord ++ tailWord_933822).sum := by decide
  have hdescent : baseEnd_933822 < baseStart_933822 := by decide
  rcases family_descends (prefixWord ++ tailWord_933822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933838 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_933838 : Nat := 118140960795 + 933838 * 2 ^ 59
def prefixEnd_933838 : Nat := 4983230072969 + 3 ^ 40 * 933838 * 2
def baseEnd_933838 : Nat := 479507747433422588230363

theorem tailTrace_933838 : CollatzResearch.WordTrace tailWord_933838 prefixEnd_933838 479507747433422588230363 := by
  unfold tailWord_933838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257483748858985959764271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22706579993914591785409445 4257483748858985959764271)
  ·
    refine ⟨6386225623288478939646407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257483748858985959764271 6386225623288478939646407)
    ·
      refine ⟨9579338434932718409469611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386225623288478939646407 9579338434932718409469611)
      ·
        refine ⟨14369007652399077614204417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579338434932718409469611 14369007652399077614204417)
        ·
          refine ⟨10776755739299308210653313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14369007652399077614204417 10776755739299308210653313)
          ·
            refine ⟨8082566804474481157989985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10776755739299308210653313 8082566804474481157989985)
            ·
              refine ⟨6061925103355860868492489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082566804474481157989985 6061925103355860868492489)
              ·
                refine ⟨4546443827516895651369367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061925103355860868492489 4546443827516895651369367)
                ·
                  refine ⟨6819665741275343477054051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546443827516895651369367 6819665741275343477054051)
                  ·
                    refine ⟨10229498611913015215581077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819665741275343477054051 10229498611913015215581077)
                    ·
                      refine ⟨479507747433422588230363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10229498611913015215581077 479507747433422588230363)
                      ·
                        rfl

theorem cell23_933838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_933838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933838 prefixEnd_933838 := by exact prefixLift 933838
  have htrace : WordTrace (prefixWord ++ tailWord_933838) baseStart_933838 baseEnd_933838 := by
    simpa [prefixWord, tailWord_933838, baseEnd_933838] using wordTrace_append hprefix tailTrace_933838
  have hstable : (prefixWord ++ tailWord_933838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933838).length < 2 ^ (prefixWord ++ tailWord_933838).sum := by decide
  have hdescent : baseEnd_933838 < baseStart_933838 := by decide
  rcases family_descends (prefixWord ++ tailWord_933838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933845 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_933845 : Nat := 118140960795 + 933845 * 2 ^ 59
def prefixEnd_933845 : Nat := 4983230072969 + 3 ^ 40 * 933845 * 2
def baseEnd_933845 : Nat := 479511341798004060842831

theorem tailTrace_933845 : CollatzResearch.WordTrace tailWord_933845 prefixEnd_933845 479511341798004060842831 := by
  unfold tailWord_933845
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060125301846527873618989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22706750201231018582412659 34060125301846527873618989)
  ·
    refine ⟨12772546988192447952607121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34060125301846527873618989 12772546988192447952607121)
    ·
      refine ⟨9579410241144335964455341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12772546988192447952607121 9579410241144335964455341)
      ·
        refine ⟨3592278840429125986670753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9579410241144335964455341 3592278840429125986670753)
        ·
          refine ⟨2694209130321844490003065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592278840429125986670753 2694209130321844490003065)
          ·
            refine ⟨2020656847741383367502299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694209130321844490003065 2020656847741383367502299)
            ·
              refine ⟨3030985271612075051253449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020656847741383367502299 3030985271612075051253449)
              ·
                refine ⟨2273238953709056288440087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030985271612075051253449 2273238953709056288440087)
                ·
                  refine ⟨3409858430563584432660131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273238953709056288440087 3409858430563584432660131)
                  ·
                    refine ⟨5114787645845376648990197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3409858430563584432660131 5114787645845376648990197)
                    ·
                      refine ⟨479511341798004060842831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5114787645845376648990197 479511341798004060842831)
                      ·
                        rfl

theorem cell23_933845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_933845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933845 prefixEnd_933845 := by exact prefixLift 933845
  have htrace : WordTrace (prefixWord ++ tailWord_933845) baseStart_933845 baseEnd_933845 := by
    simpa [prefixWord, tailWord_933845, baseEnd_933845] using wordTrace_append hprefix tailTrace_933845
  have hstable : (prefixWord ++ tailWord_933845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933845).length < 2 ^ (prefixWord ++ tailWord_933845).sum := by decide
  have hdescent : baseEnd_933845 < baseStart_933845 := by decide
  rcases family_descends (prefixWord ++ tailWord_933845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933855 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_933855 : Nat := 118140960795 + 933855 * 2 ^ 59
def prefixEnd_933855 : Nat := 4983230072969 + 3 ^ 40 * 933855 * 2
def baseEnd_933855 : Nat := 479516476604549021717785

theorem tailTrace_933855 : CollatzResearch.WordTrace tailWord_933855 prefixEnd_933855 479516476604549021717785 := by
  unfold tailWord_933855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060490031810299581483019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22706993354540199720988679 34060490031810299581483019)
  ·
    refine ⟨51090735047715449372224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34060490031810299581483019 51090735047715449372224529)
    ·
      refine ⟨38318051285786587029168397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51090735047715449372224529 38318051285786587029168397)
      ·
        refine ⟨14369269232169970135938149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38318051285786587029168397 14369269232169970135938149)
        ·
          refine ⟨2694237981031869400488403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14369269232169970135938149 2694237981031869400488403)
          ·
            refine ⟨4041356971547804100732605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694237981031869400488403 4041356971547804100732605)
            ·
              refine ⟨1515508864330426537774727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4041356971547804100732605 1515508864330426537774727)
              ·
                refine ⟨2273263296495639806662091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515508864330426537774727 2273263296495639806662091)
                ·
                  refine ⟨3409894944743459709993137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273263296495639806662091 3409894944743459709993137)
                  ·
                    refine ⟨2557421208557594782494853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409894944743459709993137 2557421208557594782494853)
                    ·
                      refine ⟨479516476604549021717785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2557421208557594782494853 479516476604549021717785)
                      ·
                        rfl

theorem cell23_933855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_933855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933855 prefixEnd_933855 := by exact prefixLift 933855
  have htrace : WordTrace (prefixWord ++ tailWord_933855) baseStart_933855 baseEnd_933855 := by
    simpa [prefixWord, tailWord_933855, baseEnd_933855] using wordTrace_append hprefix tailTrace_933855
  have hstable : (prefixWord ++ tailWord_933855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933855).length < 2 ^ (prefixWord ++ tailWord_933855).sum := by decide
  have hdescent : baseEnd_933855 < baseStart_933855 := by decide
  rcases family_descends (prefixWord ++ tailWord_933855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933902 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_933902 : Nat := 118140960795 + 933902 * 2 ^ 59
def prefixEnd_933902 : Nat := 4983230072969 + 3 ^ 40 * 933902 * 2
def baseEnd_933902 : Nat := 479540610195310337830069

theorem tailTrace_933902 : CollatzResearch.WordTrace tailWord_933902 prefixEnd_933902 479540610195310337830069 := by
  unfold tailWord_933902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257775532830003326055495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22708136175093351072295973 4257775532830003326055495)
  ·
    refine ⟨6386663299245004989083243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257775532830003326055495 6386663299245004989083243)
    ·
      refine ⟨9579994948867507483624865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386663299245004989083243 9579994948867507483624865)
      ·
        refine ⟨7184996211650630612718649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9579994948867507483624865 7184996211650630612718649)
        ·
          refine ⟨5388747158737972959538987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7184996211650630612718649 5388747158737972959538987)
          ·
            refine ⟨8083120738106959439308481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388747158737972959538987 8083120738106959439308481)
            ·
              refine ⟨6062340553580219579481361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083120738106959439308481 6062340553580219579481361)
              ·
                refine ⟨4546755415185164684611021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062340553580219579481361 4546755415185164684611021)
                ·
                  refine ⟨1705033280694436756729133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4546755415185164684611021 1705033280694436756729133)
                  ·
                    refine ⟨639387480260413783773425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705033280694436756729133 639387480260413783773425)
                    ·
                      refine ⟨479540610195310337830069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639387480260413783773425 479540610195310337830069)
                      ·
                        rfl

theorem cell23_933902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_933902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933902 prefixEnd_933902 := by exact prefixLift 933902
  have htrace : WordTrace (prefixWord ++ tailWord_933902) baseStart_933902 baseEnd_933902 := by
    simpa [prefixWord, tailWord_933902, baseEnd_933902] using wordTrace_append hprefix tailTrace_933902
  have hstable : (prefixWord ++ tailWord_933902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933902).length < 2 ^ (prefixWord ++ tailWord_933902).sum := by decide
  have hdescent : baseEnd_933902 < baseStart_933902 := by decide
  rcases family_descends (prefixWord ++ tailWord_933902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933909 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_933909 : Nat := 118140960795 + 933909 * 2 ^ 59
def prefixEnd_933909 : Nat := 4983230072969 + 3 ^ 40 * 933909 * 2
def baseEnd_933909 : Nat := 479544204559891810442537

theorem tailTrace_933909 : CollatzResearch.WordTrace tailWord_933909 prefixEnd_933909 479544204559891810442537 := by
  unfold tailWord_933909
  simp only [CollatzResearch.WordTrace]
  refine ⟨34062459573614666803948781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22708306382409777869299187 34062459573614666803948781)
  ·
    refine ⟨12773422340105500051480793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34062459573614666803948781 12773422340105500051480793)
    ·
      refine ⟨9580066755079125038610595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12773422340105500051480793 9580066755079125038610595)
      ·
        refine ⟨14370100132618687557915893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580066755079125038610595 14370100132618687557915893)
        ·
          refine ⟨1347196887433001958554615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14370100132618687557915893 1347196887433001958554615)
          ·
            refine ⟨2020795331149502937831923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347196887433001958554615 2020795331149502937831923)
            ·
              refine ⟨3031192996724254406747885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020795331149502937831923 3031192996724254406747885)
              ·
                refine ⟨1136697373771595402530457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3031192996724254406747885 1136697373771595402530457)
                ·
                  refine ⟨852523030328696551897843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136697373771595402530457 852523030328696551897843)
                  ·
                    refine ⟨1278784545493044827846765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 852523030328696551897843 1278784545493044827846765)
                    ·
                      refine ⟨479544204559891810442537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1278784545493044827846765 479544204559891810442537)
                      ·
                        rfl

theorem cell23_933909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_933909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933909 prefixEnd_933909 := by exact prefixLift 933909
  have htrace : WordTrace (prefixWord ++ tailWord_933909) baseStart_933909 baseEnd_933909 := by
    simpa [prefixWord, tailWord_933909, baseEnd_933909] using wordTrace_append hprefix tailTrace_933909
  have hstable : (prefixWord ++ tailWord_933909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933909).length < 2 ^ (prefixWord ++ tailWord_933909).sum := by decide
  have hdescent : baseEnd_933909 < baseStart_933909 := by decide
  rcases family_descends (prefixWord ++ tailWord_933909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933932 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_933932 : Nat := 118140960795 + 933932 * 2 ^ 59
def prefixEnd_933932 : Nat := 4983230072969 + 3 ^ 40 * 933932 * 2
def baseEnd_933932 : Nat := 479556014614945220454931

theorem tailTrace_933932 : CollatzResearch.WordTrace tailWord_933932 prefixEnd_933932 479556014614945220454931 := by
  unfold tailWord_933932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031649226265670866018025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22708865635020894488024033 17031649226265670866018025)
  ·
    refine ⟨12773736919699253149513519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17031649226265670866018025 12773736919699253149513519)
    ·
      refine ⟨19160605379548879724270279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12773736919699253149513519 19160605379548879724270279)
      ·
        refine ⟨28740908069323319586405419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19160605379548879724270279 28740908069323319586405419)
        ·
          refine ⟨43111362103984979379608129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28740908069323319586405419 43111362103984979379608129)
          ·
            refine ⟨32333521577988734534706097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43111362103984979379608129 32333521577988734534706097)
            ·
              refine ⟨24250141183491550901029573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32333521577988734534706097 24250141183491550901029573)
              ·
                refine ⟨4546901471904665793943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24250141183491550901029573 4546901471904665793943045)
                ·
                  refine ⟨852544025982124836364321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4546901471904665793943045 852544025982124836364321)
                  ·
                    refine ⟨639408019486593627273241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 852544025982124836364321 639408019486593627273241)
                    ·
                      refine ⟨479556014614945220454931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639408019486593627273241 479556014614945220454931)
                      ·
                        rfl

theorem cell23_933932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_933932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_933932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_933932 prefixEnd_933932 := by exact prefixLift 933932
  have htrace : WordTrace (prefixWord ++ tailWord_933932) baseStart_933932 baseEnd_933932 := by
    simpa [prefixWord, tailWord_933932, baseEnd_933932] using wordTrace_append hprefix tailTrace_933932
  have hstable : (prefixWord ++ tailWord_933932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933932).length < 2 ^ (prefixWord ++ tailWord_933932).sum := by decide
  have hdescent : baseEnd_933932 < baseStart_933932 := by decide
  rcases family_descends (prefixWord ++ tailWord_933932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934025 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_934025 : Nat := 118140960795 + 934025 * 2 ^ 59
def prefixEnd_934025 : Nat := 4983230072969 + 3 ^ 40 * 934025 * 2
def baseEnd_934025 : Nat := 479603768315813356592003

theorem tailTrace_934025 : CollatzResearch.WordTrace tailWord_934025 prefixEnd_934025 479603768315813356592003 := by
  unfold tailWord_934025
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066690441194418615171529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22711126960796279076781019 34066690441194418615171529)
  ·
    refine ⟨25550017830895813961378647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34066690441194418615171529 25550017830895813961378647)
    ·
      refine ⟨38325026746343720942067971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550017830895813961378647 38325026746343720942067971)
      ·
        refine ⟨57487540119515581413101957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38325026746343720942067971 57487540119515581413101957)
        ·
          refine ⟨10778913772409171514956617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57487540119515581413101957 10778913772409171514956617)
          ·
            refine ⟨8084185329306878636217463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10778913772409171514956617 8084185329306878636217463)
            ·
              refine ⟨12126277993960317954326195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084185329306878636217463 12126277993960317954326195)
              ·
                refine ⟨18189416990940476931489293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12126277993960317954326195 18189416990940476931489293)
                ·
                  refine ⟨6821031371602678849308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18189416990940476931489293 6821031371602678849308485)
                  ·
                    refine ⟨1278943382175502284245341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821031371602678849308485 1278943382175502284245341)
                    ·
                      refine ⟨479603768315813356592003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1278943382175502284245341 479603768315813356592003)
                      ·
                        rfl

theorem cell23_934025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_934025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934025 prefixEnd_934025 := by exact prefixLift 934025
  have htrace : WordTrace (prefixWord ++ tailWord_934025) baseStart_934025 baseEnd_934025 := by
    simpa [prefixWord, tailWord_934025, baseEnd_934025] using wordTrace_append hprefix tailTrace_934025
  have hstable : (prefixWord ++ tailWord_934025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934025).length < 2 ^ (prefixWord ++ tailWord_934025).sum := by decide
  have hdescent : baseEnd_934025 < baseStart_934025 := by decide
  rcases family_descends (prefixWord ++ tailWord_934025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934045 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 8]
def baseStart_934045 : Nat := 118140960795 + 934045 * 2 ^ 59
def prefixEnd_934045 : Nat := 4983230072969 + 3 ^ 40 * 934045 * 2
def baseEnd_934045 : Nat := 53290448658767030926879

theorem tailTrace_934045 : CollatzResearch.WordTrace tailWord_934045 prefixEnd_934045 53290448658767030926879 := by
  unfold tailWord_934045
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067419901121962030899589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22711613267414641353933059 34067419901121962030899589)
  ·
    refine ⟨6387641231460367880793673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34067419901121962030899589 6387641231460367880793673)
    ·
      refine ⟨4790730923595275910595255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6387641231460367880793673 4790730923595275910595255)
      ·
        refine ⟨7186096385392913865892883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790730923595275910595255 7186096385392913865892883)
        ·
          refine ⟨10779144578089370798839325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186096385392913865892883 10779144578089370798839325)
          ·
            refine ⟨4042179216783514049564747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10779144578089370798839325 4042179216783514049564747)
            ·
              refine ⟨6063268825175271074347121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042179216783514049564747 6063268825175271074347121)
              ·
                refine ⟨4547451618881453305760341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063268825175271074347121 4547451618881453305760341)
                ·
                  refine ⟨53290448658767030926879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4547451618881453305760341 53290448658767030926879)
                  ·
                    rfl

theorem cell23_934045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_934045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934045 prefixEnd_934045 := by exact prefixLift 934045
  have htrace : WordTrace (prefixWord ++ tailWord_934045) baseStart_934045 baseEnd_934045 := by
    simpa [prefixWord, tailWord_934045, baseEnd_934045] using wordTrace_append hprefix tailTrace_934045
  have hstable : (prefixWord ++ tailWord_934045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934045).length < 2 ^ (prefixWord ++ tailWord_934045).sum := by decide
  have hdescent : baseEnd_934045 < baseStart_934045 := by decide
  rcases family_descends (prefixWord ++ tailWord_934045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934066 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_934066 : Nat := 118140960795 + 934066 * 2 ^ 59
def prefixEnd_934066 : Nat := 4983230072969 + 3 ^ 40 * 934066 * 2
def baseEnd_934066 : Nat := 159874940340882565393105

theorem tailTrace_934066 : CollatzResearch.WordTrace tailWord_934066 prefixEnd_934066 159874940340882565393105 := by
  unfold tailWord_934066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517046458511470654353513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22712123889363921744942701 8517046458511470654353513)
  ·
    refine ⟨6387784843883602990765135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8517046458511470654353513 6387784843883602990765135)
    ·
      refine ⟨9581677265825404486147703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387784843883602990765135 9581677265825404486147703)
      ·
        refine ⟨14372515898738106729221555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581677265825404486147703 14372515898738106729221555)
        ·
          refine ⟨21558773848107160093832333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372515898738106729221555 21558773848107160093832333)
          ·
            refine ⟨8084540193040185035187125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21558773848107160093832333 8084540193040185035187125)
            ·
              refine ⟨757925643097517347048793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8084540193040185035187125 757925643097517347048793)
              ·
                refine ⟨568444232323138010286595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757925643097517347048793 568444232323138010286595)
                ·
                  refine ⟨852666348484707015429893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568444232323138010286595 852666348484707015429893)
                  ·
                    refine ⟨159874940340882565393105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852666348484707015429893 159874940340882565393105)
                    ·
                      rfl

theorem cell23_934066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_934066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934066 prefixEnd_934066 := by exact prefixLift 934066
  have htrace : WordTrace (prefixWord ++ tailWord_934066) baseStart_934066 baseEnd_934066 := by
    simpa [prefixWord, tailWord_934066, baseEnd_934066] using wordTrace_append hprefix tailTrace_934066
  have hstable : (prefixWord ++ tailWord_934066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934066).length < 2 ^ (prefixWord ++ tailWord_934066).sum := by decide
  have hdescent : baseEnd_934066 < baseStart_934066 := by decide
  rcases family_descends (prefixWord ++ tailWord_934066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
